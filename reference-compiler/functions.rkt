#lang racket
(require graph)
(require "vectors.rkt")
(require "interp.rkt")
(require "interp-R4.rkt")
(require "utilities.rkt")
(require "runtime-config.rkt")
(require "type-check-R4.rkt")
(provide compile-R4 functions-passes)

(define compile-R4
  (class compile-R3
    (super-new)

    (inherit source-primitives primitives color-graph root-type? identify-home
             build-interference-block build-move-block
             patch-block print-x86-block select-instr-arg remove-jumps-CFG
             uncover-live-CFG assign-homes-block add-node num-used-callee
             type-equal? record-num-spills block->goto)
    (inherit-field control-flow-graph)
    (field [function-name (make-parameter #f)])

    (define/public (non-apply-ast)
      (set-union (source-primitives)
		 (set 'eq? 'vector 'vector-ref 'vector-set! 'if 'let 
                      'define 'program 'void 'fun-ref 'has-type
                      'collect 'allocate 'global-value)))

    (define/public (fun-def-name d)
      (match d
	[(Def f ps rt info body)
	 f]
	[else (error 'fun-def-name "ill-formed function definition in ~a" d)]))
      
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; shrink

    (define/override (shrink-exp e)
      (match e
        [(Apply f es)
         (define new-f (shrink-exp f))
         (define new-es (for/list ([e es]) (shrink-exp e)))
         (Apply new-f new-es)]
        [else (super shrink-exp e)]
        ))

    (define/public (shrink-def d)
      (match d
        [(Def f params rt info body)
         (Def f params rt info (shrink-exp body))]
        [else (error 'shrink-def "R4/unmatched ~a" d)]
        ))
    
    (define/override (shrink e)
      (match e
        [(ProgramDefsExp info ds body)
         (define ds^ (for/list ([d ds]) (shrink-def d)))
         (define body^ (shrink-exp body))
         (define main (Def 'main '() 'Integer '() body^))
         (ProgramDefs info (append ds^ (list main)))]
        [else (error "shrink couldn't match" e)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; partial-eval : R4 -> R4

    (define/override (pe-exp env)
      (lambda (e)
	(copious "R4/pe-exp" e)
	(define recur (pe-exp env))
	(match e
	  [(Apply f es)
	   (define new-es (map recur es))
	   (define new-f (recur f))
	   (Apply new-f new-es)]
	  [else ((super pe-exp env) e)]
	  )))
    
    (define/public (pe-def d)
      (copious "R4/pe-def" d)
      (match d
        [(Def f ps rt info body)
         (Def f ps rt info ((pe-exp '()) body))]
        ))
	  
    (define/override (partial-eval e)
      (copious "R4/partial-eval" e)
      (match e
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (pe-def d)))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> R4 -> R4

    (define/override (uniquify-exp env)
      (lambda (e)
	(copious "R4/uniquify-exp" e)
	(define recur (uniquify-exp env))
	(match e
	  [(HasType e t) (HasType (recur e) t)]
	  [(Apply f es)
	   (define new-es (map recur es))
	   (define new-f (recur f))
	   (Apply new-f new-es)]
	  [else ((super uniquify-exp env) e)]
	  )))
    
    (define/public (uniquify-def env)
      (lambda (d)
	(copious "R4/uniquify-def" d)
	(match d
	  [(Def f (list `[,xs : ,ps] ...) rt info body)
	   (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
	   (define new-env (append (map cons xs new-xs) env))
	   (Def (cdr (assq f env))
             (map (lambda (x t) `[,x : ,t]) new-xs ps)
             rt info ((uniquify-exp new-env) body))]
	  )))
	  
    (define/override (uniquify e)
      (copious "R4/uniquify" e)
      (match e
        [(ProgramDefs info ds)
         (define new-env
           (for/list ([d ds])
             (match d
               [(Def f (list `[,xs : ,ps] ...) rt info body)
                (define new-f
                  (cond [(eq? f 'main) 'main]
                        [else (gensym (racket-id->c-id f))]))
                (cons f new-f)]
               [else (error "R4/uniquify, ill-formed function def")])))
         (ProgramDefs info (for/list ([d ds]) ((uniquify-def new-env) d)))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; limit-functions

    (define/public (limit-type t)
      (match t
        [`(Vector ,ts ...)
         (define ts^ (for/list ([t ts])
                       (limit-type t)))
         `(Vector ,@ts^)]
        [`(,ts ... -> ,rt)
         (define ts^ (for/list ([t ts])
                       (limit-type t)))
         (define rt^ (limit-type rt))
         (define n (vector-length arg-registers))
         (cond [(> (length ts^) n)
                (define-values (first-ts last-ts) (split-at ts^ (- n 1)))
                `(,@first-ts (Vector ,@last-ts) -> ,rt^)]
               [else
                `(,@ts^ -> ,rt^)])]
        [else t]
        ))
    
    (define/public (limit-functions-exp param-env)
      (lambda (e)
	(copious "R4/limit-functions-exp" e)
	(let ([recur (limit-functions-exp param-env)])
	  (match e
	    [(Int n) e]
	    [(Var x)
	     (let ([res (assq x param-env)])
	       (cond [res (match res
			    [`(,arg ,typ1 ,typ2 ,vec ,ind)
			     (Prim 'vector-ref
                                   (list vec (Int ind)))]
                            [else
                             (error "R4/limit-functions-exp unhandled" res)]
                            )]
		     [else (Var x)]))]
            [(FunRef f)
             (FunRef f)]
	    [(Let x e body)
	     (Let x (recur e) (recur body))]
	    [(Void) (Void)]
	    [(Bool b) (Bool b)]
	    [(If cnd thn els)
	     (If (recur cnd) (recur thn) (recur els))]
	    [(HasType e t) (HasType (recur e) (limit-type t))]
            [(Prim op es) (Prim op (map recur es))]
	    [(Apply e es)
             (define n (vector-length arg-registers))
	     (cond [(<= (length es) n)
		    (Apply (recur e) (map recur es))]
		   [else
                    ;; pass the first n-1 arguments as normal, and the
                    ;; rest in a vector.
		    (define-values (first-es last-es) 
		      (cond [(> (length es) n) 
                             (split-at es (- n 1))]
			    [else (values es '())]))
		    (define vector-val (Prim 'vector (map recur last-es)))
		    (Apply (recur e) (append (map recur first-es)
                                             (list vector-val)))])]
            [else
             (error 'limit-functions-exp "unmatched ~a" e)]
            ))))

    (define/public (limit-functions-def d)
      (debug "R4/limit-functions-def" d)
      (match d
        [(Def f params rt info body)
         (define n (vector-length arg-registers))
         ;; update the parameter types
         (define new-params (for/list ([p params])
                              (match p [`[,x : ,T] `[,x : ,(limit-type T)]])))
         (cond [(<= (length new-params) n)
                (Def f new-params rt info ((limit-functions-exp '()) body))]
               [else
                (define vec-param (gensym 'vec-param))
                ;; separate the first n-1 parameters from the rest
                (define-values (first-params last-params) 
                  (cond [(> (length new-params) n)
                         (split-at new-params (- n 1))]
                        [else (values new-params '())]))
                ;; create the type for the new vector parameter
                (define vec-typ
                  `(Vector ,@(map (lambda (e)
                                    (match e [`(,arg : ,typ) typ]))
                                  last-params)))
                ;; create an environment for helping to translate parameters to
                ;; vector references.
                (define param-env
                  (map (lambda (e i)
                         (match e [`(,param : ,typ)
                                   `(,param ,typ ,vec-typ ,(Var vec-param) ,i)]))
                       last-params (range (length last-params))))
                (define new-body ((limit-functions-exp param-env) body))
                (Def f (append first-params `((,vec-param : ,vec-typ)))
                  rt info new-body)])]
        ))
    
    (define/public (limit-functions e)
      (debug "R4/limit-functions" e)
      (match e
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (limit-functions-def d)))]
        [else
         (debug "R4/limit-functions unhandled program" e)]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal functions and application

    (define/public (reveal-functions-exp funs)
      (lambda (e)
	(let* ([recur (reveal-functions-exp funs)])
          (match e
            [(Int n) (Int n)]
            [(Var x)
             (cond
               [(memq x funs) (FunRef x)]
               [else (Var x)])]
            [(Void) (Void)]
            [(Bool b) (Bool b)]
            [(HasType e t) (HasType (recur e) t)]
            [(Let x e body)
             (Let x (recur e) (recur body))]
            [(If cnd thn els)
             (If (recur cnd) (recur thn) (recur els))]
            [(Prim op es)
             (Prim op (map recur es))]
            [(Apply f es)
             (Apply (recur f) (map recur es))]
            [else
             (error "R4/reveal-functions-exp unmatched" e)]
            ))))

    (define/public (reveal-functions-def funs)
      (lambda (e)
        (match e
          [(Def f params rt info body)
           (Def f params rt info 
             ((reveal-functions-exp funs) body))]
          [else
           (error "R4/reveal-functions-def unmatched" e)]
          )))
      
    (define/public (reveal-functions e)
      (match e
        [(ProgramDefs info ds)
         (define funs (for/list ([d ds]) (fun-def-name d)))
         (ProgramDefs info (for/list ([d ds])
                             ((reveal-functions-def funs) d)))]
        [else
         (error "R4/reveal-functions unmatched" e)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; expose allocation

    (define/override (expose-alloc-exp e)
      (verbose "R4/expose-alloc-exp" e)
      (match e
        [(Apply e es)
         (Apply (expose-alloc-exp e)
                (for/list ([e es]) (expose-alloc-exp e)))]
        [(FunRef f) (FunRef f)]
        [else
         (super expose-alloc-exp e)]
        ))

    (define/public (expose-allocation-def def)
      (match def
	[(Def f params t info e)
	 (Def f params t info (expose-alloc-exp e))]
	[else (error 'expose-allocation-def "unmatched ~a" def)]))

    (define/override (expose-allocation e)
      (verbose "R4/expose-allocation" e)
      (match e
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (expose-allocation-def d)))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; remove-complex-opera*

    (define/override (rco-atom e)
      (verbose "R4/rco-atom" e)
      (match e
        [(FunRef f)
         (define tmp (gensym 'tmp))
         (values (Var tmp) `((,tmp . ,(FunRef f))))]
        [(Apply f es)
         (define-values (new-f f-ss) (rco-atom f))
         (define-values (new-es sss) (for/lists (ls1 ls2) ([e es])
                                       (rco-atom e)))
         (define fun-apply (Apply new-f new-es))
         (define tmp (gensym 'tmp))
         (values (Var tmp) (append (append f-ss (append* sss))
                                   `((,tmp . ,fun-apply))))]
        [else
         (super rco-atom e)]
        ))

    (define/override (rco-exp e)
      (verbose "R4/rco-exp" e)
      (match e
        [(FunRef label)
         (FunRef label)]
        [(Apply f es)
         (define-values (new-f f-ss) (rco-atom f))
         (define-values (new-es sss) (for/lists (ls1 ls2) ([e es])
                                       (rco-atom e)))
         (make-lets (append f-ss (append* sss))
                    (Apply new-f new-es))]
        [else
         (super rco-exp e)]
        ))

    #;(define/override (rco-pred e)
      (verbose "R4/rco-pred" e)
      (match e
        [(Apply f es)
         (define-values (new-f ss) (rco-atom f))
         (define-values (new-es sss)
           (for/lists (l1 l2) ([e es]) (rco-atom e)))
         (make-lets (append ss (append* sss))
                    (Apply new-f new-es))]
        [else
         (super rco-pred e)]
        ))

    
    (define/public (rco-def d)
      (verbose "R4/rco-def" d)
      (match d
        [(Def f params  ty info e)
         (Def f params ty info (rco-exp e))]
        ))

    (define/override (remove-complex-opera* e)
      (verbose "R4/remove-complex-opera*" e)
      (match e
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (rco-def d)))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; explicate-control

    (define/override (basic-exp? e)
      (match e
        [(FunRef label) #t]
        [else (super basic-exp? e)]
        ))

    (define/override (explicate-assign e x cont-block)
      (match e
        [(Apply f arg*)
         (delay (Seq (Assign (Var x) (Call f arg*)) (force cont-block)))]
        [else (super explicate-assign e x cont-block)]
        ))
    
    (define/override (explicate-tail e)
      (match e
        [(Apply f arg*) (delay (TailCall f arg*))]
        [else (super explicate-tail e)]
        ))
    
    (define/override (explicate-pred cnd thn-block els-block)
      (match cnd
        [(Apply f arg*)
         (define tmp (gensym 'tmp))
         (delay (Seq (Assign (Var tmp) (Call f arg*))
                     (IfStmt (Prim 'eq? (list (Var tmp) (Bool #t)))
                             (force (block->goto thn-block))
                             (force (block->goto els-block)))))]
        [else (super explicate-pred cnd thn-block els-block)]
        ))
    
    (define/public (explicate-control-def d)
      (match d
        [(Def f params ty info body)
         (set! control-flow-graph '())
         (define body-block (force (explicate-tail body)))
         (define new-CFG (dict-set control-flow-graph (symbol-append f 'start)
                                   body-block))
         (Def f params ty info new-CFG)]
        ))

    (define/override (explicate-control p)
      (match p
        [(ProgramDefs info ds)
         (define new-ds (for/list ([d ds]) (explicate-control-def d)))
         (ProgramDefs info new-ds)]
         ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions

    (define/override (select-instr-tail t)
      (match t
	[(TailCall f es)
         (unless (<= (length es) (vector-length arg-registers))
           (error "R4/select-instr-stmt: more arguments than arg-registers"))
	 (define new-f (select-instr-arg f))
	 (define new-es (for/list ([e es]) (select-instr-arg e)))
	 (append (for/list ([arg new-es] [r arg-registers])
                   (Instr 'movq (list arg (Reg r))))
                 (list (TailJmp new-f (length es))))]
        [(Return e)
         (define ret-label (symbol-append (function-name) 'conclusion))
         (append (select-instr-stmt (Assign (Reg 'rax) e))
                 (list (Jmp ret-label)))]
        [else
         (super select-instr-tail t)]
        ))
    
    (define/override (select-instr-stmt e)
      (verbose "R4/select-instr-stmt" e)
      (match e
	[(Assign lhs (FunRef f))
	 (define new-lhs (select-instr-arg lhs))
	 (list (Instr 'leaq (list (FunRef f) new-lhs)))]
	[(Assign lhs (Call f es))
         (unless (<= (length es) (vector-length arg-registers))
           (error "R4/select-instr-stmt: more arguments than arg-registers"))
	 (define new-lhs (select-instr-arg lhs))
	 (define new-f (select-instr-arg f))
	 (define new-es (for/list ([e es]) (select-instr-arg e)))
	 (append (for/list ([arg new-es] [r arg-registers])
                   (Instr 'movq (list arg (Reg r))))
		 (list (IndirectCallq new-f (length es))
                       (Instr 'movq (list (Reg 'rax) new-lhs))))]
        [else
         (super select-instr-stmt e)]
        ))

    (define/public (select-instr-def d)
      (verbose "R4/select-instr-def" d)
      (match d
	[(Def f (list `[,xs : ,ps] ...) rt info CFG)
         (unless (<= (length xs) (vector-length arg-registers))
           (error "R4/select-instr-def: more parameters than arg-registers"))
         (define new-CFG
           (parameterize ([function-name f])
             (for/list ([(label tail) (in-dict CFG)])
               (cons label (Block '() (select-instr-tail tail))))))
	 (define param-moves
	   (for/list ([param xs] [r arg-registers])
             (Instr 'movq (list (Reg r) (Var param)))))
         (define start-label (symbol-append f 'start))
         (define new-start
           (match (dict-ref new-CFG start-label)
             [(Block info ss)
              (Block info (append param-moves ss))]
             [else
              (error "R4/select-instr-def: expected block")]))
         (define newer-CFG (dict-set new-CFG start-label new-start))
         (define new-info
           (dict-set-all
            info   ;; parameters become locals
            `((locals-types . ,(append (map cons xs ps)
                                       (dict-ref info 'locals-types)))
              (num-params . ,(length xs)))))
	 (Def f '() 'Integer new-info newer-CFG)]
        [else
         (error 'select-instr-def "unhandled case" d)]
        ))

    (define/override (select-instructions e)
      (copious "R4/select-instructions" e)
      (match e
	[(ProgramDefs info ds)
	 (define new-ds (for/list ([d ds]) (select-instr-def d)))
	 (ProgramDefs info new-ds)]
	[else (super select-instructions e)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; remove-jumps
    
    (define/public (remove-jumps-def ast)
      (match ast
        [(Def f '() rt info CFG)
         (Def f '() rt info (remove-jumps-CFG f CFG))]
        ))

    (define/override (remove-jumps ast)
      (match ast
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (remove-jumps-def d)))]
        [else (error "R4/remove-jumps unhandled" ast)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> pseudo-x86 -> pseudo-x86*

    (define/override (free-vars a)
      (match a
        [(FunRef f) (set)]
        [else (super free-vars a)]
        ))

    (define/override (read-vars instr)
      (match instr
	 [(Instr 'leaq (list s d)) (free-vars s)]
	 [(IndirectCallq arg n) 
	  (set-union (free-vars arg)
                     (vector->set (vector-take arg-registers n)))]
	 [(TailJmp arg n)
          (set-union (free-vars arg)
                     (vector->set (vector-take arg-registers n)))]
	 [else (super read-vars instr)]))

    (define/override (write-vars instr)
      (match instr
        [(IndirectCallq f n) (caller-save-for-alloc)]
        [(TailJmp f n) (caller-save-for-alloc)]
        [(Instr 'leaq (list s d)) (free-vars d)]
        [else (super write-vars instr)]))
    
    (define/public (uncover-live-def ast)
      (match ast
        [(Def f '() rt info CFG)
         (define conclusion (symbol-append f 'conclusion))
         (Def f '() rt info (uncover-live-CFG CFG f))]
        ))

    (define/override (uncover-live ast)
      (match ast
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (uncover-live-def d)))]
        [else (error "R4/uncover-live unhandled" ast)]))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph

    (define/override (build-interference-instr live-after G loc-types)
      (lambda (ast)
	(match ast
          [(Callq f _)
           ;; The function might call collect. -Jeremy
           (for ([v live-after])
             (cond [(and (not (set-member? registers v))
                         (root-type? (dict-ref loc-types v)))
                    (for ([u (callee-save-for-alloc)])
                      (add-edge! G u v))]))
           ((super build-interference-instr live-after G loc-types) ast)]
          [(IndirectCallq arg _)
           ;; The function might call collect. -Jeremy
           (for ([v live-after])
             (cond [(and (not (set-member? registers v))
                         (root-type? (dict-ref loc-types v)))
                    (for ([u (callee-save-for-alloc)])
                      (add-edge! G u v))]))
           ((super build-interference-instr live-after G loc-types) ast)]
          [else
           ((super build-interference-instr live-after G loc-types) ast)]
          )))

    (define/public (build-interference-def d)
      (match d
        [(Def f '() rt info CFG)
         (define loc-types (lookup 'locals-types info))
         (define IG (undirected-graph '()))
         (for ([v (dict-keys loc-types)])
           (add-vertex! IG v))
         (define new-CFG
           (for/list ([(label block) (in-dict CFG)])
             (cons label ((build-interference-block IG loc-types) block))))
         (print-dot IG (format "./~s-interfere.dot" f))
         (define new-info (dict-set info 'conflicts IG))
         (Def f '() rt new-info new-CFG)]
        [else 
         (error "R4/build-interference-def unhandled" d)]
        ))

    (define/override (build-interference ast)
      (copious "R4/build-interference" ast)
      (match ast
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (build-interference-def d)))]
        [else 
         (error "R4/build-interferenced unhandled" ast)]
        ))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-move-graph : pseudo-x86* -> pseudo-x86*
    ;; *annotate program with move graph
    
    (define/public (build-move-graph-def d)
      (match d
        [(Def f '() rt info CFG)
         (define MG (undirected-graph '()))
         (for ([v (dict-keys (dict-ref info 'locals-types))])
           (add-vertex! MG v))
         (define new-CFG
           (for/list ([(label block) (in-dict CFG)])
             (cons label (build-move-block block MG))))
         (print-dot MG (format "./~s-move.dot" f))
         (define new-info (dict-set info 'move-graph MG))
         (Def f '() rt new-info new-CFG)]
        ))

    (define/override (build-move-graph ast)
      (match ast
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (build-move-graph-def d)))]
        [else (error "R4/build-move-graph unhandled" ast)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-homes : homes -> pseudo-x86 -> pseudo-x86

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'leaq)))

    (define/override (assign-homes-imm homes)
      (lambda (e)
        (match e
          [(FunRef f) (FunRef f) ]
          [else
           ((super assign-homes-imm homes) e)]
          )))
    
    (define/override (assign-homes-instr homes)
      (lambda (e)
        (match e
          [(IndirectCallq f n)
           (IndirectCallq ((assign-homes-imm homes) f) n)]
          [(TailJmp f n)
           (TailJmp ((assign-homes-imm homes) f) n)]
          [else
           ((super assign-homes-instr homes) e)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86

    (define/public (allocate-registers-def d)
      (match d
        [(Def f '() rt info CFG)
         (define locals (dict-keys (dict-ref info 'locals-types)))
         (define IG (dict-ref info 'conflicts))
         (define MG (dict-ref info 'move-graph))
         (define-values (color num-spills) (color-graph IG MG info))
         (define homes
           (for/hash ([x locals])
             (define home (identify-home (num-used-callee locals color)
                                         (hash-ref color x)))
             ;(debug "home of ~a is ~a" x home)
             (values x home)))
         (debug "homes ~a\n" homes)
         (define new-CFG
           (for/list ([(label block) (in-dict CFG)])
             (cons label ((assign-homes-block homes) block))))
         (define (callee? home)
           (match home
             [(Reg r) (set-member? (callee-save-for-alloc) r)]
             [else #f]))
         (define used-callee-reg
           (for/set ([(var home) (in-hash homes)] #:when (callee? home))
             (match home [(Reg r) r])))
         (debug "allocate reg, used callee ~a\n" used-callee-reg)
         (define info2 (record-num-spills info num-spills))
         (define info3 (dict-set info2 'used-callee-reg used-callee-reg))
         (define new-info
           (dict-remove-all info3 (list 'conflicts 'move-graph)))
         (Def f '() rt new-info new-CFG)]
        ))

    (define/override (allocate-registers ast)
      (match ast
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (allocate-registers-def d)))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; patch-instructions : psuedo-x86 -> x86

    (define/override (in-memory? a)
      (match a
        [(FunRef f) #t]
        [else (super in-memory? a)]))

    (define/override (patch-instr e)
      (match e
        [(IndirectCallq f n)
         (list (IndirectCallq f n))]
        [(TailJmp (Reg 'rax) n) ;; where do trivial moves get removed? -Jeremy
         (TailJmp (Reg 'rax) n)]
        [(TailJmp target n)
         ;; Target must be put in rax because all other registers may
         ;; get trampled by the epilogue that gets inserted by
         ;; tail-jmp. -Jeremy
         (list (Instr 'movq (list target (Reg 'rax)))
               (TailJmp (Reg 'rax) n))]
        [(Instr 'leaq (list s d))
         (cond [(in-memory? d)
                (list (Instr 'leaq (list s (Reg 'rax)))
                      (Instr 'movq (list (Reg 'rax) d)))]
               [else
                (list (Instr 'leaq (list s d)))])]
        [else
         (super patch-instr e)]
        ))

    (define/public (patch-instr-def d)
      (match d
        [(Def f '() rt info CFG)
         (define new-CFG
           (for/list ([(label block) (in-dict CFG)])
             (cons label (patch-block block))))
         (Def f '() rt info new-CFG)]
        [else
         (error "R4/patch-instr-def unhandled" d)]
        ))

    (define/override (patch-instructions e)
      (match e
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (patch-instr-def d)))]
        [else (error "R4/patch-instructions unhandled " e)]
        ))

    (inherit variable-size)
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string

    ;; hack: should break into multiple functions and thread through
    ;; epilogue -mv
    (define epilogue (box (void)))

    (define/override (print-x86-imm e)    
      (match e
        [(FunRef f)
         (format "~a(%rip)" (label-name f))]
        [else
         (super print-x86-imm e)]
        ))

    (define/override (print-x86-instr e)
      (verbose "R4/print-x86-instr" e)
      (match e
        [(IndirectCallq f n)
         (format "\tcallq\t*~a\n" (print-x86-imm f))]
        [(TailJmp f n)
         (string-append
          (unbox epilogue)
          (format "\tjmp\t*~a\n" (print-x86-imm f)))]
        [else
         (super print-x86-instr e)]
        ))

    (define/public (print-x86-def d)
      (match d
        [(Def f '() rt info CFG)
         (define spills (dict-ref info 'num-spills))
         (define root-spills (dict-ref info 'num-root-spills))
         (define stack-space (* (variable-size) spills))
         (define root-space (* (variable-size) root-spills))
         (define used-callee-reg (dict-ref info 'used-callee-reg))
         (define callee-reg (set->list used-callee-reg))
         (debug "function ~a used callee: ~a\n" f callee-reg)
         (define save-callee-reg
           (for/list ([r callee-reg])
             (format "\tpushq\t%~a\n" r)))
         (define restore-callee-reg
           (for/list ([r (reverse callee-reg)])
             (format "\tpopq\t%~a\n" r)))
         (define callee-space (* (length callee-reg) (variable-size)))
         (define stack-adj (- (align (+ callee-space stack-space) 16)
                              callee-space))
         (define initialize-heaps
           (string-append
            (format "\tmovq\t$~a, %rdi\n" (rootstack-size))
            (format "\tmovq\t$~a, %rsi\n" (heap-size))
            (format "\tcallq\t~a\n" (label-name "initialize"))
            (format "\tmovq\t~a, %~a\n" 
                    (print-x86-imm (Global 'rootstack_begin))
                    rootstack-reg)))
         (define initialize-roots
           (for/list ([i (range (/ root-space (variable-size)))])
             (string-append 
              (format "\tmovq\t$0, (%~a)\n" rootstack-reg)
              (format "\taddq\t$~a, %~a\n" 
                      (variable-size) rootstack-reg))))
         (set-box! epilogue
                   (string-append
                    (if (equal? stack-adj 0) ""
                        (format "\taddq\t$~a, %rsp\n" stack-adj)	     )
                    (string-append* restore-callee-reg)
                    (if (eq? root-space 0) ""
                        (format "\tsubq\t$~a, %~a\n" root-space rootstack-reg))
                    (format "\tpopq\t%rbp\n")))
         (string-append
          (string-append*
           (for/list ([(label block) (in-dict CFG)])
             (string-append (format "~a:\n" (label-name label))
                            (print-x86-block block))))
          "\n"
          (format "\t.globl ~a\n" (label-name f))
          (format "\t.align 16\n")
          (format "~a:\n" (label-name f))
          (format "\tpushq\t%rbp\n")
          (format "\tmovq\t%rsp, %rbp\n")
          (string-append* save-callee-reg)
          (if (eq? stack-adj 0) "" (format "\tsubq\t$~a, %rsp\n" stack-adj))
          (if (eq? f 'main) initialize-heaps "")
          (string-append* initialize-roots)
          (format "\tjmp\t~a\n" (label-name (symbol-append f 'start)))
          "\n"
          (format "~a:\n" (label-name (symbol-append f 'conclusion)))
          (unbox epilogue)
          (format "\tretq\n")
          )]
        ))

    (define/override (print-x86 e)
      (match e
	[(ProgramDefs info ds)
         (string-append* (for/list ([d ds]) (print-x86-def d)))]
	))

    ));; compile-R4
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes

(define functions-passes
  (let ([compiler (new compile-R4)])
    `(("shrink"
       ,(lambda (p) (send compiler shrink p))
       ,interp-R4
       ,type-check-R4)
      ("uniquify" 
       ,(lambda (p) (send compiler uniquify p))
       ,interp-R4
       ,type-check-R4)
      ("partial-eval"
       ,(lambda (p) (send compiler partial-eval p))
       ,interp-R4
       ,type-check-R4)
      ("reveal-functions"
       ,(lambda (p) (send compiler reveal-functions p))
       ,interp-F1
       ,type-check-R4)
      ("limit-functions"
       ,(lambda (p) (send compiler limit-functions p))
       ,interp-F1
       ,type-check-R4)
      ("expose allocation"
       ,(lambda (p) (send compiler expose-allocation p))
       ,interp-F1
       ,type-check-R4)
      ("remove-complex-opera*"
       ,(lambda (p) (send compiler remove-complex-opera* p))
       ,interp-F1
       ,type-check-R4)
      ("explicate-control"
       ,(lambda (p) (send compiler explicate-control p))
       ,interp-C3
       ,type-check-C3)
      ("instruction selection"
       ,(lambda (p) (send compiler select-instructions p))
       ,interp-pseudo-x86-3)
      ("uncover-live"
       ,(lambda (p) (send compiler uncover-live p))
       ,interp-pseudo-x86-3)
      ("build-interference"
       ,(lambda (p) (send compiler build-interference p))
       ,interp-pseudo-x86-3)
      ("build-move-graph"
       ,(lambda (p) (send compiler build-move-graph p))
       ,interp-pseudo-x86-3)
      ("allocate-registers"
       ,(lambda (p) (send compiler allocate-registers p))
       ,interp-x86-3)
      ("remove-jumps"
       ,(lambda (p) (send compiler remove-jumps p))
       ,interp-x86-3)
      ("patch instructions"
       ,(lambda (p) (send compiler patch-instructions p))
       ,interp-x86-3)
      ("print x86"
       ,(lambda (p) (send compiler print-x86 p))
       #f)
      )))
