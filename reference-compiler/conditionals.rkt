#lang racket
(require data/queue)
(require graph)
(require "multigraph.rkt")
(require "register_allocator.rkt")
(require "interp.rkt")
(require "interp-R2.rkt")
(require "interp-C1.rkt")
(require "utilities.rkt")
(require "type-check-R2.rkt")
(require "priority_queue.rkt")
(provide compile-R2 cond-passes)

(define challenge #t)

(define compile-R2
  (class compile-reg-R1
    (super-new)

    (inherit first-offset variable-size in-memory?
             uncover-live-block
	     color-graph identify-home build-move-graph-instr
             print-x86-block partial-eval)

    ;; These functions are used in the type checker and corresponds to
    ;; when to use type-check-op. -Jeremy 
    (define/public (source-primitives)
      (set-union (super primitives)
                 (set '< '<= '> '>=)
                 (set 'and 'or 'not)))

    (define/public (comparison-ops) (set 'eq? '<))

    (define/override (primitives)
      (set-union (super primitives) 
                 (comparison-ops)
		 (set 'not)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> R2 -> R2 (new pass)

    (define/public (binary-op-types)
      '((+ . ((Integer Integer) . Integer))
        (- . ((Integer Integer) . Integer))
	(and . ((Boolean Boolean) . Boolean))
	(or . ((Boolean Boolean) . Boolean))
	(< . ((Integer Integer) . Boolean))
	(<= . ((Integer Integer) . Boolean))
	(> . ((Integer Integer) . Boolean))
	(>= . ((Integer Integer) . Boolean))
	))

    (define/public (unary-op-types)
      '((- . ((Integer) . Integer))
	(not . ((Boolean) . Boolean))
        ))

    (define/public (nullary-op-types)
      '((read . (() . Integer))))

    (define/public (type-equal? t1 t2)
      (equal? t1 t2))
    
    (define/public (type-check-op op arg-types)
      (define table
	(cond
	 [(eq? 2 (length arg-types)) (binary-op-types)]
	 [(eq? 1 (length arg-types)) (unary-op-types)]
	 [else (nullary-op-types)]))
      (copious "type-check-op" op table)
      (match (dict-ref table op)
        [`(,param-types . ,return-type)
         (for ([at arg-types] [pt param-types]) 
           (unless (type-equal? at pt)
             (error 'type-check-op "type error: argument type ~a not equal to parameter type ~a"
                    at pt)))
         return-type]
        [else
         (error 'type-check-op "type checking: error operator lookup for " op table)]))

    (define/public (type-check-exp env)
      (lambda (e)
        (copious "conditionals/type-check-exp" e env)
        (match e
          [(Var x)
           (let ([t (dict-ref env x)])
             (values (Var x) t))]
          [(Int n) (values (Int n) 'Integer)]
          [(Bool b) (values (Bool b) 'Boolean)]
          [(Let x e body)
           (define-values (e^ Te) ((type-check-exp env) e))
           (define-values (b Tb) ((type-check-exp (dict-set env x Te)) body))
           (values (Let x e^ b) Tb)]
          [(If cnd thn els)
           (define-values (c Tc) ((type-check-exp env) cnd))
	   (define-values (t Tt) ((type-check-exp env) thn))
	   (define-values (e Te) ((type-check-exp env) els))
	   (unless (type-equal? Tc 'Boolean)
             (error 'type-check-exp "type error: condition of if should be Boolean, not" Tc))
	   (unless (type-equal? Tt Te)
             (error 'type-check-exp "type error: branches of if have different types"
		    (list Tt Te)))
	   (values (If c t e) Te)]
          [(Prim 'eq? (list e1 e2))
           (define-values (e1^ T1) ((type-check-exp env) e1))
	   (define-values (e2^ T2) ((type-check-exp env) e2))
	   (unless (type-equal? T1 T2)
             (error 'type-check-exp "type error: arguments of eq? with different types"
                    (list T1 T2)))
	   (values (Prim 'eq? (list e1^ e2^)) 'Boolean)]
	  [(Prim op es)
            (define-values (new-es ts)
              (for/lists (exprs types) ([e es]) ((type-check-exp env) e)))
	    (define t-ret (type-check-op op ts))
            (values (Prim op new-es) t-ret)]
          [else
           (error 'type-check-exp "couldn't match" e)])))
    
    (define/public (type-check env)
      (lambda (e)
        (copious "conditionals/type-check" e env)
        (match e
          [(Program info body)
           (define-values (body^ Tb) ((type-check-exp '()) body))
           (copious "conditionals/type-check" body^)
           (unless (type-equal? Tb 'Integer)
             (error "result of the program must be an integer, not " Tb))
	   (Program info body^)]
          [else
	    (error 'type-check "couldn't match" e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; shrink : R2 -> R2

    (define/public (shrink-exp e)
      (match e
        [(Prim 'and (list e1 e2))
         ;; The following is compatible with the dynamically typed semantics.
         ;; But it hurts explicate-pred. -Jeremy
         #;(let ([tmp (gensym 'tmp)])
           (Let tmp (shrink-exp e1)
                (If (Var tmp) (shrink-exp e2) (Var tmp))))
         
         ;; The following is what Dybvig does.
         ;; The compiler for dynamic can override this. -Jeremy
         (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
        [(Prim 'or (list e1 e2))
         ;; This works well with explicate-pred. -Jeremy
         (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
        [(Prim '<= (list e1 e2))
	 (let ([tmp (gensym 'tmp)])
           (Let tmp (shrink-exp e1)
                (Prim 'not (list (Prim '< (list (shrink-exp e2) (Var tmp)))))))]
        [(Prim '> (list e1 e2))
	 (let ([tmp (gensym 'tmp)])
           (Let tmp (shrink-exp e1)
                (Prim '< (list (shrink-exp e2) (Var tmp)))))]
        [(Prim '>= (list e1 e2))
         (Prim 'not (list (Prim '< (list (shrink-exp e1) (shrink-exp e2)))))]
        [(Prim '- (list e1 e2))
         (Prim '+ (list (shrink-exp e1) (Prim '- (list (shrink-exp e2)))))]

        [(Bool b) (Bool b)]
        [(If cnd thn els)
         (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
        [(Var x) (Var x)]
        [(Int n) (Int n)]
        [(Let x e body)
         (Let x (shrink-exp e) (shrink-exp body))]
        [(Prim op es) 
         #:when (set-member? (primitives) op)
         (Prim op (for/list ([e es]) (shrink-exp e)))]
        [else
         (error 'shrink-exp "R2/unmatched ~a" e)]
        ))
      
    (define/public (shrink e)
      (match e
        [(Program info body)
         (Program info (shrink-exp body))]
        [else (error "shrink couldn't match" e)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; partial-eval : R2 -> R2

    (define/override (pe-exp env)
      (lambda (e)
        (debug "R2/pe-exp: " e)
        (match e
          [(Bool b) (Bool b)]
          [(If cnd thn els)
           (define cnd^ ((pe-exp env) cnd))
           (match cnd^
             [(Bool #t)
              ((pe-exp env) thn)]
             [(Bool #f)
              ((pe-exp env) els)]
             [else
              (If cnd^ ((pe-exp env) thn) ((pe-exp env) els))])]
          [(Prim op es)
           #:when (member op '(< eq? not))
           ;; TODO
           (define es^ (for/list ([e es]) ((pe-exp env) e)))
           (Prim op es^)]
          [else  ((super pe-exp env) e)]
          )))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> R2 -> R2
    
    (define/override (uniquify-exp env)
      (lambda (e)
        (define recur (uniquify-exp env))
	(match e
          [(Bool b) (Bool b)]
          [(If cnd thn els)
           (If (recur cnd) (recur thn) (recur els))]
          [else ((super uniquify-exp env) e)]
          )))
    
    (define/override (uniquify e)
      (match e
        [(Program info e)
         (Program info ((uniquify-exp '()) e))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/override (rco-atom e)
      (verbose "R2/rco-atom" e)
      (match e
        [(Bool b) (values (Bool b) '())]
        [(If cnd thn els)
         (define if-exp (If (rco-exp cnd) (rco-exp thn) (rco-exp els)))
         (define tmp (gensym 'tmp))
         (values (Var tmp) `((,tmp . ,if-exp)))]
        [else
         (super rco-atom e)]
        ))
    
    (define/override (rco-exp e)
      (verbose "R2/rco-exp" e)
      (match e
        [(Bool b) (Bool b)]
        [(If cnd thn els)
         (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
        [else
         (super rco-exp e)]
        ))

    #;(define/public (rco-pred e)
      (verbose "R2/rco-pred" e)
      (match e
        [(Var x) (Var x)]
        ;[(Int n) (Int n)] not needed
        [(Let x rhs body)
         (Let x (rco-exp rhs) (rco-pred body))]
        [(Prim 'not (list e))
         (Prim 'not (list (rco-pred e)))]
        [(Prim op es)
         (define-values (new-es sss)
           (for/lists (l1 l2) ([e es]) (rco-atom e)))
         (make-lets (append* sss) (Prim op new-es))]
        [(Bool b) (Bool b)]
        [(If cnd thn els)
         (If (rco-pred cnd) (rco-pred thn) (rco-pred els))]
        [else
         (error 'rco-pred "unmatched ~a" e)]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; explicate-control
    
    (define (arg? e)
      (match e
        [(or (Var _) (Int _) (Bool _)) #t]
        [else #f]))

    (field [control-flow-graph '()])

    (define/public (add-node block)
      (let ([label (gensym 'block)])
        (debug "adding block " label block)
        (set! control-flow-graph (cons (cons label block) control-flow-graph))
        ;; dictify this -Jeremy
        label))

    (define/public (block->goto block)
      (delay
        (define b (force block))
        (match b
          [(Goto label) (Goto label)]
          [else (Goto (add-node b))]
          )))

    (define/override (basic-exp? e)
      (match e
        [(Bool b) #t]
        [else (super basic-exp? e)]
        ))

    ;; explicate-tail : exp -> tail
    (define/override (explicate-tail e)
      (copious "explicate-tail" e)
      (match e
        [(If cnd thn els)
         (explicate-pred cnd (explicate-tail thn) (explicate-tail els))]
        [else (super explicate-tail e)]
        ))

    ;; explicate-assign : exp -> var -> tail -> tail
    ;; side effect: adds nodes to the CFG
    (define/override (explicate-assign e x cont-block)
      (copious "explicate-assign" e x)
      (match e
        [(If cnd thn els)
         (delay
           (define cont (block->goto cont-block))
           (force (explicate-pred cnd (explicate-assign thn x cont)
                                  (explicate-assign els x cont))))]
        [else (super explicate-assign e x cont-block)]
        ))

    ;; precondition: cnd is atomic
    (define/public (generic-explicate-pred cnd thn-block els-block)
      (IfStmt (Prim 'eq? (list cnd (Bool #t)))
              (force (block->goto thn-block))
              (force (block->goto els-block))))
    
    ;; explicate-pred : exp * tail * tail -> tail
    ;; side effect: adds nodes to the CFG
    (define/public (explicate-pred cnd thn-block els-block)
      (copious "explicate-pred" cnd)
      (match cnd
        [(Var x)
         (delay (generic-explicate-pred cnd thn-block els-block))]
        [(Bool #t)
         thn-block]
        [(Bool #f)
         els-block]
        [(Prim 'not (list e))
         (explicate-pred e els-block thn-block)]
        [(Prim op arg*)
         #:when (set-member? (comparison-ops) op)
         (delay (IfStmt (Prim op arg*)
                        (force (block->goto thn-block))
                        (force (block->goto els-block))))]
        [(Let x rhs body)
         (define body-block (explicate-pred body thn-block els-block))
         (explicate-assign rhs x body-block)]
        [(If cnd thn els)
         (delay
           (define thn-goto (block->goto thn-block))
           (define els-goto (block->goto els-block))
           (define new-thn (explicate-pred thn thn-goto els-goto))
           (define new-els (explicate-pred els thn-goto els-goto))
           (force (explicate-pred cnd new-thn new-els)))]
        [else
         (error 'explicate-pred "unmatched ~a" cnd)]
        ))

    (define/override (explicate-control p)
      (match p
        [(Program info body)
         (set! control-flow-graph '())
         (define body-block (force (explicate-tail body)))
         (Program info (CFG (dict-set control-flow-graph 'start body-block)))]
         ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> C1 -> x86*

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'cmpq 'set 'andq 'xorq 'movzbq)))

    (define/override (binary-op->inst op)
      (match op
	 ['and 'andq]
	 [else (super binary-op->inst op)]
	 ))

    (define/public (immediate? e)
      (match e
        [(Imm n) #t]
        [else #f]))

    (define/public (compare->cc cmp)
      (match cmp
	 ['eq? 'e]
	 ['< 'l]
	 ['<= 'le]
	 ['> 'g]
	 ['>= 'ge]
	 [else (error 'compare->cc "unmatched ~a" cmp)]
	 ))

    ;; select-instr-arg : arg -> imm
    (define/override (select-instr-arg e)
      (match e
        [(Bool #t) (Imm 1)]
        [(Bool #f) (Imm 0)]
        [else
         (super select-instr-arg e)]
        ))
      
    (define/override (select-instr-stmt e)
      (match e
        [(Assign lhs (Bool b))
         (let ([lhs (select-instr-arg lhs)]
               [rhs (select-instr-arg (Bool b))])
           (list (Instr 'movq (list rhs lhs))))]
        [(Assign lhs (Prim 'not (list e)))
         (define new-lhs (select-instr-arg lhs))
         (define new-e (select-instr-arg e))
         (cond [(equal? new-e new-lhs)
                (list (Instr 'xorq (list (Imm 1) new-lhs)))]
               [else (list (Instr 'movq (list new-e new-lhs))
                           (Instr 'xorq (list (Imm 1) new-lhs)))])]
        [(Assign lhs (Prim cmp (list e1 e2)))
         #:when (set-member? (comparison-ops) cmp)
         (define new-lhs (select-instr-arg lhs))
         ;; Swap operands because the ordering for x86 cmpq is weird. -Jeremy
         (define new-e1 (select-instr-arg e2))
         (define new-e2 (select-instr-arg e1))
         ;; The second operand of cmpq can't be an immediate.
         ;; We handle this here instead of in patch-instructions
         ;; because if new-e2 is an immediate, doing register
         ;; allocation isn't going to change that.
         ;; Also, this expansion causes a minor change in the
         ;; lifetimes of variables in e1 and e2, so its
         ;; good to have that information available for
         ;; the register allocator. -Jeremy
         (define comparison
           (cond [(immediate? new-e2)
                  (list (Instr 'movq (list new-e2 (Reg 'rax)))
                        (Instr 'cmpq (list new-e1 (Reg 'rax))))]
                 [else 
                  (list (Instr 'cmpq (list new-e1 new-e2)))]))
         ;; This works because movzbq %al, %rax is a valid instruction
         (append comparison
                 (list (Instr 'set (list (compare->cc cmp) (ByteReg 'al)))
                       (Instr 'movzbq (list (ByteReg 'al) new-lhs)))
                 )]
        [else (super select-instr-stmt e)]
        ))

    ;; select-instr-tail : tail -> instr list
    (define/override (select-instr-tail t)
      (match t
        [(Goto label)
         (list (Jmp label))]
        [(IfStmt (Prim cmp (list e1 e2)) (Goto thn-label) (Goto els-label))
         (let ([a1 (select-instr-arg e1)]
               [a2 (select-instr-arg e2)])
           (list (Instr 'cmpq (list a2 a1))
                 (JmpIf (compare->cc cmp) thn-label)
                 (Jmp els-label)))]
        [else
         (super select-instr-tail t)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; remove-unreachable OBSOLETE

    (define/public (remove-unreachable! fun-name CFG new-CFG)
      (define G (CFG->graph CFG))
      (define in-degree (make-hash))
      (for ([u (in-vertices G)])
        (hash-set! in-degree u 0))
      ;; compute in-degree
      (for ([u (in-vertices G)])
        (for ([v (get-neighbors G u)])
          (hash-set! in-degree v (+ 1 (hash-ref in-degree v)))))
        
      (define (compare u v)
        (<= (hash-ref in-degree u) (hash-ref in-degree v)))
      (define Q (make-pqueue compare))
        
      ;; collect vertices with zero in-degree into the Q (except the start vertex)
      (for ([u (in-vertices G)])
        (cond [(and (eq? 0 (hash-ref in-degree u))
                    (not (eq? u (symbol-append fun-name 'start))))
               (pqueue-push! Q u)]))

      (while (< 0 (pqueue-count Q))
        (define u (pqueue-pop! Q))
        (dict-remove! new-CFG u)
        (for ([v (get-neighbors G u)])
          (hash-set! in-degree v (- (hash-ref in-degree v) 1))
          (cond [(and (eq? 0 (hash-ref in-degree v))
                      (not (eq? v (symbol-append fun-name 'start))))
                 (pqueue-push! Q v)]))
        ) ;; while
      )

    #;(define/public (remove-unreachable p)
      (verbose "R2/remove-unreachable" p)
      (match p
        [(Program info (CFG G))
         (define new-CFG (make-hash G))
         (remove-unreachable! (string->symbol "") G new-CFG)
         (Program info (CFG (for/list ([(k v) (in-hash new-CFG)])
                              (cons k v))))]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; remove-jumps
    ;;
    ;; If there is only one jump to a block, then remove the block and
    ;; replace the jump with the block itself. We place this pass
    ;; after instruction selection so that we can reuse the auxilliary
    ;; functions for creating an explicit graph that are also needed
    ;; for liveness analysis.

    ;; TODO: bug? under-live doesn't know how to deal with jumps from
    ;; the middle of a block.  Though this probably doesn't affect
    ;; correctness, just means more things interfere than they
    ;; should. -Jeremy

    (define/public (remove-jumps-CFG fun-name CFG)
      (debug "remove-jumps-CFG: " CFG)
      (define trans-G (transpose (CFG->graph CFG)))
      (define new-CFG (make-hash CFG))
      (define conclusion (symbol-append fun-name 'conclusion))
      (for ([v (tsort trans-G)] #:when (not (equal? v conclusion)))
        (define adj (get-neighbors trans-G v))
        (when (and (= (length adj) 1)
                   (not (equal? adj conclusion)))
          (define u (first adj))
          (match* ((dict-ref new-CFG u) (dict-ref new-CFG v))
            [((Block u-info u-ss) (Block v-info v-ss))
             (define-values (u-front u-last)
               (split-at u-ss (- (length u-ss) 1)))
             (match u-last
               [(list (Jmp label))
                (cond [(eq? label v)
                       (dict-set! new-CFG u
                                  (Block u-info (append u-front v-ss)))
                       (dict-remove! new-CFG v)
                       (remove-vertex! trans-G v)]
                      )]
               [else ;; ignore indirect-jmp, tail-jmp 
                (void)])]))
        )
      (for/list ([(k v) (in-hash new-CFG)])
        (cons k v)))

    (define/public (remove-jumps p)
      (verbose "R2/remove-jumps" p)
      (match p
        [(Program info (CFG G))
         (Program info (CFG (remove-jumps-CFG (string->symbol "") G)))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live
    
    (define/override (free-vars a)
      (match a
        [(ByteReg r) (set (byte-reg->full-reg r))]
        [(Prim cmp (list e1 e2))
         #:when (set-member? (comparison-ops) cmp)
         (set-union (free-vars e1) (free-vars e2))]
        [else (super free-vars a)]
        ))
    
    (define/override (read-vars instr)
      (match instr
        [(Instr 'movzbq (list s d)) (free-vars s)]
        [(Instr 'cmpq (list s1 s2)) (set-union (free-vars s1) (free-vars s2))]
        [(Instr binop (list s d))
         #:when (set-member? '(andq xorq) binop)
         (set-union (free-vars s) (free-vars d))]
        [(Instr 'set (list cc d)) (set)]
        [(JmpIf cc label) (set)]
        [else (super read-vars instr)]))
    
    (define/override (write-vars instr)
      (match instr
        [(Instr 'movzbq (list s d)) (free-vars d)]
        [(Instr 'cmpq (list s1 s2)) (set '__flag)]
        [(Instr binop (list s d))
         #:when (set-member? '(andq xorq) binop)
         (free-vars d)]
        [(Instr 'set (list cc d)) (free-vars d)]
        [(JmpIf cc label) (set)]
        [else (super write-vars instr)]))

    (define/public (adjacent-instr s)
      (match s
        [(Jmp label)      (list label)]
        [(JmpIf cc label) (list label)]
        [else (list)]))

    (define/public (adjacent-block b)
      (match b
        [(Block info ss)
         (for/fold ([outs (list)]) ([s ss])
           (append outs (adjacent-instr s)))]
        ))

    (define/public (CFG->graph cfg)
      (define G (make-multigraph '()))
      (for ([label (in-dict-keys cfg)])
        (add-vertex! G label))
      (for ([(s b) (in-dict cfg)])
        (for ([t (adjacent-block b)])
          (add-directed-edge! G s t)))
      G)
    
    (define/public (live-before label CFG-hash)
      (match (hash-ref CFG-hash label)
        [(Block info ss)
         (car (dict-ref info 'lives))]))

    (define/public (uncover-live-CFG cfg fun-name)
      (define G (CFG->graph cfg))
      (define CFG-hash (make-hash))
      (define trans-G (transpose G))
      (define conclusion (symbol-append fun-name 'conclusion))
      (define label->live (make-hash (list (cons conclusion (set 'rax 'rsp)))))
      (for ([label (tsort trans-G)] #:when (not (equal? label conclusion)))
        (debug "uncover live, block" label)
        (define live-after
          (for/fold ([lives (set)])
                    ([node (in-neighbors G label)])
            (debug "successor" node)
            (set-union lives (dict-ref label->live node))))
        (define new-block (uncover-live-block (dict-ref cfg label) live-after))
        (hash-set! CFG-hash label new-block)
        (dict-set! label->live label (live-before label CFG-hash))
        ) ;; for
      (hash->list CFG-hash))

    (define/override (uncover-live ast)
      (verbose "uncover-live " ast)
      (match ast
        [(Program info (CFG G))
         (Program info (CFG (uncover-live-CFG G (string->symbol ""))))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph, removes liveness

    (define/override (build-interference-instr live-after G)
      (lambda (ast)
        (verbose "build-interference-instr" ast live-after)
        (match ast
          [(Instr 'movzbq (list s d))
           ;; treat movzbq like a movq
           ((super build-interference-instr live-after G)
            (Instr 'movq (list s d)))
           ast]
          [else ((super build-interference-instr live-after G) ast)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-move-graph

    ;; nothing to change here

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-homes
    
    (define/override (assign-homes-imm homes)
      (lambda (e)
	(match e
          [(ByteReg r) (ByteReg r)]          
          [else ((super assign-homes-imm homes) e)]
          )))
    
    (define/override (assign-homes-instr homes)
      (lambda (e)
        (verbose "R2/assign-homes-instr" e)
	(match e
          [(Instr 'set (list cc imm))
           (Instr 'set (list cc ((assign-homes-imm homes) imm)))]
          [(JmpIf cc label)
           (JmpIf cc label)]
          [else
           ((super assign-homes-instr homes) e)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; patch-instructions

    (define/override (patch-instr e)
      (match e
        [(JmpIf cc label) (list (JmpIf cc label))]
        [(Instr 'cmpq (list a1 a2))
         (match* (a1 a2)
           [(a1 (Imm n2))
            (list (Instr 'movq (list (Imm n2) (Reg 'rax)))
                  (Instr 'cmpq (list a1 (Reg 'rax))))]
           [((? in-memory? n1) (? in-memory? n2))
            (list (Instr 'movq (list n2 (Reg 'rax)))
                  (Instr 'cmpq (list n1 (Reg 'rax))))]
           [(_ _)
            (list (Instr 'cmpq (list a1 a2)))])]
        ;; destination of movzbq must be a register -Andre
        [(Instr 'movzbq (list s (? in-memory? d)))
         (list (Instr 'movzbq (list s (Reg 'rax)))
               (Instr 'movq (list (Reg 'rax) d)))]
        [else
         (super patch-instr e)]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86

    (define/override (print-x86-imm e)
      (match e
        [(ByteReg r) (format "%~a" r)]
        [else (super print-x86-imm e)]
        ))

    (define/override (print-x86-instr e)
      (verbose "R2/print-x86-instr" e)
      (match e
        [(Instr 'set (list cc d)) (format "\tset~a\t~a\n" cc (print-x86-imm d))]
        [(Instr 'cmpq (list s1 s2))
         (format "\tcmpq\t~a, ~a\n" (print-x86-imm s1) (print-x86-imm s2))]
        [(JmpIf cc label) (format "\tj~a ~a\n" cc (label-name label))]
        [else (super print-x86-instr e)]
        ))

    )) ;; compile-R2

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes

(define cond-passes
  (let ([compiler (new compile-R2)])
    `(("shrink"
       ,(lambda (p) (send compiler shrink p))
       ,interp-R2
       ,type-check-R2)
      ("uniquify"
       ,(lambda (p) (send compiler uniquify p))
       ,interp-R2
       ,type-check-R2)
      ("partial-eval"
       ,(lambda (p) (send compiler partial-eval p))
       ,interp-R2)
      ("remove-complex-opera*"
       ,(lambda (p) (send compiler remove-complex-opera* p))
       ,interp-R2
       ,type-check-R2)
      ("explicate-control"
       ,(lambda (p) (send compiler explicate-control p))
       ,interp-C1
       ,type-check-C1)
      ("select-instructions"
       ,(lambda (p) (send compiler select-instructions p))
       ,interp-pseudo-x86-1)
      ("uncover-live"
       ,(lambda (p) (send compiler uncover-live p))
       ,interp-pseudo-x86-1)
      ("build-interference"
       ,(lambda (p) (send compiler build-interference p))
       ,interp-pseudo-x86-1)
      ("build-move-graph"
       ,(lambda (p) (send compiler build-move-graph p))
       ,interp-pseudo-x86-1)
      ("allocate-registers"
       ,(lambda (p) (send compiler allocate-registers p))
       ,interp-x86-1)
      ("remove-jumps"
       ,(lambda (p) (send compiler remove-jumps p))
       ,interp-x86-1)
      ("patch-instructions"
       ,(lambda (p) (send compiler patch-instructions p))
       ,interp-x86-1)
      ("print-x86"
       ,(lambda (p) (send compiler print-x86 p))
       #f)
      )))
