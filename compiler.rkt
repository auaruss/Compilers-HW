#lang racket
(require racket/set racket/stream)
(require graph)
(require racket/fixnum)
(require "interp-R0.rkt")
(require "interp-R1.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require racket/dict)
(require racket/set)

(define globalCFG (directed-graph '()))
(define-vertex-property globalCFG instructions)
(define-vertex-property globalCFG live-before-set)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; R0 examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]
    ))

(define (flip-R0 e)
  (match e
    [(Program info e) (Program info (flip-exp e))]
    ))


;; Next we have the partial evaluation pass described in the bzook.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    ))

(define (pe-R0 p)
  (match p
    [(Program info e) (Program info (pe-exp e))]
    ))

(define (test-pe p)
  (assert "testing pe-R0"
     (equal? (interp-R0 p) (interp-R0 (pe-R0 p)))))

(test-pe (parse-program `(program () (+ 10 (- (+ 5 3))))))
(test-pe (parse-program `(program () (+ 1 (+ 3 1)))))
(test-pe (parse-program `(program () (- (+ 3 (- 5))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW3 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Type-Check Pass: R2 -> R2

(define (boolean-operator? op)
  (match op
    ['and #t]
    ['or #t]
    ['not #t]
    [else #f]))

(define (comparison-operator? op)
  (match op
    ['eq? #t]
    ['< #t]
    ['<= #t]
    ['> #t]
    ['>= #t]
    [else #f]))

(define (type-check-exp env)
  (lambda (e)
    (match e
      [(Var x) (dict-ref env x)]
      [(Int n) 'Integer]
      [(Bool b) 'Boolean]
      [(Let x e body)
        (define Te ((type-check-exp env) e))
        (define Tb ((type-check-exp (dict-set env x Te)) body))
        Tb]
      [(Prim op (list)) 'Integer]
      [(Prim op (list e1)) 
       (match op
	 ['-   
          (define Te ((type-check-exp env) e1))
          (unless (equal? Te 'Integer)
            (error "argument to an arithmetic operator must be an integer, not" Te))
	  'Integer]
	 ['not 
          (define Te ((type-check-exp env) e1))
          (unless (equal? Te 'Boolean)
            (error "argument to a boolean operator must be a boolean, not" Te))
	  'Boolean])]
      [(Prim op (list e1 e2))
       (match op
         ['eq? 
          (define Te1 ((type-check-exp env) e1))
          (define Te2 ((type-check-exp env) e2))
          (unless (equal? Te1 Te2)
            (error "arguments to eq? must be the same type, not" Te1 'and Te2))
	  'Boolean]
         [`,y #:when (boolean-operator? op)
          (define Te1 ((type-check-exp env) e1))
          (define Te2 ((type-check-exp env) e2))
          (unless (equal? Te1 'Boolean)
            (error "argument to a boolean operator must be a boolean, not" Te1))
          (unless (equal? Te2 'Boolean)
            (error "argument to a boolean operator must be a boolean, not" Te2))
	  'Boolean]
         [`,y #:when (comparison-operator? op)
          (define Te1 ((type-check-exp env) e1))
          (define Te2 ((type-check-exp env) e2))
          (unless (equal? Te1 'Integer)
            (error "argument to a comparison operator must be a integer, not" Te1))
          (unless (equal? Te2 'Integer)
            (error "argument to a copmarison operator must be an integer, not" Te2))
	  'Boolean]
	 [else
          (define Te1 ((type-check-exp env) e1))
          (define Te2 ((type-check-exp env) e2))
          (unless (equal? Te1 'Integer)
            (error "argument to an arithmetic operator must be an integer, not" Te1))
          (unless (equal? Te2 'Integer)
            (error "argument to an arithmetic operator must be an integer, not" Te2))
         'Integer])] 
      [(If e1 e2 e3)
          (define Te1 ((type-check-exp env) e1))
          (define Te2 ((type-check-exp env) e2))
          (define Te3 ((type-check-exp env) e3))
          (unless (equal? Te1 'Boolean)
            (error "If condition must be a boolean, not" Te1))
          (unless (equal? Te2 Te3)
            (error "branches of an if statement must be the same type, not" Te2 'and Te3))
	  Te2]
      [else
        (error "type-check-exp couldn't match" e)])))

(define (type-check env)
  (lambda (e)
    (match e
      [(Program info body)
        (define Tb ((type-check-exp '()) body))
        (unless (equal? Tb 'Integer)
          (error "result of the program must be an integer, not" Tb))
        (Program info body)]
)))

(define (type-check-R2 p)
  (match p
    [(Program info e)
     ((type-check '()) p)]
    ))

(define r2p1 (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()))) (Prim 'read '())))))
(define r2p2 (Program '() (Prim '+ (list (If (Prim 'not (list (Bool #f))) (Int 7) (Int 6)) (Prim 'read '())))))
(define r2p3 (Program '() (Prim '+ (list (If (Prim 'not (list (Bool #f))) (Int 7) (Bool #t)) (Prim 'read '())))))
(define r2p4 (Program '() (Prim '+ (list (If (Prim 'not (list (Bool #f))) (Bool #f) (Bool #t)) (Prim 'read '())))))

;;((type-check-R2 '()) r2p4)

;;Shrink Pass: R2 -> R2
(define (shrink-exp e)
  (match e
    [(Prim '- (list e1 e2)) (Prim '+ (list (shrink-exp e1) (Prim '- (list (shrink-exp e2)))))]
    [(Prim 'and (list e1 e2)) (If (shrink-exp e1) (If (shrink-exp e2) (Bool #t) (Bool #f)) (Bool #f))]
    [(Prim 'or (list e1 e2)) (If (shrink-exp e1) (Bool #t) (If (shrink-exp e2) (Bool #t) (Bool #f)))]
    [(Prim '<= (list e1 e2)) (Prim 'not (list (shrink-exp (Prim '> (list e1 e2)))))]
    [(Prim '> (list e1 e2)) (let ([new-tmp (gensym 'tmp)]) (Let new-tmp (shrink-exp e1) (Prim '< (list (shrink-exp e2) (Var new-tmp)))))]
    [(Prim '>= (list e1 e2)) (Prim 'not (list (shrink-exp (Prim '< (list e1 e2)))))]
    [(Prim op (list e1)) (Prim op (list (shrink-exp e1)))]
    [(Prim op (list e1 e2)) (Prim op (list (shrink-exp e1) (shrink-exp e2)))]
    [(If e1 e2 e3) (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3))]
    [else e]
    ))

(define (shrink p)
  (match p
    [(Program info e)
     (Program info (shrink-exp e))]
    ))

(define r2p5 (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()) (Int 7))) (Prim 'read '())))))
(define r2p6 (Program '() (Prim '+ (list (If (Prim 'and (list (Prim 'not (list (Bool #f))) (Prim 'or (list (Prim '<= (list (Int 7) (Int 8))) (Bool #f))))) (Int 7) (Int 6)) (Prim 'read '())))))
(define r2p7 (Program '() (Prim '+ (list (If (Prim 'and (list (Prim 'not (list (Bool #f))) (Prim 'or (list (Prim '> (list (Int 7) (Int 8))) (Bool #f))))) (Int 7) (Int 6)) (Prim 'read '())))))
(define r2p8 (Program '() (Prim '+ (list (If (Prim 'and (list (Prim 'not (list (Bool #f))) (Prim 'or (list (Prim '<= (list (Int 7) (Int 8))) (Bool #f))))) (Int 7) (Int 6)) (Prim 'read '())))))

;;(interp-R2 (shrink ((type-check-R2 '()) r2p8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniquify-exp
  (λ (symtab)
    (λ (exp)
      (match exp
        [(Var x)
         (Var (symbol-table-lookup symtab x))]
        [(Int n) (Int n)]
        [(Bool b) (Bool b)]
	[(Let x e body)
         (let ([new-x (gensym x)]) 
           (Let new-x
                ((uniquify-exp symtab) e)
                ((uniquify-exp (extend-symbol-table symtab x new-x)) body)))]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp symtab) e)))]
	[(If e1 e2 e3)
	 (If ((uniquify-exp symtab) e1) ((uniquify-exp symtab) e2) ((uniquify-exp symtab) e3) )]))))


(define init-symbol-table
  (λ ()
    (let ([init (make-immutable-hash)]) init)))

(define symbol-table-lookup
  (λ (symtab x)
    (if (empty? (hash-ref symtab x)) (error "variable not in scope") (car (hash-ref symtab x)))))

(define extend-symbol-table
  (λ (symtab x new-x)
    (hash-set symtab
              x
              (let [(not-found (λ () '()))]
                (cons new-x (hash-ref symtab x not-found))))))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e)
     (Program info ((uniquify-exp (init-symbol-table)) e))]
    ))

;;(interp-R2 (uniquify (shrink ((type-check-R2 '()) r2p8))))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
    (match p
      [(Program info e)
       (Program info (rco-exp e))]))

;; rco-atom : exp -> exp * (var * exp) list
(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(Let x rhs body)
     (define new-rhs (rco-exp rhs))
     (define-values (new-body body-ss) (rco-atom body))
     (values new-body (append `((,x . ,new-rhs)) body-ss))]
    [(Prim op es) 
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ss `((,tmp . ,(Prim op new-es)))))]
    [(If e1 e2 e3)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e (list e1 e2 e3)]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (match new-es
	    [(list e1 e2 e3)
	     (values (Var tmp)
             (append ss `((,tmp . ,(If e1 e2 e3)))))])]
    ))

(define (make-lets^ bs e)
  (match bs
    [`() e]
    [`((,x . ,e^) . ,bs^)
     (Let x e^ (make-lets^ bs^ e))]))

;; rco-exp : exp -> exp
(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets^ (append* sss) (Prim op new-es))]
    [(If e1 e2 e3)
     ;;(define-values (expression symbols) (rco-atom e))
     ;;(make-lets^ (append* symbols) expression)]
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e (list e1 e2 e3)]) (rco-atom e)))
     (match new-es
	    [(list e1 e2 e3)
	     (make-lets^ (append* sss) (If e1 e2 e3))])]
    ))


#|(define map-values
    (λ (f ls)
      (cond
        [(empty? ls)
         (values '() '())]
        [(cons? ls) (define-values (v1 v2) (f (car ls)))
                    (define-values (ls1 ls2) (map-values f (cdr ls)))
                    (values (cons v1 ls1) (cons v2 ls2))])))

(define rco-atom
  (λ (e)
    (match e
      [(Var x) (values e '())]
      [(Int n) (values e '())]
      [(Bool b) (values e '())]
      [(Let x e body)
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (list (cons v (Let x (rco-exp e) (rco-exp body))))))] ;; rco-atom on body, no gensym
      [(Prim op es)
       (define-values (exps syms)
         (map-values
          (λ (e)
            (cond [(or (Var? e) (Int? e))
                   (rco-atom e)]
                  [else (let ([v (gensym 'tmp)])
                          (define-values (_1 _2) (rco-atom e))
                          (values (Var v)
                                  (cons (cons v _1) _2)))]))
          es))
       (let ([v (gensym 'tmp)])
         (values (Var v)
                 (cons (cons v (Prim op exps)) (append* syms))))]
      [(If e1 e2 e3)
       (define-values (new-e1 s1) (rco-atom e1))
       (define-values (new-e2 s2) (rco-atom e2))
       (define-values (new-e3 s3) (rco-atom e3))
       (define ss (append* (list s1 s2 s3)))
       (define tmp (gensym 'tmp))
       (values (Var tmp) (append ss `((,tmp . ,(If new-e1 new-e2 new-e3)))))
       ])))

(define (make-lets bs e)
  (match bs
    [`() e]
    [`((,x . ,e^) . ,bs^)
     (Let x e^ (make-lets bs^ e))]))

(define rco-exp
  (λ (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
      [(Prim op es)
       (define-values (exps symbols) (map-values rco-atom es))
       (foldl
        (λ (elem acc)
          (if (empty? elem) acc (Let (car elem) (cdr elem) acc)))
        (Prim op exps)
        (append* (reverse symbols)))]
      [(If e1 e2 e3)
       (define-values (expression symbols) (rco-atom e))
       (make-lets (append* symbols) expression)]
      )))
|#

(define rp (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()))) (Prim 'read '())))))

;;(interp-R2 (remove-complex-opera* (uniquify (shrink ((type-check-R2 '()) r2p8)))))

;; Sam

; explicate-tail : R1 -> C0Tail x [Var]
; takes in R1 expression and produces C0 Tail and list of let-bound variables
(define (explicate-tail r2exp)
  (match r2exp
    [(Int n)
     (values (Return (Int n)) '())]
    [(Bool b)
     (values (Return (Bool b)) '())]
    [(Prim 'read '())
     (values (Return (Prim 'read '())) '())]
    [(Prim op (list e))
     (values (Return (Prim op (list e))) '())]
    [(Prim op (list e1 e2))
     (values (Return (Prim op (list e1 e2))) '())] 
    [(Var x)
     (values (Return (Var x)) '())]
    [(Let x e body) 
     (define-values (c1tail let-binds) (explicate-tail body))
     (define-values (c1tail^ let-binds^) (explicate-assign e (Var x) c1tail)) ;; why var here
     (values c1tail^ (cons x (append let-binds let-binds^)))]
    [(If e1 e2 e3)
     (define-values (c1tail-then let-binds-then) (explicate-tail e2))
     (define-values (c1tail-else let-binds-else) (explicate-tail e3))  
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new))
     ]
    ))


; explicate-assign : R1 Var C0Tail -> C0Tail x [Var]
; takes in R1 expression, the variable where it will be assigned, and a C0Tail that comes
; after the assignment. Returns a C0Tail and list of variables

;; simplify

(define (explicate-assign r2exp v c)
  (match r2exp
    [(Int n)
     (values (Seq (Assign v (Int n)) c) '())]
    [(Bool b)
     (values (Seq (Assign v (Bool b)) c) '())]
    [(Prim 'read '())
     (values (Seq (Assign v (Prim 'read '())) c) '())]
    [(Prim op (list e))
     (values (Seq (Assign v (Prim op (list e))) c)
             '())] 
    [(Prim op (list e1 e2))
     (values (Seq (Assign v (Prim op (list e1 e2))) c)
             '())] 
    [(Var x)
     (values (Seq (Assign v (Var x)) c) '())]
    [(Let x e body) 
     (define-values (c1tail let-binds) (explicate-assign body v c))
     (define-values (c1tail^ let-binds^) (explicate-assign e (Var x) c1tail))
     (values c1tail^ (cons x (append let-binds let-binds^)))]
    [(If e1 e2 e3)
     (define label (gensym 'block))
     #;(add-vertex! globalCFG (cons label c))
     (add-vertex! globalCFG label)
     (instructions-set! label c)
     (live-before-set-set! label (list->set '()))
     (define-values (c1tail-then let-binds-then) (explicate-assign e2 v (Goto label)))
     (define-values (c1tail-else let-binds-else) (explicate-assign e3 v (Goto label)))
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new))
     ]
    ))

;; explicate-pred : R2_exp x C1_tail x C1_tail -> C1_tail x var list
(define (explicate-pred r2exp c1 c2)
  (match r2exp
    [(Bool b)
     (values (if b c1 c2) '())]
    [(Var v)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     #;(add-vertex! globalCFG (cons label1 c1))
     #;(add-vertex! globalCFG (cons label2 c2))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (values (IfStmt (Prim 'eq? (list r2exp (Bool #t))) (Goto label1) (Goto label2))
             '())]
    [(Prim op (list e))
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     #;(add-vertex! globalCFG (cons label1 c1))
     #;(add-vertex! globalCFG (cons label2 c2))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (values (IfStmt r2exp (Goto label1) (Goto label2))
             '())] 
    [(Prim op (list e1 e2))
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     #;(add-vertex! globalCFG (cons label1 c1))
     #;(add-vertex! globalCFG (cons label2 c2))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (values (IfStmt r2exp (Goto label1) (Goto label2))
             '())]
    [(If e1 e2 e3)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     #;(add-vertex! globalCFG (cons label1 c1))
     #;(add-vertex! globalCFG (cons label2 c2))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (define-values (c1tail-then let-binds-then) (explicate-pred e2 (Goto label1) (Goto label2)))
     (define-values (c1tail-else let-binds-else) (explicate-pred e3 (Goto label1) (Goto label2)))
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new)) 
     ]
     ))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e)
     (define-values (c0t let-binds) (explicate-tail e))
     (add-vertex! globalCFG 'start)
     (instructions-set! 'start c0t) 
     (define labeled-instruction-lists (for/list ([l (get-vertices globalCFG)]) (cons l (instructions l))))
     (Program (cons (cons 'locals let-binds) info) (CFG labeled-instruction-lists))]))

(define given-let (Let 'x (Let 'y (Prim '- (list (Int 42))) (Var 'y)) (Prim '- (list (Var 'x)))))
(define r1program-let (Program '() given-let))

(define new-let (Let 'x (Prim 'read '()) (Let 'y (Prim 'read '())
                                              (Prim '+ (list (Var 'x) (Prim '- (list (Var 'y))))))))

(define newprog (Program '() new-let))

(define asdf (Program '() (Let 'x (Prim '+ (list (Prim 'read '()) (Prim 'read '()))) (Var 'x))))

;; todo: more testing!

;; note: explicate-control passes all tests in run-tests.rkt

; atm? : c0exp -> bool

(define (atm? c0exp)
    (match c0exp
      [(Int n) #t]
      [(Var x) #t]
      [(Bool b) #t]
      [_ #f]))

; sel-ins-atm : C0atm -> pseudo-x86
; takes in a c0 atom and converts to pseudo-x86

(define (sel-ins-atm c0a)
  (match c0a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Bool b) 
     (match b
      [#t (Imm 1)]
      [#f (Imm 0)])]))

; sel-ins-stmt : C0stmt -> pseudo-x86
; takes in a c0 statement and converts to pseudo-x86

(define (sel-ins-stmt c0stmt)
  (match c0stmt
    [(Assign v e)
     (if (atm? e)
         (list (Instr 'movq (list (sel-ins-atm e) v)))
         (match e
           [(Prim 'read '())
            (list (Callq 'read_int)
                  (Instr 'movq (list (Reg 'rax) v)))]
           [(Prim '- (list atm))
            (define x86atm (sel-ins-atm atm))
            (if (equal? x86atm v)
                (list (Instr 'negq (list v)))
                (list (Instr 'movq (list x86atm v))
                      (Instr 'negq (list v))))]
           [(Prim '+ (list atm1 atm2))
            (define x86atm1 (sel-ins-atm atm1))
            (define x86atm2 (sel-ins-atm atm2))
            (cond [(equal? x86atm1 v) (list (Instr 'addq (list x86atm2 v)))]
                  [(equal? x86atm2 v) (list (Instr 'addq (list x86atm1 v)))]
                  [else (list (Instr 'movq (list x86atm1 v))
                              (Instr 'addq (list x86atm2 v)))])]
           [(Prim 'not (list atm))
            (if (eqv? v atm)
                (list (Instr 'xorq (list (Imm 1) v)))
                (list (let ([atm_ (sel-ins-atm atm)])
                        (Instr 'movq (list atm_ v)))
                      (Instr 'xorq (list (Imm 1) v))))]
           [(Prim 'eq? (list atm1 atm2))
            (let ([atm1_ (sel-ins-atm atm1)]
                  [atm2_ (sel-ins-atm atm2)]
                  [v_ (sel-ins-atm v)])
              (list
               (Instr 'cmpq (list atm2_ atm1_))
               (Instr 'set (list 'e (Reg 'al)))
               (Instr 'movzbq (list (Reg 'al) v_))))]
           [(Prim '< (list atm1 atm2))
           (let ([atm1_ (sel-ins-atm atm1)]
                  [atm2_ (sel-ins-atm atm2)]
                  [v_ (sel-ins-atm v)])
              (list
               (Instr 'cmpq (list atm2_ atm1_))
               (Instr 'set (list 'l (Reg 'al)))
               (Instr 'movzbq (list (Reg 'al) v_))))]))]))

; sel-ins-tail : C1tail -> pseudo-x86
; takes in a c1 tail and converts it ot pseudo-x86

(define (sel-ins-tail c0t)
  (match c0t
    [(Return e)
     (append (sel-ins-stmt (Assign (Reg 'rax) e))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (define x86stmt (sel-ins-stmt stmt))
     (define x86tail (sel-ins-tail tail))
     (append x86stmt x86tail)]
    [(Goto label)
     (list (Jmp label)) ]
    [(IfStmt (Prim 'eq? (list arg1 arg2)) (Goto label1) (Goto label2))
     (let ([arg1_ (sel-ins-atm arg1)]
           [arg2_ (sel-ins-atm arg2)])
       (list
        (Instr 'cmpq (list arg2_ arg1_))
        (JmpIf 'e label1)
        (Jmp label2)))]
    [(IfStmt (Prim '< (list arg1 arg2)) (Goto label1) (Goto label2))
     (let ([arg1_ (sel-ins-atm arg1)]
           [arg2_ (sel-ins-atm arg2)])
       (list
        (Instr 'cmpq (list arg2_ arg1_))
        (JmpIf 'l label1)
        (Jmp label2)))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(Program info (CFG es))
     (Program info (CFG (for/list ([ls es]) (cons (car ls) (Block '() (sel-ins-tail (cdr ls)))))))]))

;;(explicate-control (remove-complex-opera* (uniquify (shrink (type-check-R2 r2p8)))))
;; I think this is right...
;; todo: check/test !

;; note: select-instructions passes all tests in run-tests.rkt

;; /Sam

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;  Assignment 2 Work (Replaces assign-homes)    ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-live
(define (add-global-CFG-edges label1 instr-ls)
  (match instr-ls
    ['() '()] ;;does nothing, just ends the function
    [ls 
      (match (car ls)
	[(Jmp 'conclusion) (add-global-CFG-edges label1 (cdr ls))]
        [(JmpIf cc label2) (add-directed-edge! globalCFG label1 label2) (add-global-CFG-edges label1 (cdr ls))]
        [(Jmp label2) (add-directed-edge! globalCFG label1 label2) (add-global-CFG-edges label1 (cdr ls))]
        [_ (add-global-CFG-edges label1 (cdr ls))]
        )]
    ))

;; turn association list of blocks in CFG into graph
;; then reverse topo sort said graph, uncover-live that sorted list

(define (instr-arg-varset arg)
  (match arg 
	 [(Var v) (set v)]
	 [_ (list->set '())]))

(define (instr-read-varset instr) 
  (match instr
	 [(Instr 'set (list e1 e2))
	  (list->set '())]
	 [(Instr 'movzbq (list e1 e2))
	  (list->set '())]
	 [(Instr 'movq (list e1 e2))
	  (instr-arg-varset e1)]
	 [(Instr op (list e1 e2))
	  (set-union (instr-arg-varset e1) (instr-arg-varset e2))]
	 [(Instr 'negq (list e1))
	  (instr-arg-varset e1)]
	 [_ (list->set '())]))

(define (instr-written-varset instr)
  (match instr
	 [(Instr 'cmpq (list e1 e2))
	  (list->set '())]
	 [(Instr op (list e1 e2))
	  (instr-arg-varset e2)]
	 [(Instr 'negq (list e1))
	  (instr-arg-varset e1)]
	 [_ (list->set '())]))

(define (uncover-live-helper instr-ls live-after-set label)
  (cond
    #;[(null? instr-ls) (list (list->set '()))]
    [(null? instr-ls) (live-before-set-set! label live-after-set) (list live-after-set)]
    [else (let ([new-live-after-set (set-union (set-subtract live-after-set (instr-written-varset (car instr-ls))) (instr-read-varset (car instr-ls)))]) 
	  (append (uncover-live-helper (cdr instr-ls) new-live-after-set label) (list live-after-set)))]
    ))

(define (get-first-live ls)
  (match ls
    ['() (list->set '())]
    [else (set-union (live-before-set (car ls)) (get-first-live (cdr ls)))]
    )
  )

(define (find-instructions label es)
  (if (eq? label (car (car es))) 
      (match (cdr (car es))
        [(Block b-info ls) ls])
      (find-instructions label (cdr es)))
  )

(define (sort-blocks ordered-vertices es)
  (for/list ([label ordered-vertices]) 
	    (define first-live-after-set (get-first-live (get-neighbors (transpose globalCFG) label)))
	    (cons label (Block (uncover-live-helper (reverse (find-instructions label es)) first-live-after-set label) (find-instructions label es)))))

(define (uncover-live p)
  (match p
    [(Program info (CFG es)) 
     (for ([ls es]) (add-global-CFG-edges (car ls) (match (cdr ls)
							       [(Block b-info instr-ls) instr-ls])))
     (Program info (CFG (sort-blocks (tsort (transpose globalCFG)) es) #;(for/list ([ls es]) (cons (car ls) (match (cdr ls)
							     [(Block b-info instr-ls) 
							      (Block (uncover-live-helper (reverse instr-ls) (list->set '())) instr-ls)])))))]
    ))


;;Test from book chapter 3
(define ch3example (Let 'v (Int 1) (Let 'w (Int 46) (Let 'x (Prim '+ (list (Var 'v) (Int 7))) (Let 'y (Prim '+ (list (Int 4) (Var 'x))) (Let 'z (Prim '+ (list (Var 'x) (Var 'w))) (Prim  '+ (list (Var 'z) (Prim '- (list (Var 'y)))))))))))
(define ch3program (Program '() ch3example))
(define r1-11 (Prim '+ (list (Int 1) (Prim '+ (list (Int 1) (Prim '+ (list (Int 1) (Int 1))))))))
(define r1-11prog (Program '() r1-11))

(define r1-12 (Prim '+ (list (Let 'x (Int 1) (Var 'x)) (Let 'x (Int 1) (Var 'x)))))
(define r1-12prog (Program '() r1-12))

(define asd (Prim '+ (list (Int 1) (Prim '+ (list (Int 1) (Int 1))))))
(define asdp (Program '() asd))

;;match case used to print the block's info
#;(uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify ch3program)))))
#;(match (uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify ch3program)))))
       [(Program info (CFG es))
	(match (cdr (car es)) 
	       [(Block b-info instr-ls) b-info])])

;; build-interference

;; movzbq is similar to movq
;; consider register al the same as rax


(define caller-save-for-alloc '(%al rax rdx rcx rsi rdi r8 r9 r10 r11))

(define (free-vars arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [(Deref r i) (set r)]
    [(Imm n) (set)]
    [else (error "free vars, unhandled" arg)]))

(define (write-vars instr)
  (match instr
    [(Instr 'movq (list s d)) (free-vars d)]
    [(Instr name arg*)
     (free-vars (last arg*))]
    [(Jmp label) (set)]
    [(Callq f) (set)]
    [else (error "write-vars unmatched" instr)]))

(define (build-interference-instr live-after g)
  (λ (ast)
    (match ast
      [(Instr 'movq (list s d))
       (for ([v live-after])
         (for ([d (free-vars d)])
           (cond [(equal? (Var v) s) (verbose "same source" s)]
                 [(equal? v d) (verbose "skip self edge on" d)]
                 [else (add-edge! g d v)])))
       ast]
      [(Callq f)
       (for ([v live-after])
         (for ([u caller-save-for-alloc])
           (if (equal? v u)
               (verbose "skip self edge on" v)
               (add-edge! g u v))))
       ast]
      [else
       (for ([v live-after])
         (for ([d (write-vars ast)])
           (if (equal? v d)
               (verbose "skip self edge on" v)
               (add-edge! g d v))))
       ast])))
                       
                  

(define (build-interference-block ast g)
  (match ast
    [(Block info ss)
     (let* ([lives (dict-ref info 'lives)]
            [live-afters (cdr lives)]
            [new-ss (for/list ([inst ss] [live-after live-afters])
                      ((build-interference-instr live-after g) inst))]
            [new-info (dict-remove info 'lives)])
       (Block info ss))]))

(define (build-interference ast)
  (match ast
    [(Program info (CFG cfg))
     (let* ([locals (dict-ref info 'locals)]
            [g (undirected-graph '())])
       (for ([v locals]) (add-vertex! g v))
       (let* ([new-cfg (for/list ([(label block) (in-dict cfg)])
                         (cons label (build-interference-block block g)))]
              [new-info (dict-set info 'conflicts g)])
         (Program new-info (CFG new-cfg))))]))

;; allocate-registers

;; get-longest : [List] -> List
;; gets longest list in list of lists

(define (get-longest ls)
  (foldr (λ (e acc) (if (> (length e) (length acc)) e acc)) (car ls) (cdr ls))
  #;(if (empty? ls)
      '()
      (if (>= (length (first ls))
              (length (get-longest (rest ls))))
          (first ls)
          (get-longest (rest ls)))))

;; get-longest-val : [Hash Any List] -> List
;; get the longest value in hash

(define (get-longest-val hash)
  (let ([vals (hash-values hash)])
    (get-longest vals)))

;; choose-least : [Nat] Nat -> Nat
;; returns the smallest Nat not in the given set

(define (choose-least satset cand)
  (if (empty? satset)
      cand
      (let ([m (apply min satset)])
        (if (< cand m)
            cand
            (choose-least (remove m satset) (add1 cand))))))

;; hash-key : [Hash Key Val] Val -> Key
;; returns the (a) key that maps to given val

(define (hash-key hash val)
  (local
    [(define (first-cdr ls v)
        (if (empty? ls)
            (error "val not found")
            (if (equal? (cdr (car ls)) v)
                (car (car ls))
                (first-cdr (cdr ls) v))))]
    (first-cdr (hash->list hash) val)))

;; A SatSet is a set of nats (colors)

;; color-graph : InterferenceGraph -> [Hash Var SatSet] -> [(Var . Nat)]
;; takes an unweighted/undirected intereference graph and a mutable hashtable of vars to saturation sets
;; in program, returns mapping from var to color (Nat)

;; interference graph from book example
(define ig1 (unweighted-graph/undirected '((t z) (z y) (z w) (y w) (x w) (w v))))
(define h1 (make-hash '((t . ()) (z . ()) (y . ()) (w . ()) (x . ()) (v . ()))))
(define testhash (hash 't '(a e w) 'z '() 'y '(w q f f d) 'w '() 'x '(z a) 'v '(e)))

#;(define ch3ig
  (match (build-interference (uncover-live (select-instructions
                                            (explicate-control (remove-complex-opera* (uniquify ch3program))))))
    [(Program info CFG) (dict-ref info 'conflicts)]))

#;(define r1-11ig
  (match (build-interference (uncover-live (select-instructions
                                            (explicate-control (remove-complex-opera* (uniquify r1-11prog))))))
    [(Program info CFG) (dict-ref info 'conflicts)]))

#;(define r1-12ig
  (match (build-interference (uncover-live (select-instructions
                                            (explicate-control (remove-complex-opera* (uniquify r1-12prog))))))
    [(Program info CFG) (dict-ref info 'conflicts)]))

#;(define asdig
  (match (build-interference (uncover-live (select-instructions
                                            (explicate-control (remove-complex-opera* (uniquify asdp))))))
    [(Program info CFG) (dict-ref info 'conflicts)]))





(define (color-graph ig hash)
  (if (hash-empty? hash)
      empty
      (let* ([maxsat (get-longest-val hash)]
             [maxsat-vert (hash-key hash maxsat)]
             [adj-verts (if (has-vertex? ig maxsat-vert)
                            (get-neighbors ig maxsat-vert)
                            '())]
             [col (choose-least maxsat 0)])
        (for-each (λ (vert) (if (and (hash-has-key? hash vert)
                                     (not (member col (hash-ref hash vert))))
                                (hash-set! hash vert
                                           (cons col (hash-ref hash vert)))
                                hash))
                      adj-verts)
        (hash-remove! hash maxsat-vert)
        (cons `(,maxsat-vert . ,col) (color-graph ig hash)))))

;; allocate-registers-exp : pseudo-x86 InterferenceGraph [Var] [Var . Home] -> pseudo-x86
;; takes in pseudo-x86 exp, intereference graph, and list of vars, returns
;; a pseudo-x86 exp with allocated registers according to color-graph

(define REGCOLS '((0 . rbx) (1 . rcx) (2 . rdx) (3 . rsi) (4 . rdi) (5 . r8) (6 . r9)
                            (7 . r10) (8 . r11) (9 . r12) (10 . r13) (11 . r14)))

;; change sig to
;; allocate-registers-exp : pseudo-x86 [Var . Nat] -> pseudo-x86

(define (allocate-registers-exp e coloring)
    (match e
      [(Reg reg) (Reg reg)]
      [(Imm int) (Imm int)]
      [(Var v) (let ([colnum (dict-ref coloring v)])
                 (if (<= colnum 11)
                     (Reg (dict-ref REGCOLS colnum))
                     (Deref 'rbp (+ 48 (* -8 (- colnum 11))))))]
      [(Instr 'addq (list e1 e2)) (Instr 'addq (list (allocate-registers-exp e1 coloring)
                                                     (allocate-registers-exp e2 coloring)))]
      [(Instr 'subq (list e1 e2)) (Instr 'subq (list (allocate-registers-exp e1 coloring)
                                                     (allocate-registers-exp e2 coloring)))]
      [(Instr 'movq (list e1 e2)) (Instr 'movq (list (allocate-registers-exp e1 coloring)
                                                     (allocate-registers-exp e2 coloring)))]
      [(Instr 'negq (list e1)) (Instr 'negq (list (allocate-registers-exp e1 coloring)))]
      [(Callq l) (Callq l)]
      [(Retq) (Retq)]
      [(Instr 'pushq (list e1)) (Instr 'pushq (list (allocate-registers-exp e1 coloring)))]
      [(Instr 'popq (list e1)) (Instr 'popq (list (allocate-registers-exp e1 coloring)))]
      [(Jmp e1) (Jmp e1)]
      [(Block info es) (Block info (for/list ([e es]) (allocate-registers-exp e coloring)))]))

#;(define (allocate-registers-exp e ig vars)
  (let* ([hash (make-hash (map (λ (var) `(,var . ())) vars))]
         [coloring (color-graph ig hash)])
    (match e
      [(Reg reg) (Reg reg)]
      [(Imm int) (Imm int)]
      [(Var v) (let ([colnum (dict-ref coloring v)])
                 (if (<= colnum 11)
                     (Reg (dict-ref REGCOLS colnum))
                     (Deref 'rbp (* -8 (- colnum 11)))))]
      [(Instr 'addq (list e1 e2)) (Instr 'addq (list (allocate-registers-exp e1 ig vars)
                                                     (allocate-registers-exp e2 ig vars)))]
      [(Instr 'subq (list e1 e2)) (Instr 'subq (list (allocate-registers-exp e1 ig vars)
                                                     (allocate-registers-exp e2 ig vars)))]
      [(Instr 'movq (list e1 e2)) (Instr 'movq (list (allocate-registers-exp e1 ig vars)
                                                     (allocate-registers-exp e2 ig vars)))]
      [(Instr 'negq (list e1)) (Instr 'negq (list (allocate-registers-exp e1 ig vars)))]
      [(Callq l) (Callq l)]
      [(Retq) (Retq)]
      [(Instr 'pushq (list e1)) (Instr 'pushq (list (allocate-registers-exp e1 ig vars)))]
      [(Instr 'popq (list e1)) (Instr 'popq (list (allocate-registers-exp e1 ig vars)))]
      [(Jmp e1) (Jmp e1)]
      [(Block info es) (Block info (for/list ([e es]) (allocate-registers-exp e ig vars)))])))

#;(define (allocate-registers p)
  (match p
    [(Program info (CFG es))
     (Program (list (cons 'stack-space 16 #;(calc-stack-space (dict-ref info 'locals) #;(cdr (car info)))))
              (CFG (for/list ([ls es]) (cons (car ls)
                                             (allocate-registers-exp
                                              (cdr ls)
                                              (color-graph (dict-ref info 'conflicts)
                                                           (make-hash (map (λ (var) `(,var . ())) (dict-ref info 'locals)))))
                                             #;(allocate-registers-exp (cdr ls)
                                                                     (dict-ref info 'conflicts)
                                                                     (dict-ref info 'locals))))))]))

(define (allocate-registers p)
  (match p
    [(Program info (CFG es))
     (let ([coloring (color-graph (dict-ref info 'conflicts)
                                  (make-hash (map (λ (var) `(,var . ())) (dict-ref info 'locals))))])
       (Program (list (cons 'stack-space (let ([f (* 8 (- (if (> (length coloring) 0)
                                                              (apply max (map (λ (assoc) (cdr assoc)) coloring))
                                                              0) 11))])
                                           (if (negative? f)
                                               0
                                               f #;(+ f (modulo f 16))))))
                (CFG 
                 (for/list ([ls es]) (cons (car ls)
                                           (allocate-registers-exp
                                            (cdr ls)
                                            coloring)
                                           #;(allocate-registers-exp (cdr ls)
                                                                     (dict-ref info 'conflicts)
                                                                     (dict-ref info 'locals)))))))]))

;; assign-homes : pseudo-x86 -> pseudo-x86

(define (calc-stack-space ls)
  (cond
    [(null? ls) 0]
    [else (+ 8 (calc-stack-space (cdr ls)))]
    ))

(define (find-index v ls)
  (cond
    ;;[(eq? v (Var-name (car ls))) 1]
    [(eq? v (car ls)) 1]
    [else (add1 (find-index v (cdr ls)))]
    ))

;; simplify
;; todo: FIX PUSHQ/POPQ

(define (assign-homes-exp e ls)
  (match e
    [(Reg reg) (Reg reg)]
    [(Imm int) (Imm int)]
    [(Var v) (Deref 'rbp (* -8 (find-index v (cdr ls))))]
    [(Instr 'addq (list e1 e2)) (Instr 'addq (list (assign-homes-exp e1 ls) (assign-homes-exp e2 ls)))]
    [(Instr 'subq (list e1 e2)) (Instr 'subq (list (assign-homes-exp e1 ls) (assign-homes-exp e2 ls)))]
    [(Instr 'movq (list e1 e2)) (Instr 'movq (list (assign-homes-exp e1 ls) (assign-homes-exp e2 ls)))]
    [(Instr 'negq (list e1)) (Instr 'negq (list (assign-homes-exp e1 ls)))]
    [(Callq l) (Callq l)]
    [(Retq) (Retq)]
    [(Instr 'pushq (list e1)) (Instr 'pushq (list (assign-homes e1 ls)))]
    [(Instr 'popq (list e1)) (Instr 'popq (list (assign-homes e1 ls)))]
    [(Jmp e1) (Jmp e1)]
    [(Block info es) (Block info (for/list ([e es]) (assign-homes-exp e ls)))]
    ))

(define (assign-homes p)
  (match p
    [(Program info (CFG es)) (Program (list (cons 'stack-space (calc-stack-space (cdr (car info)))))
                                      (CFG (for/list ([ls es]) (cons (car ls) (assign-homes-exp (cdr ls) (car info))))))]
    ))

;; note: assign-homes passes all tests in run-tests.rkt

;;TEST
;;(assign-homes (Program (list (cons 'locals (list (Var 'x) (Var 'y)))) (CFG (list (cons 'start (Block '() (list (Instr 'movq (list (Imm 42) (Var 'y))) (Instr 'negq (list (Var 'y))) (Instr 'movq (list (Var 'y) (Var 'x))) (Instr 'movq (list (Var 'x) (Reg 'rax))) (Instr 'negq (list (Reg 'rax))) (Jmp 'conclusion))))))))
;;(assign-homes (select-instructions (explicate-control r1program-let)))
;;(let ([x (+ (read) (read))]) x)
;(remove-complex-opera* (uniquify (Program '() (Let 'x (Prim '+ (list (Prim 'read '()) (Prim 'read '()))) (Var 'x)))))


;; Grant

;; patch-instructions : psuedo-x86 -> x86

;; fix cmpq with second arg as immediate
;; fix movzbq target arg must be register (move stack var into reg for it)

(define (patch-instructions-instr px86instr)
  (match px86instr
    [(Instr 'cmpq (list e1 e2))
     (match e2
       [(Imm n) (list (Instr 'movq (list e2 (Reg 'rax))) (Instr 'cmpq (list e1 (Reg 'rax))))]
       [_ (list (Instr 'cmpq (list e1 e2)))])]
    [(Instr 'movzbq (list e1 e2))
     (match e2 
       [(Deref reg n) (list (Instr 'movq (list e2 (Reg 'rax))) (Instr 'movzbq (list e1 (Reg 'rax))))]
       [_ (list (Instr 'movzbq (list e1 e2)))])]
    [(Instr op (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (list (Instr 'movq (list e1 (Reg 'rax))) (Instr op (list (Reg 'rax) e2)))]
       [(list x y) (list (Instr op (list e1 e2)))]
       )]
    [(Instr op (list e1)) (list (Instr op (list e1)))]
    [i (list i)]
    ))

(define (patch-instructions-block px86block)
  (match px86block
    [(Block info es) (Block info (append* (for/list ([i es]) (patch-instructions-instr i))))]
    ))

(define (patch-instructions p)
  (match p
    [(Program info (CFG es)) (Program info (CFG (for/list ([ls es]) (cons (car ls) (patch-instructions-block (cdr ls))))))]
    ))

;;TEST
;;(patch-instructions (assign-homes (select-instructions (explicate-control r1program-let))))

;;  (error "TODO: code goes here (patch-instructions)"))

;; Grant/Sam

(define r1-10 (Let 'x (Prim 'read '()) (Let 'y (Prim 'read '()) (Prim '+ (list (Var 'x) (Prim '- (list (Var 'y))))))))
(define r1-10prog (Program '() r1-10))

(define x86prog (patch-instructions (assign-homes (select-instructions (explicate-control r1program-let)))))
;x86prog

;rsp  rbx r12 r13 r14 r15
;
(define callee-reg-str-push
  "\tpushq\t%rbx\n\tpushq\t%r12\n\tpushq\t%r13\n\tpushq\t%r14\n\tpushq\t%r15")
;
(define callee-reg-str-pop
  "popq\t%r15\n\tpopq\t%r14\n\tpopq\t%r13\n\tpopq\t%r12\n\tpopq\t%rbx")

(define (main-str stacksize)
  (format "\t.globl ~a\n~a:\n\tpushq\t%rbp\n\tmovq\t%rsp, %rbp\n~a\n\tsubq\t$~a, %rsp\n\tjmp ~a\n"
           (label-name "main") (label-name "main") callee-reg-str-push (+ 8 (align stacksize 16)) (label-name "start"))) ;; 16 is stack-space

(define (concl-str stacksize)
  (format "~a:\n\taddq\t$~a, %rsp\n\t~a\n\tpopq\t%rbp\n\tretq"
          (label-name "conclusion") (+ 8 (align stacksize 16)) callee-reg-str-pop)) ;; stack-space

(define (stringify-arg arg)
  (match arg
    [(Imm n) (format "$~a" n)]
    [(Reg r) (format "%~a" r)]
    [(Deref r n) (format "~a(%~a)" n r)]))

(define (stringify-in instr)
  (match instr
    [(Instr 'addq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "addq\t~a, ~a" st1 st2)]
    [(Instr 'subq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "subq\t~a, ~a" st1 st2)]
    [(Instr 'movq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "movq\t~a, ~a" st1 st2)]
    [(Instr 'negq (list a))
     (define st (stringify-arg a))
     (format "negq\t~a" st)]
    [(Callq lbl)
     (format "callq\t~a" (label-name lbl))]
    [(Retq) "retq"]
    [(Instr 'pushq arg)
     (define st (stringify-arg arg))
     (format "pushq\t~a" st)]
    [(Instr 'popq arg)
     (define st (stringify-arg arg))
     (format "popq\t~a" st)]
    [(Jmp lbl)
     (format "jmp\t~a" (label-name lbl))]))

;; format-x86 : [instr] -> string
(define (format-x86 ins)
  (foldr (λ (f r) (string-append "\t" f "\n" r)) "" (map stringify-in ins)))
     
     ;(format "~a:\n\t" label)

;; print-x86 : x86 -> string
(define (print-x86 p)
  (match p
    [(Program info (CFG es)) (format "~a:\n~a~a~a"
                                     (label-name "start")
                                     (format-x86 (Block-instr* (cdr (car es))))
                                     (main-str (cdr (car info)))
                                     (concl-str (cdr (car info))))]))

;;(printf (print-x86 (patch-instructions (allocate-registers (build-interference (uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify (Program '() (Prim 'read (list)))))))))))))
;;(printf (print-x86 (patch-instructions (allocate-registers (build-interference (uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify ch3program))))))))))
;;Grant/Sam
