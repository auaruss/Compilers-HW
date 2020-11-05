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
(AST-output-syntax 'concrete-syntax)

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

;; example program from lecture:
#;(let ([v (vector 42)])
    (let ([w (vector v)])
      (let ([v^ (vector-ref w 0)])
        (vector-ref v^ 0))))

(define hw4ex (Let 'v (Prim 'vector (list (Int 42)))
                   (Let 'w (Prim 'vector (list (Var 'v)))
                        (Let 'v^ (Prim 'vector-ref (list (Var 'w) (Int 0)))
                             (Prim 'vector-ref (list (Var 'v^) (Int 0)))))))

(define hw4prog (Program '() hw4ex))


;;Type-Check Pass: R4 -> R4

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

(define (fun-def-name d)
  (match d 
    [(Def f (list `[,xs : ,ps] ...) rt info body)
     f]))

(define (fun-def-type d)
  (match d
    [(Def f (list `[,xs : ,ps] ...) rt info body)
     `(,@ps -> ,rt)]))

(define (type-check-exp env)
  (lambda (e)
    (define recur (type-check-exp env))
    (match e
      [(Var x) (let ([t (dict-ref env x)]) 
		 (values (HasType e t) t))]
      [(Int n) (values (HasType e 'Integer) 'Integer)]
      [(Bool b) (values (HasType e 'Boolean) 'Boolean)]
      [(Let x e body)
        (define-values (e^ Te) ((type-check-exp env) e))
        (define-values (b^ Tb) ((type-check-exp (dict-set env x Te)) body))
        (values 
	  (HasType (Let x e^ b^) Tb) Tb)]
      [(Void) (values (HasType (Void) 'Void) 'Void)]
      [(Prim 'vector es)
        (define-values (e* t*) (for/lists (e* t*) ([e es]) (recur e)))
        (let ([t `(Vector ,@t*)])
          (values (HasType (Prim 'vector e*) t) t))]
      [(Prim 'vector-ref (list e (Int i)))
        (define-values (e^ t) (recur e))
        (match t
         [`(Vector ,ts ...)
           (unless (and (exact-nonnegative-integer? i) (< i (length ts)))
             (error 'type-check-exp "invalid index ~a" i))
           (let ([t (list-ref ts i)])
           (values
             (HasType (Prim 'vector-ref
                            (list e^ (HasType (Int i) 'Integer)))
                      t)
           t))]
         [else (error "expected a vector in vector-ref, not" t)])]
      [(Prim 'vector-set! (list e1 (Int i) e2))
        (if (and (Var? e1) (Var? e2)) 
           (unless (not (eq? (Var-name e1) (Var-name e2)))
             (error 'type-check-exp "vector-set! exp1 and exp2 must no be same, both are ~a" e1))
	   (Var? e1) ;;null operation, does nothing
           )
	(define-values (e1^ t1) (recur e1))
        (define-values (e2^ t2) (recur e2))
	(match e1^
         [(HasType e* `(Vector ,ts ...))
           (unless (and (exact-nonnegative-integer? i) (< i (length ts)))
             (error 'type-check-exp "invalid index ~a" i))
           (unless (equal? (list-ref ts i) t2)
             (error 'type-check-exp "cannot change vector element's type from ~a to ~a" (list-ref ts i) t2))
	   (values
             (HasType (Prim 'vector-set!
                            (list (HasType e* `(Vector ,@ts)) (HasType (Int i) 'Integer) e2^))
                      'Void)
           'Void)]
         [else (error "expected a vector in vector-set, not" t1)])]
      [(Prim op (list)) (values (HasType e 'Integer) 'Integer)]
      [(Prim op (list e1)) 
       (match op
	 ['-   
          (define-values (e1^ Te1) (recur e1))
	  (unless (equal? Te1 'Integer)
            (error "argument to an arithmetic operator must be an integer, not" Te1))
	  (values (HasType (Prim op (list e1^)) 'Integer) 'Integer)]
	 ['not 
          (define-values (e1^ Te1) (recur e1))
          (unless (equal? Te1 'Boolean)
            (error "argument to a boolean operator must be a boolean, not" Te1))
	  (values (HasType (Prim op (list e1^)) 'Boolean) 'Boolean)])]
      [(Prim op (list e1 e2))
       (match op
         ['eq? 
          (define-values (e1^ Te1) (recur e1))
          (define-values (e2^ Te2) (recur e2))
          (unless (equal? Te1 Te2)
            (error "arguments to eq? must be the same type, not" Te1 'and Te2))
	  (values (HasType (Prim op (list e1^ e2^)) 'Boolean) 'Boolean)]
         [`,y #:when (boolean-operator? op)
          (define-values (e1^ Te1) (recur e1))
          (define-values (e2^ Te2) (recur e2))
          (unless (equal? Te1 'Boolean)
            (error "argument to a boolean operator must be a boolean, not" Te1))
          (unless (equal? Te2 'Boolean)
            (error "argument to a boolean operator must be a boolean, not" Te2))
	  (values (HasType (Prim op (list e1^ e2^)) 'Boolean) 'Boolean)]
         [`,y #:when (comparison-operator? op)
          (define-values (e1^ Te1) (recur e1))
          (define-values (e2^ Te2) (recur e2))
          (unless (equal? Te1 'Integer)
            (error "argument to a comparison operator must be a integer, not" Te1))
          (unless (equal? Te2 'Integer)
            (error "argument to a copmarison operator must be an integer, not" Te2))
	  (values (HasType (Prim op (list e1^ e2^)) 'Boolean) 'Boolean)]
	 [else
          (define-values (e1^ Te1) (recur e1))
          (define-values (e2^ Te2) (recur e2))
          (unless (equal? Te1 'Integer)
            (error "argument to an arithmetic operator must be an integer, not" Te1))
          (unless (equal? Te2 'Integer)
            (error "argument to an arithmetic operator must be an integer, not" Te2))
          (values (HasType (Prim op (list e1^ e2^)) 'Integer) 'Integer)])] 
      [(If e1 e2 e3)
       (define-values (e1^ Te1) (recur e1))
       (define-values (e2^ Te2) (recur e2))
       (define-values (e3^ Te3) (recur e3))
       (unless (equal? Te1 'Boolean)
         (error "If condition must be a boolean, not" Te1))
       (unless (equal? Te2 Te3)
         (error "branches of an if statement must be the same type, not" Te2 'and Te3))
       (values (HasType (If e1^ e2^ e3^) Te2) Te2)]
      [(Apply e es)
       (define-values (e^ ty) ((type-check-exp env) e))
       (define-values (e* ty*) (for/lists (e* ty*) ([e (in-list es)])
                                 ((type-check-exp env) e)))
       (match ty
         [`(,ty^* ... -> ,rt)
          (for ([arg-ty ty*] [prm-ty ty^*])
          (unless (equal? arg-ty prm-ty)
            (error "argument ~a not equal to parameter ~a" arg-ty prm-ty)))
          (values (HasType (Apply e^ e*) rt) rt)]
         [else (error "expected a function, not" ty)])]
      [else
        (error "type-check-exp couldn't match" e)])))

(define (type-check-def env)
  (lambda (e)
    (match e
      [(Def f (and p:t* (list `[,xs : ,ps] ...)) rt info body)
       (define new-env (append (map cons xs ps) env))
       (define-values (body^ ty^) ((type-check-exp new-env) body))
       (unless (equal? ty^ rt)
         (error "body type ~a not equal to return type ~a" ty^ rt))
       (Def f p:t* rt info body^)])))

;;type-check for R3 and before
#;(define (type-check env)
  (lambda (e)
    (match e
      [(Program info body)
        (define-values (b^ Tb) ((type-check-exp '()) body))
	  (unless (equal? Tb 'Integer)
            (error "result of the program must be an integer, not" Tb))
          (Program info b^)]
)))

(define (type-check env)
  (lambda (e)
    (match e
      [(ProgramDefsExp info ds body)
       (define new-env (for/list ([d ds])
                        (cons (fun-def-name d) (fun-def-type d))))
       (define ds^ (for/list ([d ds])
                             ((type-check-def new-env) d)))
       (define-values (body^ ty) ((type-check-exp new-env) body))
       (unless (equal? ty 'Integer)
         (error "result of the program must be an integer, not " ty))
       (ProgramDefsExp info ds^ body^)]
      [else (error 'type-check "R4/type-check unmatched ~a" e)])))

(define (type-check-R4 p)
  (match p
    [(Program info e)
     (define new-p (ProgramDefsExp info '() e))
     ((type-check '()) new-p)]
    [(ProgramDefsExp info ds body)
     ((type-check '()) p)]
    ))

#;(define (type-check-R3 p)
  (match p
    [(Program info e)
     ((type-check '()) p)]
    ))

#;(define (type-check-R2 p)
  (match p
    [(Program info e)
     ((type-check '()) p)]
    ))

(define r2p1 (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()))) (Prim 'read '())))))
(define r2p2 (Program '() (Prim '+ (list (If (Prim 'not (list (Bool #f))) (Int 7) (Int 6)) (Prim 'read '())))))
(define r2p3 (Program '() (Prim '+ (list (If (Prim 'not (list (Bool #f))) (Int 7) (Bool #t)) (Prim 'read '())))))
(define r2p4 (Program '() (Prim '+ (list (If (Prim 'not (list (Bool #f))) (Bool #f) (Bool #t)) (Prim 'read '())))))
(define r3_1 (Program '() (Let 'v (Prim 'vector (list (Int 1) (Int 2))) (Int 42))))
(define r3_2 (Program '() (Let 'v (Prim 'vector (list (Int 20) (Int 22))) (Prim '+ (list (Prim 'vector-ref (list (Var 'v) (Int 0))) (Prim 'vector-ref (list (Var 'v) (Int 1))))))))
(define r3_15 (Program '() 
		       (Let 'v1 (Prim 'vector (list (Int 0))) 
			    (Let 'g1 (Prim 'vector (list (Int 1) (Int 2) (Int 3) (Int 4) (Int 5)))
				 (Let 'dummy (If (Prim 'eq? (list (Prim 'read '()) (Int 0)))
                                                 (Prim 'vector-set! (list (Var 'v1) (Int 0) (Int 42)))
                                                 (Prim 'vector-set! (list (Var 'g1) (Int 0) (Int 42))))
				      (Prim 'vector-ref (list (Var 'v1) (Int 0))))))))

;;(type-check-R3 r3_15)

;;Shrink Pass: R2 -> R2
(define (shrink-exp e)
  (match e
    [(HasType (Prim '- (list e1 e2)) 'Integer) 
     (HasType (Prim '+ (list (shrink-exp e1) (HasType (Prim '- (list (shrink-exp e2))) 'Integer))) 'Integer)]
    [(HasType (Prim 'and (list e1 e2)) 'Boolean) 
     (HasType (If (shrink-exp e1) (HasType (If (shrink-exp e2) (HasType (Bool #t) 'Boolean) (HasType (Bool #f) 'Boolean)) 'Boolean) (HasType (Bool #f) 'Boolean)) 'Boolean)]
    [(HasType (Prim 'or (list e1 e2)) 'Boolean)
     (HasType (If (shrink-exp e1) (HasType (Bool #t) 'Boolean) (HasType (If (shrink-exp e2) (HasType (Bool #t) 'Boolean) (HasType (Bool #f) 'Boolean)) 'Boolean)) 'Boolean)]
    [(HasType (Prim '<= (list e1 e2)) 'Boolean)
     (HasType (Prim 'not (list (shrink-exp (HasType (Prim '> (list e1 e2)) 'Boolean)))) 'Boolean)]
    [(HasType (Prim '> (list e1 e2)) 'Boolean)
     (let ([new-tmp (gensym 'tmp)]) 
       (HasType (Let new-tmp (shrink-exp e1) (HasType (Prim '< (list (shrink-exp e2) (HasType (Var new-tmp) 'Integer))) 'Boolean)) 'Boolean))]
    [(HasType (Prim '>= (list e1 e2)) 'Boolean) 
     (HasType (Prim 'not (list (shrink-exp (HasType (Prim '< (list e1 e2)) 'Boolean)))) 'Boolean)]
    [(HasType (Prim op (list e1)) type)
     (HasType (Prim op (list (shrink-exp e1))) type)]
    [(HasType (Prim op (list e1 e2)) type)
     (HasType (Prim op (list (shrink-exp e1) (shrink-exp e2))) type)]
    [(HasType (If e1 e2 e3) type)
     (HasType (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3)) type)]
    [else e]
    ))

(define (shrink p)
  (match p
    [(ProgramDefsExp info ds e)
     (ProgramDefs info (append ds (list (Def 'main '() 'Integer '() (shrink-exp e)))))]
    ))

(define r2p5 (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()) (Int 7))) (Prim 'read '())))))
(define r2p6 (Program '() (Prim '+ (list (If (Prim 'and (list (Prim 'not (list (Bool #f))) (Prim 'or (list (Prim '<= (list (Int 7) (Int 8))) (Bool #f))))) (Int 7) (Int 6)) (Prim 'read '())))))
(define r2p7 (Program '() (Prim '+ (list (If (Prim 'and (list (Prim 'not (list (Bool #f))) (Prim 'or (list (Prim '> (list (Int 7) (Int 8))) (Bool #f))))) (Int 7) (Int 6)) (Prim 'read '())))))
(define r2p8 (Program '() (Prim '+ (list (If (Prim 'and (list (Prim 'not (list (Bool #f))) (Prim 'or (list (Prim '<= (list (Int 7) (Int 8))) (Bool #f))))) (Int 7) (Int 6)) (Prim 'read '())))))

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
	 (If ((uniquify-exp symtab) e1) ((uniquify-exp symtab) e2) ((uniquify-exp symtab) e3) )]
	[(HasType e t)
	 (HasType ((uniquify-exp symtab) e) t)]))))


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
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (match d
				         [(Def label paramtypes returntype info e)
					  (Def label paramtypes returntype info ((uniquify-exp (init-symbol-table)) e))])))
     (ProgramDefs info new-ds)]
    ))

#;(define uptoexpose (uniquify (shrink (type-check-R3 hw4prog))))



(define (expose-allocation p)
  (match p
      [(Program info e)
       (Program info ((expose-allocation-exp '()) e))]))

(define (expose-allocation-exp env)
  (λ (e)
    (define recur (expose-allocation-exp env))
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x rhs body)
       (Let x (recur rhs) (recur body))]
      [(Prim 'vector-ref (list e^ int))
       (Prim 'vector-ref (list (recur e^) int))]
      [(Prim 'vector-set! (list exp1 int exp2))
       (Prim 'vector-set! (list (recur exp1) int (recur exp2)))]
      [(Prim op es)
       (Prim op (map recur es))]
      [(If e1 e2 e3)
       (If (recur e1) (recur e2) (recur e3))]
      [(HasType (Prim 'vector exps) type)
       (define i 0)
       (define bytes (* 8 (add1 (length exps))))
       (foldl
        (λ (elem acc)
          (let* ([x (string->symbol (string-append "x" (number->string i)))]
	        [q (HasType (Let x (recur elem) acc) type)])
            (set! i (add1 i))
            q))
        (let ([q (HasType
                  (Let '_
                       (HasType
                        (If (HasType (Prim '< (list
                                               (HasType (Prim '+ (list (HasType (GlobalValue 'free_ptr) 'Integer) (HasType (Int bytes) 'Integer))) 'Integer)
                                               (HasType (GlobalValue 'fromspace_end) 'Integer))) 'Boolean)
                            (HasType (Void) 'Void)
                            (HasType (Collect bytes) 'Void)) 'Void)
                       (HasType
                        (Let 'v
                             (HasType (Allocate (length exps) type) type)
                             (HasType
                              (foldl
                               (λ (elem acc)
                                 (let* ([x (string->symbol (string-append "x" (number->string i)))]
                                        [xtype (match type
                                                 [`(Vector ,ts ...)
                                                  (unless (and (exact-nonnegative-integer? i) (< i (length ts)))
                                                    (error 'expose-allocation-exp "invalid index ~a" i))
                                                  (list-ref ts i)]
                                                 [else (error "expected a vector in vector-ref, not" type)])]
                                        [q (HasType
                                            (Let '_
                                                 (HasType (Prim
                                                           'vector-set!
                                                           (list (HasType (Var 'v) type)
                                                                 (HasType (Int i) 'Integer)
                                                                 (HasType (Var x)
                                                                          xtype))) 'Void)
                                                 acc) type)])
                                   (set! i (add1 i))
                                   q
                                   ))
                               (begin
                                 (set! i 0)
                                 (HasType (Var 'v) type))
                               exps #;(map recur exps)) type)) type)) type)])
          (begin (set! i 0)
                 q))
          exps)]
      [(HasType e t)
       (HasType (recur e) t)]
      [(Void) (Void)])))

(define q (Program '() (Let 'v (Prim 'vector (list (Int 1) (Int 2))) (Prim 'vector-ref (list (Var 'v) (Int 0))))))

#;(expose-allocation (uniquify (shrink (type-check-R3 q))))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
    (match p
      [(Program info e)
       (Program info (rco-exp e))]))

;; rco-atom : exp -> exp * (var * exp) list
(define (rco-atom e)
  (match e
    [(Void) (values (Void) '())]
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(Let x rhs body)
     (define new-rhs (rco-exp rhs))
     (define-values (new-body body-ss) (rco-atom body))
     (values new-body (append `((,x . ,new-rhs)) body-ss))]
    [(HasType (Prim op es) t)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (values (HasType (Var tmp) t)
             (append ss `((,tmp . ,(HasType (Prim op new-es) t)))))]
    [(HasType (If e1 e2 e3) t)
     (define new-es
       (for/list ([e (list e1 e2 e3)]) (rco-exp e)))
     (define tmp (gensym 'tmp))
     (match new-es
	    [(list e1 e2 e3)
	     (values (HasType (Var tmp) t)
             `((,tmp . ,(HasType (If e1 e2 e3) t))))])]
    [(HasType (Collect n) t)
     (define tmp (gensym 'tmp))
     (values (HasType (Void) t)
             `((,tmp . ,(HasType (Collect n) t))))]
    [(HasType (GlobalValue name) t) 
     (define tmp (gensym 'tmp))
     (values (HasType (Var tmp) t)
             `((,tmp . ,(HasType (GlobalValue name) t))))]
    [(HasType (Allocate n t) t)
     (define tmp (gensym 'tmp))
     (values (HasType (Var tmp) t)
             `((,tmp . ,(HasType (Allocate n t) t))))]
    [(HasType e t)
     (define-values (new-e ss) (rco-atom e))
     (values (HasType new-e t) ss)]
    ))

(define (make-lets^ bs e)
  (match bs
    [`() e]
    [`((,x . ,e^) . ,bs^)
     (Let x e^ (make-lets^ bs^ e))]))

;; rco-exp : exp -> exp
(define (rco-exp e)
  (match e
    [(Void) (Void)]
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(HasType (Prim op es) t)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets^ (append* sss) (HasType (Prim op new-es) t))]
    [(If e1 e2 e3)
     (define new-es
       (for/list ([e (list e1 e2 e3)]) (rco-exp e)))
     (match new-es
	    [(list e1 e2 e3)
	     (If e1 e2 e3)])]
    [(Collect n) (Collect n)]
    [(GlobalValue name) (GlobalValue name)]
    [(Allocate n t) (Allocate n t)]
    [(HasType e t)
     (HasType (rco-exp e) t)]
    ))


(define rp (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()))) (Prim 'read '())))))

;;(interp-R2 (remove-complex-opera* (uniquify (shrink ((type-check-R2 '()) r2p8)))))

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
    [(Prim op ls)
     (values (Return (Prim op ls)) '())]
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
    [(HasType e t)
     (explicate-tail e)
     ]
    ))


; explicate-assign : R1 Var C0Tail -> C0Tail x [Var]
; takes in R1 expression, the variable where it will be assigned, and a C0Tail that comes
; after the assignment. Returns a C0Tail and list of variables

;; simplify

(define (explicate-assign r2exp v c)
  (match r2exp
    [(Void)
     (values (Seq (Assign v (Void)) c) '())]
    [(Collect n)
     (values (Seq (Collect n) c) '())]
    [(Allocate n t)
     (values (Seq (Assign v (Allocate n t)) c) '())]
    [(GlobalValue name)
     (values (Seq (Assign v (GlobalValue name)) c) '())]
    [(Int n)
     (values (Seq (Assign v (Int n)) c) '())]
    [(Bool b)
     (values (Seq (Assign v (Bool b)) c) '())]
    [(Prim 'read '())
     (values (Seq (Assign v (Prim 'read '())) c) '())]
    [(Prim op ls)
     (values (Seq (Assign v (Prim op ls)) c)
             '())] 
    [(Var x)
     (values (Seq (Assign v (Var x)) c) '())]
    [(Let x e body) 
     (define-values (c1tail let-binds) (explicate-assign body v c))
     (define-values (c1tail^ let-binds^) (explicate-assign e (Var x) c1tail))
     (values c1tail^ (cons x (append let-binds let-binds^)))]
    [(If e1 e2 e3)
     (define label (gensym 'block))
     (add-vertex! globalCFG label)
     (instructions-set! label c)
     (live-before-set-set! label (list->set '()))
     (define-values (c1tail-then let-binds-then) (explicate-assign e2 v (Goto label)))
     (define-values (c1tail-else let-binds-else) (explicate-assign e3 v (Goto label)))
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new))
     ]
    [(HasType e t)
     (define-values (c1tail let-binds) (explicate-assign e v c))
     (match c1tail
      [(Seq (Assign v e^) tail)
       (values (Seq (Assign v (HasType e^ t)) tail) let-binds)]
      [(Seq (Collect n) tail)
       (values (Seq (Collect n) tail) let-binds)])
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
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (values (IfStmt (Prim 'eq? (list r2exp (Bool #t))) (Goto label1) (Goto label2))
             '())]
    [(Prim op ls)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (values (IfStmt r2exp (Goto label1) (Goto label2))
             '())] 
    [(Let x e body)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (define temp (gensym 'tmp))
     (define-values (c1tail let-binds) (explicate-assign body (Var temp) (IfStmt (Prim 'eq? (list (Var temp) (Bool #t))) (Goto label1) (Goto label2))))
     (define-values (c1tail^ let-binds^) (explicate-assign e (Var x) c1tail))
     (values c1tail^ (cons x (cons temp (append let-binds let-binds^))))
     ]
    [(If e1 e2 e3)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (define-values (c1tail-then let-binds-then) (explicate-pred e2 (Goto label1) (Goto label2)))
     (define-values (c1tail-else let-binds-else) (explicate-pred e3 (Goto label1) (Goto label2)))
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new)) ]
    [(HasType e t)
     (explicate-pred e c1 c2)]
     ))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e)
     (define-values (c0t let-binds) (explicate-tail e))
     (add-vertex! globalCFG 'start)
     (instructions-set! 'start c0t)
     (live-before-set-set! 'start (set))
     (define labeled-instruction-lists (for/list ([l (get-vertices globalCFG)]) (cons l (instructions l))))
     (Program (cons (cons 'locals let-binds) info) (CFG labeled-instruction-lists))]))

(define given-let (Let 'x (Let 'y (Prim '- (list (Int 42))) (Var 'y)) (Prim '- (list (Var 'x)))))
(define r1program-let (Program '() given-let))

(define new-let (Let 'x (Prim 'read '()) (Let 'y (Prim 'read '())
                                              (Prim '+ (list (Var 'x) (Prim '- (list (Var 'y))))))))

(define newprog (Program '() new-let))

(define asdf (Program '() (Let 'x (Prim '+ (list (Prim 'read '()) (Prim 'read '()))) (Var 'x))))



;;uncover-locals-helper : C2 list of blocks -> association list of locals and their types
(define (uncover-locals-tail e)
  (match e
   [(Assign (Var v) (HasType e t))
    (list (cons v t))]
   [(Seq s t)
    (append (uncover-locals-tail s) (uncover-locals-tail t))]
   [_ (list)])
  )

(define (uncover-locals-helper es)
  (append* (for/list ([l es])
		     (uncover-locals-tail (cdr l)))))

;; uncover-locals : C2 -> C2
(define (uncover-locals p)
  (match p
    [(Program info (CFG es))
     (Program (dict-set info 'locals (uncover-locals-helper es)) (CFG es))]))

;;(uncover-locals (explicate-control (remove-complex-opera* (expose-allocation (uniquify (shrink (type-check-R3 r3_15)))))))

;; new select-instructions for R3

; atm? : c0exp -> bool

(define (atm? c0exp)
    (match c0exp
      [(HasType exp type) (atm? exp)]
      [(Int n) #t]
      [(Var x) #t]
      [(Bool b) #t]
      [_ #f]))

; sel-ins-atm : C0atm -> pseudo-x86
; takes in a c0 atom and converts to pseudo-x86

(define (sel-ins-atm c0a)
  (match c0a
    [(HasType atm type) (sel-ins-atm atm)]
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Bool b) 
     (match b
      [#t (Imm 1)]
      [#f (Imm 0)])]))

; sel-ins-stmt : C0stmt -> pseudo-x86
; takes in a c0 statement and converts to pseudo-x86

;; list->number : BinaryList -> Number
(define (list->number ls)
   (if (empty? ls)
       0
       (if (equal? 1 (car ls))
           (+ (list->number (cdr ls)) (expt 2 (length (cdr ls))))
           (list->number (cdr ls)))))

;; type->binary : Type -> BinaryList
(define (type->binary tp)
    (if (empty? tp)
        '()
        (if (and (list? (car tp)) (equal? (car (car tp)) 'Vector))
            (cons 1 (type->binary (cdr tp)))
            (cons 0 (type->binary (cdr tp))))))


;; calculate-tag : Number Type -> Number
;; calculates tag using following algorithm:
;; (1) converts given type into a binary number
;;      - this is done by placing a 1 at the spots that the tuple has a vector, 0 otherwise
;;      - e.g., '(Vector Int Boolean (Vector Int) Int (Vector)) => '(0 0 1 0 1)
;; (2) calculates the length of the type
;; (3) bitwise-or with length left-shifted 1 place and 1 (forwarding bit set)
;; (4) left-shift the type number by 7, bitwise-or with result of (3)
(define (calculate-tag len T)
  (let* ([type-num (arithmetic-shift (list->number (reverse (type->binary (cdr T)))) 7)]
         [type-len (bitwise-ior (arithmetic-shift len 1) 1)]
         [res (bitwise-ior type-num type-len)])
    res))

;;(calculate-tag 2 '(Vector (Vector Integer) (Vector Integer)))
;;(calculate-tag 3 '(Vector Integer Integer (Vector Integer)))

(define (sel-ins-stmt c0stmt)
  (match c0stmt
    [(HasType stmt type) (sel-ins-stmt stmt)]
    [(Collect n) (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
                       (Instr 'movq (list (Imm n) (Reg 'rsi))) ;; seems right
                       (Callq 'collect))]
    [(Assign v e)
     (if (atm? e)
         (list (Instr 'movq (list (sel-ins-atm e) v)))
         (match e
           [(HasType e^ t) (sel-ins-stmt (Assign v e^))]
           [(Allocate len T)
            (let ([tag (calculate-tag len T)]) ;; need to actually calculate tag using bitwise stuff
              (list (Instr 'movq (list (Global 'free_ptr) v))
                    (Instr 'addq (list (Imm (* 8 (add1 len))) (Global 'free_ptr)))
                    (Instr 'movq (list v (Reg 'r11)))
                    (Instr 'movq (list (Imm tag) (Deref 'r11 0)))))] ;; deref r11 at 0 always?
           [(Prim 'vector-ref (list atm (HasType (Int n) t)))
            (list (Instr 'movq (list (sel-ins-atm atm) (Reg 'r11))) ;; vec is atm?
                  (Instr 'movq (list (Deref 'r11 (* 8 (add1 n))) v)))]
           [(Prim 'vector-set! (list atm1 (HasType (Int n) t) atm2))
            (list (Instr 'movq (list (sel-ins-atm atm1) (Reg 'r11)))
                  (Instr 'movq (list (sel-ins-atm atm2) (Deref 'r11 (* 8 (add1 n)))))
                  (Instr 'movq (list (Imm 0) v)))]
           [(GlobalValue name) (list (Instr 'movq (list (Global name) v)))] ;; ?
           [(Void) (list (Instr 'movq (list (Imm 0) v)))]
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
    [(HasType tail type) (sel-ins-tail tail)]
    [(Return e)
     (append (sel-ins-stmt (Assign (Reg 'rax) e))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (define x86stmt (sel-ins-stmt stmt))
     (define x86tail (sel-ins-tail tail))
     (append x86stmt x86tail)]
    [(Goto label)
     (list (Jmp label)) ]
    [(IfStmt (Prim 'vector-ref (list v (HasType (Int i) 'Integer))) (Goto label1) (Goto label2))
     (let ([v_ (sel-ins-atm v)])
       (list
	(Instr 'movq (list v_ (Reg 'r11)))
        (Instr 'cmpq (list (Imm 1) (Deref 'r11 (* 8 (add1 i)))))
        (JmpIf 'e label1)
        (Jmp label2)))]
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
	    (define first-live-after-set (get-first-live (get-neighbors globalCFG label)))
	    (cons label (Block (uncover-live-helper (reverse (find-instructions label es)) first-live-after-set label) (find-instructions label es)))))

(define (uncover-live p)
  (match p
    [(Program info (CFG es)) 
     (for ([ls es]) (add-global-CFG-edges (car ls) (match (cdr ls)
							       [(Block b-info instr-ls) instr-ls])))
     (Program info (CFG (sort-blocks (tsort (transpose globalCFG)) es)))]
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

(define caller-save-for-alloc^ '(al rax rdx rcx rsi rdi r8 r9 r10 r11))
(define callee-save-for-alloc^ '(rsp rbp rbx r12 r13 r14 r15))

(define (free-vars^ arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [(Deref r i) (set r)]
    [(Global v) (set v)]
    [(Imm n) (set)]
    [else (error "free vars, unhandled" arg)]))

(define (write-vars^ instr)
  (match instr
    [(Instr 'movq (list s d)) (free-vars^ d)]
    [(Instr name arg*)
     (free-vars^ (last arg*))]
    [(JmpIf cc label) (set)]
    [(Jmp label) (set)]
    [(Callq f) (set)]
    [else (error "write-vars unmatched" instr)]))

(define (build-interference-instr^ live-after g locals)
  (λ (ast)
    (match ast
      [(or (Instr 'movq (list s d))
	   (Instr 'movzbq (list s d)))
       (for ([v live-after])
         (for ([d (free-vars^ d)])
           (cond [(equal? (Var v) s) (verbose "same source" s)]
                 [(equal? v d) (verbose "skip self edge on" d)]
                 [else (add-edge! g d v)])))
       ast]
      [(Callq f)
       (define vector-vars
	 (filter (lambda (x) (not (equal? x '()))) (for/list ([e locals]) (if (and (list? (cdr e)) (equal? 'Vector (car (cdr e)))) (car e) '()))))
       #;(define vector-vars
               (filter-map (λ (x) (and (list? (cdr x)) (list? (cadr x)) (eqv? 'Vector (caadr x)) (car x))) locals))
       (if (eqv? f 'collect)
           (for ([v live-after])
             (for ([u caller-save-for-alloc^])
               (if (equal? v u)
                   (verbose "skip self edge on" v)
                   (add-edge! g u v)))
             (for ([u callee-save-for-alloc^])
               (if (or (equal? v u) (not (member v vector-vars)))
                   (verbose "skip self edge or non-vector on" v)
                   (add-edge! g u v))))
           (for ([v live-after])
             (for ([u caller-save-for-alloc^])
               (if (equal? v u)
                   (verbose "skip self edge on" v)
                   (add-edge! g u v)))))
       ast]
      [else
       (for ([v live-after])
         (for ([d (write-vars^ ast)])
           (if (equal? v d)
               (verbose "skip self edge on" v)
               (add-edge! g d v))))
       ast])))

;;(filter (lambda (x) (not (equal? x '()))) (for/list ([e `((x . (Vector Integer Integer)) (y . (Vector Integer)) (z . Integer))]) (if (and (list? (cdr e)) (equal? 'Vector (car (cdr e)))) (car e) '())))                      
;;(filter-map (λ (x) (and (list? (cdr x)) (list? (cadr x)) (equal? 'Vector (caadr x)) (car x))) `((x . (Vector Integer Integer)) (y . (Vector Integer)) (z . Integer)))                 

(define (build-interference-block^ ast g locals)
  (match ast
    [(Block info ss)
     (let* ([lives info]
            [live-afters (cdr lives)]
            [new-ss (for/list ([inst ss] [live-after live-afters])
                      ((build-interference-instr^ live-after g locals) inst))]
            [new-info '()])
       (Block info ss))]))

(define (build-interference ast)
  (match ast
    [(Program info (CFG cfg))
     (let* ([locals (dict-ref info 'locals)]
            [g (undirected-graph '())])
       (for ([v locals]) (add-vertex! g v))
       (let* ([new-cfg (for/list ([(label block) (in-dict cfg)])
                         (cons label (build-interference-block^ block g locals)))]
              [new-info (dict-set info 'conflicts g)])
         (Program new-info (CFG new-cfg))))]))

;; allocate-registers

;; get-longest : [List] -> List
;; gets longest list in list of lists

(define (get-longest ls)
  (foldr (λ (e acc) (if (> (length e) (length acc)) e acc)) (car ls) (cdr ls)))

;; get-longest-val : [Hash Any List] -> List
;; get the longest value in hash

(define (get-longest-val hash)
  (let ([vals (hash-values hash)])
    (get-longest vals)))

;; choose-least : [Nat] Nat -> Nat
;; returns the smallest Nat not in the given set

(define (vector-type? locals v) 
  (match (dict-ref locals v)
	 [`(Vector ,ts ...)
	   #t]
	 [else 
	   #f]))

(define (choose-least satset cand locals v)
  (if (and (not (member cand satset)) 
	   (or (and (even? cand) 
		    (vector-type? locals v)) 
	       (and (odd? cand) 
		    (not (vector-type? locals v)))))
      cand
      (choose-least satset (add1 cand) locals v)
      ))

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





(define (color-graph ig hash locals)
  (if (hash-empty? hash)
      empty
      (let* ([maxsat (get-longest-val hash)]
             [maxsat-vert (hash-key hash maxsat)]
             [adj-verts (if (has-vertex? ig maxsat-vert)
                            (get-neighbors ig maxsat-vert)
                            '())]
             [col (choose-least maxsat 0 locals maxsat-vert)])
        (for-each (λ (vert) (if (and (hash-has-key? hash vert)
                                     (not (member col (hash-ref hash vert))))
                                (hash-set! hash vert
                                           (cons col (hash-ref hash vert)))
                                hash))
                      adj-verts)
        (hash-remove! hash maxsat-vert)
        (cons `(,maxsat-vert . ,col) (color-graph ig hash locals)))))

;; allocate-registers-exp : pseudo-x86 InterferenceGraph [Var] [Var . Home] -> pseudo-x86
;; takes in pseudo-x86 exp, intereference graph, and list of vars, returns
;; a pseudo-x86 exp with allocated registers according to color-graph

(define REGCOLS '((0 . rbx) (1 . rcx) (2 . rdx) (3 . rsi) (4 . rdi) (5 . r8) (6 . r9)
                            (7 . r10) #;(8 . r11) (8 . r12) (9 . r13) (10 . r14)))


(define spilled-root (mutable-set))
(define spilled-stack (mutable-set))

;; change sig to
;; allocate-registers-exp : pseudo-x86 [Var . Nat] -> pseudo-x86

(define (allocate-registers-exp e coloring locals)
    (match e
      [(Reg reg) (Reg reg)]
      [(Imm int) (Imm int)]
      [(Deref v i) (Deref v i)]
      [(Var v) (if (vector-type? locals v)
                  (let ([colnum (dict-ref coloring v)])
                    (if (<= colnum 10)
                        (Reg (dict-ref REGCOLS colnum))
                        (begin 
			  (let ([location (* 8 (add1 (quotient (- colnum 10) 2)))])
                          (set-add! spilled-root location)
                          (Deref 'r15 location)))))
                  (let ([colnum (dict-ref coloring v)])
                    (if (<= colnum 10)
                        (Reg (dict-ref REGCOLS colnum))
                        (begin
			  (let ([location (* -8 (quotient (- colnum 10) 2))])
                          (set-add! spilled-stack location)
                          (Deref 'rbp (- location 32)))))))]
      [(Instr 'addq (list e1 e2)) (Instr 'addq (list (allocate-registers-exp e1 coloring locals)
                                                     (allocate-registers-exp e2 coloring locals)))]
      [(Instr 'subq (list e1 e2)) (Instr 'subq (list (allocate-registers-exp e1 coloring locals)
                                                     (allocate-registers-exp e2 coloring locals)))]
      [(Instr 'movq (list e1 e2)) (Instr 'movq (list (allocate-registers-exp e1 coloring locals)
                                                     (allocate-registers-exp e2 coloring locals)))]
      [(Instr 'movzbq (list e1 e2)) (Instr 'movzbq (list (allocate-registers-exp e1 coloring locals)
                                                     (allocate-registers-exp e2 coloring locals)))]
      [(Instr 'cmpq (list e1 e2)) (Instr 'cmpq (list (allocate-registers-exp e1 coloring locals)
                                                     (allocate-registers-exp e2 coloring locals)))]
      [(Instr 'xorq (list e1 e2)) (Instr 'xorq (list (allocate-registers-exp e1 coloring locals)
                                                     (allocate-registers-exp e2 coloring locals)))]
      [(Instr 'set (list cc e)) (Instr 'set (list cc
                                                     (allocate-registers-exp e coloring locals)))]
      [(Instr 'negq (list e1)) (Instr 'negq (list (allocate-registers-exp e1 coloring locals)))]
      [(Callq l) (Callq l)]
      [(Retq) (Retq)]
      [(Global var) (Global var)]
      [(Instr 'pushq (list e1)) (Instr 'pushq (list (allocate-registers-exp e1 coloring locals)))]
      [(Instr 'popq (list e1)) (Instr 'popq (list (allocate-registers-exp e1 coloring locals)))]
      [(Jmp e1) (Jmp e1)]
      [(JmpIf cc label) (JmpIf cc label)]
      [(Block info es) (Block info (for/list ([e es]) (allocate-registers-exp e coloring locals)))]))

(define (allocate-registers p)
  (match p
    [(Program info (CFG es))
     (for ([vertex (get-vertices globalCFG)]) (remove-vertex! globalCFG vertex))
     (let* ([coloring (color-graph (dict-ref info 'conflicts)
                                  (make-hash (map (λ (a) `(,(car a) . ())) (dict-ref info 'locals))) (dict-ref info 'locals))]
	    [es^ (for/list ([ls es]) (cons (car ls)
                                           (allocate-registers-exp
                                            (cdr ls)
                                            coloring
                                            (dict-ref info 'locals))
                                           ))])
       (define s1 (set-count spilled-stack))
       (define s2 (set-count spilled-root)) 
       (set! spilled-root (mutable-set))
       (set! spilled-stack (mutable-set))
       (Program (list (cons 'stack-space (* 8 s1) #;(let ([f (* 8 (- (if (> (length coloring) 0)
                                                              (apply max (map (λ (assoc) (cdr assoc)) coloring))
                                                              0) 11))])
                                           (if (negative? f)
                                               0
                                               f #;(+ f (modulo f 16)))))
                      (cons 'num-spills `(,s1 . ,s2))
                )
                (CFG 
                 es^)))]))


(define tuples-and-gc-prog (Program '() (Prim 'vector-ref (list (Prim 'vector-ref (list (Prim 'vector (list (Prim 'vector (list (Int 42))))) (Int 0))) (Int 0)))))
#;(explicate-control (remove-complex-opera* (expose-allocation (uniquify (shrink (type-check-R3 tuples-and-gc-prog))))))

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
       [(list (Global name) (Deref a b)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                               (Instr op (list (Reg 'rax) e2)))]
       [(list (Deref a b) (Deref c d)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                             (Instr op (list (Reg 'rax) e2)))]
       [(list (Global name) (Global name1)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                                  (Instr op (list (Reg 'rax) e2)))]
       [(list (Deref a b) (Global name)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                               (Instr op (list (Reg 'rax) e2)))]
       [(list x y) (list (Instr op (list e1 e2)))])]
    [(Instr op (list e1)) (list (Instr op (list e1)))]
    [i (list i)]))

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

;;define x86prog (patch-instructions (assign-homes (select-instructions (explicate-control r1program-let)))))
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

(define (make-main stack-size root-spills)
  (let* ([push-bytes 32]
         [stack-adjust (- (align (+ push-bytes stack-size) 16) push-bytes)])
    (Block '()
           (append (list (Instr 'pushq (list (Reg 'rbp)))
                         (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                   (map (lambda (x) (Instr 'pushq (list x))) (list (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) #;(Reg 'r15))) 
                   (list (Instr 'subq (list (Imm stack-adjust) (Reg 'rsp)))) 
                   (initialize-garbage-collector root-spills)
                   (list (Jmp 'start))))))

(define (make-conclusion stack-size root-spills)
  (let* ([push-bytes 32]
         [stack-adjust (- (align (+ push-bytes stack-size) 16) push-bytes)])
    (Block '()
           (append (list (Instr 'subq (list (Imm (* 8 root-spills)) (Reg 'r15)))
                         (Instr 'addq (list (Imm stack-adjust) (Reg 'rsp))))
                   (map (lambda (x) (Instr 'popq (list x))) (list #;(Reg 'r15) (Reg 'r14) (Reg 'r13) (Reg 'r12) (Reg 'rbx))) 
                   (list (Instr 'popq (list (Reg 'rbp)))
                         (Retq))))))

(define root-stack-size 16384)
(define heap-size 16384)

(define (initialize-garbage-collector root-spills)
  (append (list (Instr 'movq (list (Imm root-stack-size) (Reg 'rdi)))
                (Instr 'movq (list (Imm heap-size) (Reg 'rsi)))
                (Callq 'initialize)
                (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
	  (for/list ([i root-spills]) (Instr 'movq (list (Imm 0) (Deref 'r15 (* i 8)))))
	  (list (Instr 'addq (list (Imm (* 8 root-spills)) (Reg 'r15))))))

(define (stringify-arg arg)
  (match arg
    [(Global name)
     (format "~a(%rip)" (label-name name))]
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
    [(Instr 'movzbq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "movzbq\t~a, ~a" st1 st2)]
    [(Instr 'xorq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "xorq\t~a, ~a" st1 st2)]
    [(Instr 'cmpq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "cmpq\t~a, ~a" st1 st2)]
    [(Instr 'set (list cc a1))
     (define st1 (stringify-arg a1))
     (format "set~a\t~a" cc st1)]
    [(Instr 'negq (list a))
     (define st (stringify-arg a))
     (format "negq\t~a" st)]
    [(Callq lbl)
     (format "callq\t~a" (label-name lbl))]
    [(Retq) "retq"]
    [(Instr 'pushq (list arg))
     (define st (stringify-arg arg))
     (format "pushq\t~a" st)]
    [(Instr 'popq (list arg))
     (define st (stringify-arg arg))
     (format "popq\t~a" st)]
    [(Jmp lbl)
     (format "jmp\t~a" (label-name lbl))]
    [(JmpIf cc lbl)
     (format "j~a \t~a" cc (label-name lbl))]))

;; format-x86 : [instr] -> string
(define (format-x86 ins)
  (foldr (λ (f r) (string-append "\t" f "\n" r)) "" (map stringify-in ins)))
     
     ;(format "~a:\n\t" label)

;; print-x86 : x86 -> string
(define (print-x86 p)
  (match p
    [(Program info (CFG es))
     (define new-es (cons (cons 'conclusion (make-conclusion (dict-ref info 'stack-space) (cdr (dict-ref info 'num-spills)))) 
			  (cons (cons 'main (make-main (dict-ref info 'stack-space) (cdr (dict-ref info 'num-spills)))) 
				es)))
     (format "~a"
             (foldr string-append ""
                    (for/list ([pair new-es])
                      (string-append (if (equal? (car pair) 'main) (format "\n\t.globl ~a\n~a" (label-name 'main) (label-name 'main)) (label-name (car pair))) ":\n" (format-x86 (Block-instr* (cdr pair))))))
             )]))

(define r2_58prog (Program '() (If (Prim '<= (list (Int 2) (Int 2))) (Int 42) (Int 0))))

#;(define testprinthw4 (print-x86
                      (patch-instructions
                       (allocate-registers
                        (build-interference
                         (uncover-live
                          (select-instructions
                           (uncover-locals
                            (explicate-control
                             (remove-complex-opera*
                              (expose-allocation
                               (uniquify
                                (shrink
                                 (type-check-R3 hw4prog))))))))))))))

;;(printf (print-x86 (patch-instructions (allocate-registers (build-interference (uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify (Program '() (Prim 'read (list)))))))))))))
;;(printf (print-x86 (patch-instructions (allocate-registers (build-interference (uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify ch3program))))))))))
;;Grant/Sam
