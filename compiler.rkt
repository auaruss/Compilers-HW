#lang racket
(require racket/set racket/stream)
(require graph)
(require racket/fixnum)
(require "interp-R0.rkt")
(require "interp-R1.rkt")
(require "interp-R5.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require "type-check-R6.rkt")
(provide (all-defined-out))
(require racket/dict)
(require racket/set)
(AST-output-syntax 'abstract-syntax)


(define globalCFG (directed-graph '()))
(define-vertex-property globalCFG instructions)
(define-vertex-property globalCFG live-before-set)
(define-vertex-property globalCFG function-label)

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

#|
(test-pe (parse-program `(program () (+ 10 (- (+ 5 3))))))
(test-pe (parse-program `(program () (+ 1 (+ 3 1)))))
(test-pe (parse-program `(program () (- (+ 3 (- 5))))))
|#


;;Type-Check Pass: R5 -> R5

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
	  (values (HasType (Prim op (list e1^)) 'Boolean) 'Boolean)]
	 ['procedure-arity 
          (define-values (e1^ Te1) (recur e1))
          (unless (and (list? Te1) (member '-> Te1))
            (error "argument to a boolean operator must be a boolean, not" Te1))
	  (values (HasType (Prim op (list e1^)) 'Integer) 'Integer)])]
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
      [(Lambda (and params (list `[,xs : ,Ts] ...)) rT body)
        (define-values (new-body bodyT)
	  ((type-check-exp (append (map cons xs Ts) env)) body))
	(define ty `(,@Ts -> ,rT))
	(cond
	  [(equal? rT bodyT)
	   (values (HasType (Lambda params rT new-body) ty) ty)]
	  [else
	    (error "mismatch in return type" bodyT rT)])] 
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
       (ProgramDefsExp '() ds^ body^)]
      [else (error 'type-check "R4/type-check unmatched ~a" e)])))

(define (type-check-R7 p)
  (match p
    [(Program info e)
     (define new-p (ProgramDefsExp info '() e))
     new-p]
    [(ProgramDefsExp info ds body)
     p]
    ))

(define (type-check-R5 p)
  (match p
    [(Program info e)
     (define new-p (ProgramDefsExp info '() e))
     ((type-check '()) new-p)]
    [(ProgramDefsExp info ds body)
     ((type-check '()) p)]
    ))

#;(define (type-check-R4 p)
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



;;Shrink Pass: R5 -> R5
(define (shrink-exp e)
  (match e
    [(Prim '- (list e1 e2)) 
     (Prim '+ (list (shrink-exp e1) (Prim '- (list (shrink-exp e2)))))]
    [(Prim 'and (list e1 e2)) 
     (If (shrink-exp e1) (If (shrink-exp e2) (shrink-exp e2) (Bool #f)) (Bool #f))]
    [(Prim 'or (list e1 e2))
     (If (shrink-exp e1) (shrink-exp e1) (If (shrink-exp e2) (shrink-exp e2)  (Bool #f)))]
    [(Prim '<= (list e1 e2))
     (Prim 'not (list (shrink-exp (Prim '> (list e1 e2)))))]
    [(Prim '> (list e1 e2))
     (let ([new-tmp (gensym 'tmp)]) 
       (Let new-tmp (shrink-exp e1) (Prim '< (list (shrink-exp e2) (Var new-tmp)))))]
    [(Prim '>= (list e1 e2)) 
     (Prim 'not (list (shrink-exp (Prim '< (list e1 e2)))))]
    [(Prim op (list e1))
     (Prim op (list (shrink-exp e1)))]
    [(Prim op (list e1 e2))
     (Prim op (list (shrink-exp e1) (shrink-exp e2)))]
    [(If e1 e2 e3)
     (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3))]
    [(Apply fs es)
     (define new-es (for/list ([e es]) (shrink-exp e)))
     (Apply (shrink-exp fs) new-es)]
    [(Let x e body)
     (Let (string->symbol (string-replace (symbol->string x) "-" "")) (shrink-exp e) (shrink-exp body))]
    [(Var f)
     (Var (string->symbol (string-replace (symbol->string f) "-" "")))]
    [(Lambda params rT body)
     (Lambda params rT (shrink-exp body))]
    [else e]
    ))

#;(define (shrink-exp e)
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
    [(HasType (Apply fs es) type)
     (define new-es (for/list ([e es]) (shrink-exp e)))
     (HasType (Apply (shrink-exp fs) new-es) type)]
    [(HasType (Let x e body) type)
     (HasType (Let (string->symbol (string-replace (symbol->string x) "-" "")) (shrink-exp e) (shrink-exp body)) type)]
    [(HasType (Var f) type) (HasType (Var (string->symbol (string-replace (symbol->string f) "-" ""))) type)]
    [(HasType (Lambda (and params (list `[,xs : ,Ts] ...)) rT body) type)
     (HasType (Lambda params rT (shrink-exp body)) type)]
    [else e]
    ))

(define (shrink p)
  (match p
    [(ProgramDefsExp info ds e)
     (define new-ds (for/list ([d ds]) (match d
                                         [(Def f paramtypes rt info body)
                                          (Def (string->symbol (string-replace (symbol->string f) "-" ""))
                                               paramtypes rt info (shrink-exp body))])))
     (ProgramDefs info (append new-ds (list (Def 'main '() 'Integer '() (shrink-exp e)))))]
    ))

(define r7_13 (parse-program '(program '()
                                       (+ 2 (or 40 0))
)))
#;(shrink (type-check-R7 r7_13))


;;Uniquify Pass: R4 -> R4
(define uniquify-exp
  (λ (symtab)
    (λ (exp)
      (match exp
        [(Void) (Void)]
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
        [(Apply e es)
         (define e^ ((uniquify-exp symtab) e))
         (define e* (for/list ([e (in-list es)])
                                   ((uniquify-exp symtab) e)))
         (Apply e^ e*)]
	[(Lambda params rT body)
         (define new-alist (for/list ([v params]) (cons v (gensym v))#;(match (car t)
                                      [v (cons v (gensym v))])))
         (define new-params (for/list ([v params]) (dict-ref new-alist v)#;(match t
                                      [`(,v : ,type)
                                       `(,(dict-ref new-alist v) : ,type)])))
         (define combined-alist (hash-union symtab (make-immutable-hash new-alist)))
	 (Lambda new-params rT ((uniquify-exp combined-alist) body))]
	[(HasType e t)
	 (HasType ((uniquify-exp symtab) e) t)]))))


(define init-symbol-table
  (λ ()
    (let ([init (make-immutable-hash)]) init)))

(define symbol-table-lookup
  (λ (symtab x)
    (if (empty? (hash-ref symtab x)) (error "variable not in scope") (hash-ref symtab x)#;(car (hash-ref symtab x)))))

(define extend-symbol-table
  (λ (symtab x new-x)
    (hash-set symtab
              x
              new-x
              #;(let [(not-found (λ () '()))]
                (cons new-x (hash-ref symtab x not-found))))))

;; uniquify : R'7 -> R'7
(define (uniquify p)
  (match p
    [(ProgramDefs info ds)
     (define new-alist (for/list ([d ds]) (match (Def-name d)
                                             ['main (cons 'main 'main)]
                                             [name (cons name (gensym name))])))
     (define new-ds (for/list ([d ds]) (match d
				         [(Def label paramtypes returntype info e)
                                          (define new-alist^ (for/list ([v paramtypes]) (cons v (gensym v))#;(match (car t)
                                                                                          [v (cons v (gensym v))])))
                                          (define new-paramtypes (for/list ([v paramtypes]) (dict-ref new-alist^ v)#;(match t
                                                                                              [`(,v : ,type)
                                                                                               `(,(dict-ref new-alist^ v) : ,type)])))
                                          (define combined-alist (append new-alist new-alist^))
					  (Def (dict-ref new-alist label) new-paramtypes returntype info ((uniquify-exp (make-immutable-hash combined-alist)) e))])))
     (ProgramDefs info new-ds)]
    ))

;; Reveal Functions : R'7 -> R'7
(define reveal-functions-exp
  (λ (functions alist)
    (λ (exp)
      (define recur (reveal-functions-exp functions alist))
      (match exp
        [(Void) (Void)]
        [(Var x)
         (if (set-member? functions x)
             (FunRefArity x (dict-ref alist x))
             (Var x))]
        [(Int n) (Int n)]
        [(Bool b) (Bool b)]
        [(Let x e body)
         (define recur-with-let-overshadowing (reveal-functions-exp (set-remove functions x) (dict-remove alist x)))
         (Let x
              (recur-with-let-overshadowing e)
              (recur-with-let-overshadowing body))]
        [(Apply f arg*) (Apply (recur f) (map recur arg*))]
        [(Prim op es) (Prim op (map recur es))]
        [(If e1 e2 e3) (If (recur e1) (recur e2) (recur e3))]
        [(Lambda params rT body)
         (Lambda params rT (recur body))]
        [(HasType e t) (HasType (recur e) t)]))))


(define reveal-functions 
  (λ (p)
    (match p
      [(ProgramDefs info defns)
       (define functions-in-env (list->set (map Def-name defns)))
       (define functions-alist (map (lambda (d) (cons (Def-name d) (length (Def-param* d)))) defns))
       (define revealed-definitions
          (for/list ([defn defns])
            (match defn
              [(Def label paramtypes returntype info e)
                (Def label paramtypes returntype info ((reveal-functions-exp functions-in-env functions-alist) e))])))
      (ProgramDefs info revealed-definitions)])))


;;Cast-Insert : R'7 -> R'6
(define new-op?
  (λ (op)
    (match op
      ['boolean? #t]
      ['integer? #t]
      ['vector? #t]
      ['procedure? #t]
      ['void? #t]
      [else #f])))
(define any-helper
  (λ (n)
    (if (eqv? n 0)
        '()
        (append '(Any) (any-helper (sub1 n))))))

(define cast-insert-exp
  (λ (e)
    (define recur cast-insert-exp)
    (match e
      [(Void) (Inject (Void) 'Void)]
      [(Var x) (Var x)]
      [(FunRefArity label arity) (Inject (FunRefArity label arity) (append (any-helper arity) '(-> Any)))]
      [(Int n)
       (Inject (Int n) 'Integer)]
      [(Bool b)
       (Inject (Bool b) 'Boolean)]
      [(Let x e body)
       (Let x (recur e) (recur body))]
      [(Apply f arg*)
       (define lambda-type (append (for/list ([a arg*]) 'Any) '(-> Any)))
       (define arg*^ (for/list ([a arg*]) (recur a)))
       (Apply (Project (recur f) lambda-type)
              arg*^)]
      [(Prim '+ (list e1 e2))
       (Inject (Prim '+ (list (Project (recur e1) 'Integer) (Project (recur e2) 'Integer))) 'Integer)]
      [(Prim '< (list e1 e2))
       (Inject (Prim '< (list (Project (recur e1) 'Integer) (Project (recur e2) 'Integer))) 'Boolean)]
      [(Prim 'read '())
       (Inject (Prim 'read '()) 'Integer)]
      [(Prim '- (list e1))
       (Inject (Prim '- (list (Project (recur e1) 'Integer))) 'Integer)]
      [(Prim 'eq? (list e1 e2))
       (Inject (Prim 'eq? (list (recur e1) (recur e2))) 'Boolean)]
      [(Prim 'not (list e1))
       (Inject (Prim 'not (list (Project (recur e1) 'Boolean))) 'Boolean)]
      [(Prim 'vector-length (list e1))
       (Inject (Prim 'vector-length (list (recur e1))) 'Integer)]
      [(Prim op (list e1))
       #:when (new-op? op)
       (Inject (Prim op (list (recur e1))) 'Boolean)]
      [(Prim 'vector es)
       (define es^ (for/list ([e es]) (recur e)))
       (Inject (Prim 'vector es^)
               (append '(Vector) (any-helper (length es))))]
      [(Prim 'vector-ref (list e1 e2))
       (define tmp1 (gensym 'tmp))
       (define tmp2 (gensym 'tmp))
       (Let tmp1 (Project (recur e1) '(Vectorof Any))
            (Let tmp2 (Project (recur e2) 'Integer)
                 (Prim 'vector-ref (list (Var tmp1) (Var tmp2)))))]
      [(Prim 'vector-set! (list e1 e2 e3))
       (define tmp1 (gensym 'tmp))
       (define tmp2 (gensym 'tmp))
       (Let tmp1 (Project (recur e1) '(Vectorof Any))
            (Let tmp2 (Project (recur e2) 'Integer)
                 (Prim 'vector-set! (list (Var tmp1) (Var tmp2) (recur e3)))))]
      [(If e1 e2 e3)
       (If (Prim 'eq? (list (recur e1) (Inject (Bool #f) 'Boolean)))
           (recur e3)
           (recur e2))]
      [(Lambda params rT body)
       (define params^ (for/list ([p params]) `[,p : Any]))
       (define body^ (recur body))
       (define lambda-type (append (for/list ([p params]) 'Any) '(-> Any)))
       (Inject
        (Lambda params^ 'Any body^)
        lambda-type)])))

(define cast-insert 
  (λ (p)
    (match p
      [(ProgramDefs info defns)
       (define cast-definitions
          (for/list ([defn defns])
            (match defn
              [(Def label paramtypes returntype info e)
               (define paramtypes^ (for/list ([p paramtypes]) `[,p : Any]))
               (Def label paramtypes^ returntype info (if (eqv? label 'main)
                                                          (Project (cast-insert-exp e) 'Integer)
                                                          (cast-insert-exp e)))])))
      (ProgramDefs info cast-definitions)])))

(define r7_3 (parse-program '(program () (define (id x) x)

                                      (id 42)
                                      )))
(define r7_7 (parse-program '(program () (define (hopefully-int) (lambda (x) (let ([maybe-int (read)])
                                                                               (if (eq? maybe-int 42) x
                                                                                   42))))
                                      (define (hopefully-bool) (lambda (x) (and (not x) #t)))
                                      (if (hopefully-bool) ((hopefully-int) 42)
                                          (+ ((hopefully-int) 42) 0))
                                      )))
(define r7_12 (parse-program '(program () (let ([f (lambda (x) x)])
                                             (if (eq? f f)
                                                 (- 45 3)
                                                 777))
                                       )))
(define r7_16 (parse-program '(program () (vector-ref (vector 42) 0)
                                       )))
(define r7_17 (parse-program '(program () (let ([x (if (eq? (read) 1) 0 #f)])
                                             (if (not x) 42 777))
                                       )))


;;Check-Bounds : R'6 -> R'6
(define check-bounds-R6-class
  (class type-check-R6-class
    (super-new)
    (inherit check-type-equal?)
    (define/override (type-check-exp env)
      (lambda (e)
        (define recur (type-check-exp env))
        (match e
          [(Prim 'vector-ref (list e1 ei))
           (define v (gensym 'v))
           (define i (gensym 'i))
           (define-values (e1^ e1-type) (recur e1))
           (define-values (ei^ ei-type) ((type-check-exp env #;(dict-set env v e1-type)) ei))
           (match e1-type
             [`(Vector ,ts ...)
              (values
               (Let v
                    e1^
                    (Let i
                         ei^
                         (If (cast-insert-exp (shrink-exp (Prim 'and (list (Prim '<= (list (Int 0) (Var i))) (Prim '< (list (Var i) (Prim 'vector-length (list (Var v)))))))))
                             (Prim 'vector-ref (list (Var v) (Var i)))
                             (Exit))))
               (list-ref ts (match ei
                              [(Int n) n])))]
             [`(Vectorof ,t)
              (values
               (Let v
                    e1^
                    (Let i
                         ei^
                         (If (cast-insert-exp (shrink-exp (Prim 'and (list (Prim '<= (list (Int 0) (Var i))) (Prim '< (list (Var i) (Prim 'vector-length (list (Var v)))))))))
                             (Prim 'vector-ref (list (Var v) (Var i)))
                             (Exit))))
               t)])]
          [(Prim 'vector-set! (list e-vec e-i e-arg))
           (define v (gensym 'v))
           (define i (gensym 'i))
           (define-values (e-vec^ e-vec-type) (recur e-vec))
           (define-values (e-i^ e-i-type) ((type-check-exp env #;(dict-set env v e-vec-type)) e-i))
           (define-values (e-arg^ e-arg-type) ((type-check-exp env #;(dict-set (dict-set env v e-vec-type) i e-i-type)) e-arg))
           (values
            (Let v
                 e-vec^
                 (Let i
                      e-i^
                      (If (cast-insert-exp (shrink-exp (Prim 'and (list (Prim '<= (list (Int 0) (Var i))) (Prim '< (list (Var i) (Prim 'vector-length (list (Var v)))))))))
                          (Prim 'vector-set! (list (Var v) (Var i) e-arg^))
                          (Exit))))
            'Void)]
          [(Prim 'vector args)
           (values (Prim 'vector args) (cons 'Vector (for/list ([arg args]) 'Any)))]
          [else ((super type-check-exp env) e)])))
    ))

(define (check-bounds p)
  (send (new check-bounds-R6-class) type-check-program p))


#;(check-bounds (cast-insert (reveal-functions (uniquify (shrink (type-check-R7 r7_16))))))


;;Reveal Casts : R'6 -> R'6
(define tagof
  (λ (ty)
    (match ty
      ['Integer 1]
      ['Boolean 4]
      [(cons 'Vector exps) 2]
      [(cons 'Vectorof exps) 2]
      [(cons x y) 3]
      ['Void 5])))

(define reveal-casts-exp
  (λ (e)
    (define recur reveal-casts-exp)
    (match e
      [(Void) (Void)]
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body)
       (Let x (recur e) (recur body))]
      [(FunRefArity label arity) (FunRefArity label arity)]
      [(Apply f arg*)
       (Apply (recur f) (map recur arg*))]
      [(Prim op (list e1))
       #:when (new-op? op)
       (define tmp (gensym 'tmp))
       (match op
         ['boolean?
          (Let tmp
               (recur e1)
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (tagof 'Boolean))))
                   (Bool #t)
                   (Bool #f)))]
         ['integer?
          (Let tmp
               (recur e1)
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (tagof 'Integer))))
                   (Bool #t)
                   (Bool #f)))]
         ['vector? (Let tmp
               (recur e1)
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (tagof '(Vector dummy)))))
                   (Bool #t)
                   (Bool #f)))]
         ['procedure? (Let tmp
               (recur e1)
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (tagof '(dummy1 -> dummy2)))))
                   (Bool #t)
                   (Bool #f)))]
         ['void? (Let tmp
               (recur e1)
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (tagof 'Void))))
                   (Bool #t)
                   (Bool #f)))])
       ]
      [(Prim op es)
       (Prim op (map recur es))]
      [(If e1 e2 e3)
       (If (recur e1) (recur e2) (recur e3))]
      [(Lambda params rT body)
       (Lambda params rT (recur body))]
      [(Project e^ ftype)
       (match ftype
         [`(,ptypes ... -> ,rT)
          (define e^^ (recur e^))
          (define tmp (gensym 'tmp))
             (Let tmp
                    e^^
                    (If (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                             (Int (tagof ftype))))
                            (Prim 'eq? (list (Prim 'procedure-arity (list (ValueOf (Var tmp) ftype)))
                                             (Int (length ptypes))))
                            (Bool #f))
                        (ValueOf (Var tmp) ftype)
                        (Exit)))]
         [`(Vector ,exps ...)
          (define e^^ (recur e^))
          (define tmp (gensym 'tmp))
             (Let tmp
                  e^^
                  (If (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                           (Int (tagof ftype))))
                          (Prim 'eq? (list (Prim 'procedure-arity (list (ValueOf (Var tmp) ftype)))
                                           (Int (length exps))))
                          (Bool #f))
                      (ValueOf (Var tmp) ftype)
                      (Exit)))]
         [else
          (define tmp (gensym 'tmp))
          (Let tmp
               (recur e^)
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (tagof ftype))))
                   (ValueOf (Var tmp) ftype)
                   (Exit)))])]
      [(Inject e^ ftype)
       (Prim 'make-any (list (recur e^) (Int (tagof ftype))))])))

(define reveal-casts 
  (λ (p)
    (match p
      [(ProgramDefs info defns)
       (define revealed-definitions
          (for/list ([defn defns])
            (match defn
              [(Def label paramtypes returntype info e)
               (Def label paramtypes returntype info (reveal-casts-exp e))])))
      (ProgramDefs info revealed-definitions)])))


#;(reveal-casts (check-bounds (cast-insert (reveal-functions (uniquify (shrink (type-check-R7 (parse-program '(program () 42)))))))))


;; Closure Conversion
(define convert-closure-type
  (lambda (type)
    (match type
      [`(,ts ... -> ,rt)
       (define ts^ (map convert-closure-type ts))
       (define rt^ (convert-closure-type rt))
       `(Vector ((Vector _) ,@ts^ -> ,rt^))]
      [`(Vector ,ts ...)
       `(Vector ,@(for/list ([t ts]) (convert-closure-type t)))]
      [else type])))

(define convert-to-closures-exp
  (λ (exp)
    (define recur convert-to-closures-exp)
    (match exp
      [(Var x) (values (Var x) '())]
      [(Void) (values (Void) '())]
      [(Exit) (values (Exit) '())]
      [(ValueOf e ftype)
       (values (ValueOf e ftype) '())]
      [(FunRefArity f n)
       (values (Closure n (list (FunRef f))) '())]
      #;[(HasType (FunRefArity f n) t)
       (define t^ (convert-closure-type t))
       (values (HasType (Closure n (list (HasType (FunRef f) '_))) t^) '())]
      [(Int n) (values (Int n) '())]
      [(Bool b) (values (Bool b) '())]
      [(Let x e body)
       (define-values (e^ e-deflist) (recur e))
       (define-values (body^ body-deflist) (recur body))
       (values 
        (Let x
             e^
             body^)
        (append e-deflist body-deflist))]
      [(Apply f arg*)
       (define tmp (gensym 'app))
       (define-values (f^ f-deflist) (recur f))
       (define-values (arg*^ arg*-deflist) (for/lists (arg*^ arg*-deflist) ([arg arg*]) (recur arg)))
       (values
        (Let tmp f^ (Apply (Prim 'vector-ref (list (Var tmp)
                                                   (Int 0)))
                           (cons (Var tmp) arg*^)))
        (append f-deflist (append* arg*-deflist)))]
      #;[(Apply f arg*)
       (define tmp (gensym 'app))
       (define-values (f^ f-deflist) (recur f))
       (define f^-type (match f^
                         [(HasType f^^ t)
                          t]))
       (define-values (arg*^ arg*-deflist) (for/lists (arg*^ arg*-deflist) ([arg arg*]) (recur arg)))
       (define rt^ (last (second f^-type)))
       (values
        (HasType (Let tmp f^ (HasType (Apply (HasType (Prim 'vector-ref (list (HasType (Var tmp) f^-type)
                                                                              (HasType (Int 0) 'Integer))) '_) ;; ?
                                             (cons (HasType (Var tmp) f^-type) arg*^)) rt^)) rt^) ;; ?
        (append f-deflist (append* arg*-deflist)))]
      [(Prim op es) 
       (define-values (es^ es-deflist) (for/lists (es^ es-deflist) ([e es]) (recur e)))
       (values
        (Prim op es^)
        (append* es-deflist))]
      [(If e1 e2 e3) 
       (define-values (es^ es-deflist) (for/lists (es^ es-deflist) ([e (list e1 e2 e3)]) (recur e)))
       (values
        (If (first es^) (second es^) (third es^))
        (append* es-deflist))]
      #;[(Lambda paramtypes returntype e)
       (define free-var-pairs
         (free-vars (foldr (λ (elem acc) (set-add acc (car elem))) (set) paramtypes)))
       (define-values (names alist) (for/lists (names alist) ([pr (set->list (free-var-pairs e))]) (values (car pr) pr)))
       (define lambda-name (gensym 'lambda))
       (define-values (e^ deflist) (recur e))
       (define clos (gensym 'fvs))
       (define vec-type `(Vector ,@(cons '_ (for/list ([name names]) (dict-ref alist name)))))
       (define i 0)
       (define rt^ (convert-closure-type returntype))
       (define lambda-def 
         (Def lambda-name 
              (cons `[,clos : ,vec-type] (for/list ([p paramtypes]) (match p
                                                                      [`[,x : ,type]
                                                                       `[,x : ,(convert-closure-type type)]])))
              rt^
              '()
              (foldl (lambda (name acc) (begin 
                                          (set! i (add1 i))
                                          (HasType (Let name (HasType (Prim 'vector-ref (list (HasType (Var clos) vec-type)
                                                                                              (HasType (Int i) 'Integer)))
                                                                      (dict-ref alist name)) acc)
                                                   (match e^
                                                     [(HasType x t) t])))) e^ names)))
       (values
        (Closure (length paramtypes) (cons (HasType (FunRef lambda-name) '_)
                                           (for/list ([name names]) (HasType (Var name) (dict-ref alist name)))))
        (cons lambda-def deflist))]
      [(Lambda paramtypes returntype e)
       (define free-var-pairs
         (free-vars (foldr (λ (elem acc) (set-add acc (car elem))) (set) paramtypes)))
       (define-values (names alist) (for/lists (names alist) ([pr (set->list (free-var-pairs e))]) (values (car pr) pr)))
       (define lambda-name (gensym 'lambda))
       (define-values (e^ deflist) (recur e))
       (define clos (gensym 'fvs))
       (define vec-type `(Vector ,@(cons '_ (for/list ([name names]) (dict-ref alist name)))))
       (define i 0)
       (define rt^ (convert-closure-type returntype))
       (define lambda-def 
         (Def lambda-name 
              (cons `[,clos : ,vec-type] (for/list ([p paramtypes]) (match p
                                                                      [`[,x : ,type]
                                                                       `[,x : ,(convert-closure-type type)]])))
              rt^
              '()
              (foldl (lambda (name acc)
                       (begin 
                         (set! i (add1 i))
                         (Let name
                              (Prim 'vector-ref (list (Var clos)
                                                      (Int i)))
                              acc)
                         )) e^ names)))
       (values
        (Closure (length paramtypes) (cons (FunRef lambda-name)
                                           (for/list ([name names]) (Var name) )))
        (cons lambda-def deflist))]
      [(HasType e t) 
       (define-values (e^ deflist) (recur e))
       (values
        (HasType e^ (convert-closure-type t))
        deflist)])))

(define free-vars
  (λ (bound-vars)
    (λ (exp)
      (define recur (free-vars bound-vars))
      (match exp
        [(Void) (set)]
        [(Var x)
         (if (set-member? bound-vars x) (set) (set (cons x 'Any)))]
        #;[(HasType (Var x) t)
         (if (set-member? bound-vars x) (set) (set (cons x (convert-closure-type t))))]
        [(FunRef f) (set)]
        [(FunRefArity f n) (set)]
        [(Exit) (set)]
        [(ValueOf e ftype)
         (recur e)]
        [(Int n) (set)]
        [(Bool b) (set)]
        [(Let x e body)
         (define recur-with-x-bound (free-vars (set-add bound-vars x)))
         (set-union (recur e) (recur-with-x-bound body))]
        [(Apply f arg*)
         (set-union (recur f) (foldr set-union (set) (map recur arg*)))]
        [(Prim op es) (foldr set-union (set) (map recur es))]
        [(If e1 e2 e3) (set-union (recur e1) (recur e2) (recur e3))]
        [(Lambda paramtypes returntype e)
         (define free-vars-in-this-lambda
           (free-vars (foldr (λ (elem acc) (set-add acc (car elem))) bound-vars paramtypes)))
         (free-vars-in-this-lambda e)]
        [(HasType e t) (recur e)]))))

(define convert-to-closures
  (λ (p)
    (match p
      [(ProgramDefs info defns)
       (define closure-converted-definitions
         (map (λ (defn)
                (match defn
                  [(Def label paramtypes returntype info e)
                   (define-values (e^ deflist) (convert-to-closures-exp e))
                   (define new-ptypes (for/list ([p paramtypes]) (match p
                                                                      [`[,name : ,type] `[,name : ,(convert-closure-type type)]])))
                   (append deflist (list (Def label (if (symbol=? label 'main) new-ptypes (cons `[,(gensym 'fvs) : _] new-ptypes)) (convert-closure-type returntype) info e^)))]))
              defns))
       (ProgramDefs info (append* closure-converted-definitions))])))

#;(convert-to-closures (reveal-functions (uniquify (shrink (type-check-R5 r5_01)))))


;; Limit Functions
(define limit-functions 
  (λ (p)
    (match p
      [(ProgramDefs info defns)
       (define vectorized-definitions (map vectorize-definition defns))
       (ProgramDefs info vectorized-definitions)])))

(define vectorize-definition
  (λ (d)
    (match d
      [(Def label paramtypes returntype info e)
       (if (> (length paramtypes) 6)
          (let ([vec (gensym 'vec)])  
            (Def label (append (take paramtypes 5)
                                (list `[,vec : 
                                       ,(cons 'Vector (map caddr (drop paramtypes 5)))]))
                  returntype info (vectorize-expression e (map car (drop paramtypes 5)) vec (cons 'Vector (map caddr (drop paramtypes 5))))))
            (Def label paramtypes returntype info (vectorize-expression2 e)))])))

(define vectorize-expression2
 (λ (e)
  (define recur (λ (_) (vectorize-expression2 _)))
  (define i 0)
  (match e
    [(Void) (Void)]
    [(Var x) (Var x)]
    [(Exit) (Exit)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x e body) (Let x (recur e) (recur body))]
    [(ValueOf e ftype)
     (ValueOf (recur e) ftype)]
    [(Apply f arg*)
     (if (> (length arg*) 6)
         (Apply (recur f) (append (map recur (take arg* 5)) (list (recur (Prim 'vector (drop arg* 5))))))
         (Apply (recur f) (map recur arg*)))]
    [(Prim op es) (Prim op (map recur es))]
    [(If e1 e2 e3) (If (recur e1) (recur e2) (recur e3))]
    [(FunRef x)
     (FunRef x)]
    #;[(HasType (FunRef x) t)
     (define new-t (if (list? t)
                       (match (take t (- (length t) 2))
                         [`(,ts ...)
                          (if (> (length ts) 6)
                              (append (take ts 5) (list `(Vector ,@(drop ts 5))) (drop t (- (length t) 2)))
                              t)])
                       t))
     (HasType (FunRef x) new-t)]
    [(Closure arity es)
     (Closure arity (map recur es))]
    [(HasType e t) (HasType (recur e) t)])))

(define vectorize-expression
 (λ (e vars vecsym vecsym-type)
  (define recur (λ (_) (vectorize-expression _ vars vecsym vecsym-type)))
  (define i 0)
  (define indexed-vars (map (λ (v) (begin (set! i (add1 i))
                                   (cons v (sub1 i)))) vars))
  (match e
    [(Void) (Void)]
    [(Var x)
     (let ([maybe-index (dict-ref indexed-vars x (λ () #f))])
      (if maybe-index
          (Prim 'vector-ref (list (Var vecsym) (Int maybe-index)))
          (Var x)))]
    #;[(Var x)
     (let ([maybe-index (dict-ref indexed-vars x (λ () #f))])
      (if maybe-index
          (Prim 'vector-ref (list (HasType (Var vecsym) vecsym-type) (HasType (Int maybe-index) 'Integer)))
          (Var x)))]
    [(FunRef x)
     (FunRef x)]
    #;[(HasType (FunRef x) t)
     (define new-t (match (take t (- (length t) 2))
                     [`(,ts ...)
                      (if (> (length ts) 6)
                          (append (take ts 5) (list `(Vector ,@(drop ts 5))) (drop t (- (length t) 2)))
                          t)]))
     (HasType (FunRef x) new-t)]
    [(Exit) (Exit)]
    [(ValueOf e ftype)
     (ValueOf (recur e) ftype)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x e body) (Let x (recur e) (recur body))]
    [(Apply f arg*)
     (if (> (length arg*) 6)
         (Apply (recur f) (append (map recur (take arg* 5)) (list (recur (Prim 'vector (drop arg* 5))))))
         (Apply (recur f) (map recur arg*)))]
    #;[(Apply f arg*)
     (define type-list (for/list ([e arg*])
                         (match e
                           [(HasType e^ t) t])))
     (if (> (length arg*) 6)
         (Apply (recur f) (append (map recur (take arg* 5)) (list (recur (HasType (Prim 'vector (drop arg* 5)) `(Vector ,@(drop type-list 5)))))))
         (Apply (recur f) (map recur arg*)))]
    [(Prim op es) (Prim op (map recur es))]
    [(If e1 e2 e3) (If (recur e1) (recur e2) (recur e3))]
    [(Closure arity es)
     (Closure arity (map recur es))]
    [(HasType e t) (HasType (recur e) t)])))

(define r4p02 (parse-program `(program '() (define (add8  [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer] [g : Integer] [h : Integer]) : Integer
   (+ a (+ b (+ c (+ d (+ e (+ f (+ g h))))))))
(add8 0 1 1 1 1 1 1 35)
)))


;;Expose Allocation: F1 -> F1 
(define (expose-allocation p)
  (match p
      [(ProgramDefs info ds)
       (define new-ds (for/list ([d ds]) (match d
                                           [(Def label paramtypes returntype info e)
                                            (Def label paramtypes returntype info ((expose-allocation-exp '()) e))])))
       (ProgramDefs info new-ds)]))

(define (expose-allocation-vec recur exps type clos-arity)
  (define i 0)
  (define bytes (* 8 (add1 (length exps))))
  (foldl
   (λ (elem acc)
     (let* ([x (string->symbol (string-append "x" (number->string i)))]
            [q (Let x (recur elem) acc)])
       (set! i (add1 i))
       q))
   (let ([q 
          (Let '_
               (If (Prim '< (list
                             (Prim '+ (list (GlobalValue 'free_ptr)
                                            (Int bytes)))
                             (GlobalValue 'fromspace_end)))
                   (Void)
                   (Collect bytes))
               (Let 'v
                    (if clos-arity
                        (AllocateClosure (length exps) type clos-arity)
                        (Allocate (length exps) type))
                    (foldl
                     (λ (elem acc)
                       (let* ([x (string->symbol (string-append "x" (number->string i)))]
                              [xtype (match type
                                         [`(Vector ((Vector _) ,ts ... -> ,rt))
                                          #;(unless (and (exact-nonnegative-integer? i) (< i (add1 (length ts))))
                                              (error 'expose-allocation-exp "invalid index ~a exps:~a type: ~a" i exps type))
                                          #;(list-ref (cons '(Vector _) (append ts (list rt))) i)
                                          (if (eqv? i 0)
                                              '(Vector _)
                                              'Any)
                                          #;(match (list-ref exps i)
                                            [(HasType exp^ t^) t^])]
                                         [`(Vector ,ts ...)
                                          (unless (and (exact-nonnegative-integer? i) (< i (length ts)))
                                            (error 'expose-allocation-exp "invalid index ~a for ~a" i ts))
                                          (list-ref ts i)]
                                         [else (error "expected a vector in vector-ref, not" type)])]
                              [q (Let '_
                                      (Prim
                                       'vector-set!
                                       (list (Var 'v)
                                             (Int i)
                                             (Var x)))
                                      acc)])
                         (set! i (add1 i))
                         q
                         ))
                     (begin
                       (set! i 0)
                       (Var 'v))
                     exps)))])
     (begin (set! i 0)
            q))
   exps))

#;(define (expose-allocation-vec recur exps type clos-arity)
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
                                          (HasType (Prim '+ (list (HasType (GlobalValue 'free_ptr) 'Integer)
                                                                  (HasType (Int bytes) 'Integer))) 'Integer)
                                          (HasType (GlobalValue 'fromspace_end) 'Integer))) 'Boolean)
                       (HasType (Void) 'Void)
                       (HasType (Collect bytes) 'Void)) 'Void)
                  (HasType
                   (Let 'v
                        (HasType (if clos-arity
                                     (AllocateClosure (length exps) type clos-arity)
                                     (Allocate (length exps) type)) type)
                        (HasType
                         (foldl
                          (λ (elem acc)
                            (let* ([x (string->symbol (string-append "x" (number->string i)))]
                                   [xtype (match type
                                            [`(Vector ((Vector _) ,ts ... -> ,rt))
                                             #;(unless (and (exact-nonnegative-integer? i) (< i (add1 (length ts))))
                                               (error 'expose-allocation-exp "invalid index ~a exps:~a type: ~a" i exps type))
                                             #;(list-ref (cons '(Vector _) (append ts (list rt))) i)
                                             (match (list-ref exps i)
                                               [(HasType exp^ t^) t^])]
                                            [`(Vector ,ts ...)
                                             (unless (and (exact-nonnegative-integer? i) (< i (length ts)))
                                               (error 'expose-allocation-exp "invalid index ~a for ~a" i ts))
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
   exps))

(define (expose-allocation-exp env)
  (λ (e)
    (define recur (expose-allocation-exp env))
    (match e
      [(Void) (Void)]
      [(Exit) (Exit)]
      [(FunRef f) (FunRef f)]
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x rhs body)
       (Let x (recur rhs) (recur body))]
      [(Prim 'vector-ref (list e^ int))
       (Prim 'vector-ref (list (recur e^) int))]
      [(Prim 'vector-set! (list exp1 int exp2))
       (Prim 'vector-set! (list (recur exp1) int (recur exp2)))]
      [(Prim 'vector exps)
       (expose-allocation-vec recur exps (cons 'Vector (for/list ([e exps]) 'Any)) #f)]
      [(Prim op es)
       (Prim op (map recur es))]
      [(If e1 e2 e3)
       (If (recur e1) (recur e2) (recur e3))]
      [(Apply f arg*) (Apply (recur f) (map recur arg*))]
      #;[(HasType (Prim 'vector exps) type)
       (expose-allocation-vec recur exps type #f)]
      [(Closure arity exps)
       (expose-allocation-vec recur exps `(Vector ,(append '((Vector _)) (cdr (for/list ([e exps]) 'Any)) '(-> Any))) arity)]
      #;[(HasType (Closure arity exps) type)
       (expose-allocation-vec recur exps type arity)]
      [(ValueOf e ftype)
       (ValueOf (recur e) ftype)]
      [(HasType e t)
       (HasType (recur e) t)])))

#;(expose-allocation (limit-functions (convert-to-closures (reveal-functions (uniquify (shrink (type-check-R5 r5_01)))))))

;; remove-complex-opera* : F1 -> F1
(define (remove-complex-opera* p)
    (match p
      [(ProgramDefs info ds)
       (define new-ds (for/list ([d ds]) (match d
                                           [(Def label paramtypes returntype info e)
                                            (Def label paramtypes returntype info (rco-exp e))])))
       (ProgramDefs info new-ds)]))

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
    [(Prim op es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ss `((,tmp . ,(Prim op new-es)))))]
    [(If e1 e2 e3)
     (define new-es
       (for/list ([e (list e1 e2 e3)]) (rco-exp e)))
     (define tmp (gensym 'tmp))
     (match new-es
	    [(list e1 e2 e3)
	     (values (Var tmp)
             `((,tmp . ,(If e1 e2 e3))))])]
    [(Collect n)
     (define tmp (gensym 'tmp))
     (values (Void)
             `((,tmp . ,(Collect n))))]
    [(GlobalValue name) 
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             `((,tmp . ,(GlobalValue name))))]
    [(Allocate n t)
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             `((,tmp . ,(Allocate n t))))]
    [(AllocateClosure n t ar)
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             `((,tmp . ,(AllocateClosure n t ar))))]
    [(FunRef name)
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             `((,tmp . ,(FunRef name))))]
    [(Exit)
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             `((,tmp . ,(Exit))))]
    [(ValueOf e ftype)
     (define-values (e^ ss)
       (rco-atom e))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ss `((,tmp . ,(ValueOf e^ ftype)))))]
    [(Apply f es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define-values (new-f ssf) (rco-atom f))
     (define ss (append* ssf sss))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ss `((,tmp . ,(Apply new-f new-es)))))]
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
    [(Exit) (Exit)]
    [(FunRef x) (FunRef x)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets^ (append* sss) (Prim op new-es))]
    [(ValueOf e ftype)
     (define-values (e^ ss)
       (rco-atom e))
     (make-lets^ ss (ValueOf e^ ftype))]
    [(Apply f es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define-values (new-f f-ss) (rco-atom f))
     (make-lets^ (append (append* sss) f-ss) (Apply new-f new-es))]
    [(If e1 e2 e3)
     (define new-es
       (for/list ([e (list e1 e2 e3)]) (rco-exp e)))
     (match new-es
	    [(list e1 e2 e3)
	     (If e1 e2 e3)])]
    [(Collect n) (Collect n)]
    [(GlobalValue name) (GlobalValue name)]
    [(Allocate n t) (Allocate n t)]
    [(AllocateClosure n t ar) (AllocateClosure n t ar)]
    [(HasType e t)
     (HasType (rco-exp e) t)]
    ))



; explicate-tail : R'6 -> C5Tail x [Var]
; takes in R'6 expression and produces C5 Tail and list of let-bound variables
(define (explicate-tail e funlabel)
  (match e
    [(Exit)
     (values (Exit) '())]
    [(Int n)
     (values (Return (Int n)) '())]
    [(Bool b)
     (values (Return (Bool b)) '())]
    [(FunRef l)
     (values (Return (FunRef l)) '())]
    [(Prim 'read '())
     (values (Return (Prim 'read '())) '())]
    [(ValueOf e ftype)
     (values (Return (ValueOf e ftype)) '())]
    [(Prim op ls)
     (values (Return (Prim op ls)) '())]
    [(Apply f es)
     (values (TailCall f es) '())]
    [(Var x)
     (values (Return (Var x)) '())]
    [(Let x e body) 
     (define-values (c1tail let-binds) (explicate-tail body funlabel))
     (define-values (c1tail^ let-binds^) (explicate-assign e (Var x) c1tail funlabel)) ;; why var here
     (values c1tail^ (cons x (append let-binds let-binds^)))]
    [(If e1 e2 e3)
     (define-values (c1tail-then let-binds-then) (explicate-tail e2 funlabel))
     (define-values (c1tail-else let-binds-else) (explicate-tail e3 funlabel))  
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else funlabel))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new))
     ]
    [(HasType e t)
     (explicate-tail e funlabel)
     ]
    ))


; explicate-assign : R4 Var C3Tail -> C3Tail x [Var]
; takes in R4 expression, the variable where it will be assigned, and a C3Tail that comes
; after the assignment. Returns a C3Tail and list of variables

;; simplify

(define (explicate-assign e v c funlabel)
  (match e
    [(Exit)
     (values (Exit) '())
     #;(values (Seq (Assign v (Exit)) c) '())]
    [(Void)
     (values (Seq (Assign v (Void)) c) '())]
    [(Collect n)
     (values (Seq (Collect n) c) '())]
    [(Allocate n t)
     (values (Seq (Assign v (Allocate n t)) c) '())]
    [(AllocateClosure n t arity)
     (values (Seq (Assign v (AllocateClosure n t arity)) c) '())]
    [(GlobalValue name)
     (values (Seq (Assign v (GlobalValue name)) c) '())]
    [(Int n)
     (values (Seq (Assign v (Int n)) c) '())]
    [(Bool b)
     (values (Seq (Assign v (Bool b)) c) '())]
    [(FunRef l)
     (values (Seq (Assign v (FunRef l)) c) '())]
    [(Prim op ls)
     (values (Seq (Assign v (Prim op ls)) c)
             '())]
    [(ValueOf e ftype)
     (values (Seq (Assign v (ValueOf e ftype)) c)
             '())]
    [(Apply f es)
     (values (Seq (Assign v (Call f es)) c)
             '())]
    [(Var x)
     (values (Seq (Assign v (Var x)) c) '())]
    [(Let x e body) 
     (define-values (c1tail let-binds) (explicate-assign body v c funlabel))
     (define-values (c1tail^ let-binds^) (explicate-assign e (Var x) c1tail funlabel))
     (values c1tail^ (cons x (append let-binds let-binds^)))]
    [(If e1 e2 e3)
     (define label (gensym 'block))
     (add-vertex! globalCFG label)
     (instructions-set! label c)
     (live-before-set-set! label (list->set '()))
     (function-label-set! label funlabel)
     (define-values (c1tail-then let-binds-then) (explicate-assign e2 v (Goto label) funlabel))
     (define-values (c1tail-else let-binds-else) (explicate-assign e3 v (Goto label) funlabel))
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else funlabel))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new))
     ]
    [(HasType e t)
     (define-values (c1tail let-binds) (explicate-assign e v c funlabel))
     (match c1tail
      [(Seq (Assign v e^) tail)
       (values (Seq (Assign v (HasType e^ t)) tail) let-binds)]
      [else
       (values c1tail let-binds)])
     ]
    ))

;; explicate-pred : R4_exp x C3_tail x C3_tail -> C3_tail x var list
(define (explicate-pred e c1 c2 funlabel)
  (match e
    [(Bool b)
     (values (if b c1 c2) '())]
    [(Var v)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (function-label-set! label1 funlabel)
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (function-label-set! label2 funlabel)
     (values (IfStmt (Prim 'eq? (list e (Bool #t))) (Goto label1) (Goto label2))
             '())]
    [(Prim op ls)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (function-label-set! label1 funlabel)
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (function-label-set! label2 funlabel)
     (values (IfStmt e (Goto label1) (Goto label2))
             '())]
    [(ValueOf e^ ftype)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (function-label-set! label1 funlabel)
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (function-label-set! label2 funlabel)
     (values (IfStmt e (Goto label1) (Goto label2))
             '())]
    [(Apply f es)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (function-label-set! label1 funlabel)
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (function-label-set! label2 funlabel)
     (values (IfStmt (Call f es) (Goto label1) (Goto label2))
             '())]
    [(Let x e body)
     (define-values (body-block body-lets) (explicate-pred body c1 c2 funlabel))
     (define-values (result result-lets) (explicate-assign e (Var x) body-block funlabel))
     (values result (append body-lets result-lets))
     ]
    [(If e1 e2 e3)
     (define label1 (gensym 'block))
     (define label2 (gensym 'block))
     (add-vertex! globalCFG label1)
     (instructions-set! label1 c1)
     (live-before-set-set! label1 (list->set '()))
     (function-label-set! label1 funlabel)
     (add-vertex! globalCFG label2)
     (instructions-set! label2 c2)
     (live-before-set-set! label2 (list->set '()))
     (function-label-set! label2 funlabel)
     (define-values (c1tail-then let-binds-then) (explicate-pred e2 (Goto label1) (Goto label2) funlabel))
     (define-values (c1tail-else let-binds-else) (explicate-pred e3 (Goto label1) (Goto label2) funlabel))
     (define-values (c1tail-new let-binds-new) (explicate-pred e1 c1tail-then c1tail-else funlabel))
     (values c1tail-new (append let-binds-then let-binds-else let-binds-new)) ]
    [(HasType e t)
     (explicate-pred e c1 c2 funlabel)]
     ))

;; explicate-control : R4 -> C3
(define (explicate-control p)
  (match p
    [(ProgramDefs info ds)
     (define localvars '())
     (define new-ds (for/list ([d ds]) (match d
                                         [(Def label paramtypes returntype info e)
                                          (define new-label (string->symbol (string-append (symbol->string label) "start")))
                                          (define-values (c3t let-binds) (explicate-tail e label))
                                          (add-vertex! globalCFG new-label)
                                          (instructions-set! new-label c3t)
                                          (live-before-set-set! new-label (set))
                                          (function-label-set! new-label label)
                                          (set! localvars (append localvars let-binds))
                                          (define def-alist (filter (λ (v) (not (equal? v '()))) (for/list ([l (get-vertices globalCFG)]) (if (equal? label (function-label l))
                                                                                                                                              (cons l (instructions l))
                                                                                                                                              '()))))
                                          (Def label paramtypes returntype info def-alist)
                                          ])))
     (ProgramDefs (cons (cons 'locals localvars) info) new-ds)]))




;;uncover-locals-helper : C3 list of blocks -> association list of locals and their types
(define (uncover-locals-tail e)
  (match e
    [(Assign (Var v) (HasType e t))
     (list (cons v t))]
    [(Seq s t)
     (append (uncover-locals-tail s) (uncover-locals-tail t))]
    [(TailCall f es)
     (filter (λ (v) (not (equal? v '()))) (for/list ([e es]) (match e
                          [(HasType (Var v) t)
                           (cons v t)]
                          [else '()])))]
    [_ (list)])
  )

(define (uncover-locals-helper es)
  (append* (for/list ([l es])
		     (uncover-locals-tail (cdr l)))))

;; uncover-locals : C3 -> C3
(define (uncover-locals p)
  (match p
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (match d
                                     [(Def label paramtypes returntype info def-alist)
                                      (define paramvars (for/list ([param paramtypes]) (match param
                                                                       [`(,v : ,t)
                                                                        (cons v t)])))
                                      (Def label paramtypes returntype (dict-set info 'locals (append paramvars (uncover-locals-helper def-alist))) def-alist)])))
     (define new-locals (append* (for/list ([d new-ds]) (match d
                                     [(Def label paramtypes returntype info def-alist)
                                      (dict-ref info 'locals)]))))         
     (ProgramDefs (dict-set info 'locals new-locals #;(append paramvars (uncover-locals-helper es))) new-ds)]))

#;(uncover-locals (explicate-control (remove-complex-opera* (expose-allocation (limit-functions (reveal-functions (uniquify (shrink (type-check-R4 r4p02)))))))))

; atm? : c0exp -> bool

#;(define (atm? c0exp)
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
      [#f (Imm 0)])]
    [(Void)
     (Imm 0)]))

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
(define (calculate-tag len T arity)
  (if arity
      (let* ([type-arity (arithmetic-shift arity 57)]
             [type-num (arithmetic-shift (list->number (reverse (type->binary (cdr T)))) 7)]
             [type-len (bitwise-ior (arithmetic-shift len 1) 1)]
             [res (bitwise-ior type-arity type-num type-len)])
        res)
      (let* ([type-num (arithmetic-shift (list->number (reverse (type->binary (cdr T)))) 7)]
             [type-len (bitwise-ior (arithmetic-shift len 1) 1)]
             [res (bitwise-ior type-num type-len)])
        res)))

;; argument registers in order:
(define ARGREGS '(rdi rsi rdx rcx r8 r9))


;; assign-arg-regs : [C3Atm] -> [x86Instr]
;; takes in a list of c3 args and returns a list of instructions that move
;; said args into the correct registers

(define (assign-arg-regs args curr)
  (if (empty? args)
      empty
      (cons (Instr 'movq (list (sel-ins-atm (car args))
                               (Reg (list-ref ARGREGS curr))))
            (assign-arg-regs (cdr args) (add1 curr)))))

(define (assign-regs-args args curr)
  (if (empty? args)
      empty
      (cons (Instr 'movq (list (Reg (list-ref ARGREGS curr))
                               (sel-ins-atm (car args))))
            (assign-regs-args (cdr args) (add1 curr)))))



(define (sel-ins-stmt c0stmt)
  (match c0stmt
    [(HasType stmt type) (sel-ins-stmt stmt)]
    [(Collect n) (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
                       (Instr 'movq (list (Imm n) (Reg 'rsi)))
                       (Callq 'collect 2))]
    [(Assign v e)
     (if (atm? e)
         (list (Instr 'movq (list (sel-ins-atm e) v)))
         (match e
           [(Prim 'make-any (list e (Int tag)))
            (if (or (= tag 1)
                    (= tag 4))
                (list (Instr 'movq (list (sel-ins-atm e) v))
                      (Instr 'salq (list (Imm 3) v))
                      (Instr 'orq (list (Imm tag) v)))
                (list (Instr 'movq (list (sel-ins-atm e) v))
                      (Instr 'orq (list (Imm tag) v))))]
           [(Prim 'tag-of-any (list e))
            (list (Instr 'movq (list (sel-ins-atm e) v))
                  (Instr 'andq (list (Imm 7) v)))]
           [(ValueOf e ty)
            (if (or (eq? ty 'Integer)
                    (eq? ty 'Boolean))
                (list (Instr 'movq (list (sel-ins-atm e) v)) 
                      (Instr 'sarq (list (Imm 3) v)))
                (list (Instr 'movq (list (Imm -8) v))
                      (Instr 'andq (list (sel-ins-atm e) v))))] 
           [(Prim 'vector-length (list e))
            (list (Instr 'movq (list (sel-ins-atm e) (Reg 'r11))) 
                  (Instr 'movq (list (Deref 'r11 0) (Reg 'r11)))
                  (Instr 'andq (list (Imm 126) (Reg 'r11)))
                  (Instr 'sarq (list (Imm 1) (Reg 'r11)))
                  (Instr 'movq (list (Reg 'r11) v)))]
           [(FunRef lbl) (list (Instr 'leaq (list (FunRef lbl) v)))]
           [(Call fun args) (append (assign-arg-regs args 0)
                                    (list (IndirectCallq (sel-ins-atm fun) (length args)) 
                                          (Instr 'movq (list (Reg 'rax) v))))]
           [(HasType e^ t) (sel-ins-stmt (Assign v e^))]
           [(Allocate len T)
            (let ([tag (calculate-tag len T #f)]) 
              (list (Instr 'movq (list (Global 'free_ptr) v))
                    (Instr 'addq (list (Imm (* 8 (add1 len))) (Global 'free_ptr)))
                    (Instr 'movq (list v (Reg 'r11)))
                    (Instr 'movq (list (Imm tag) (Deref 'r11 0)))))]
           [(AllocateClosure len T arity)
            (let ([tag (calculate-tag len T arity)]) 
              (list (Instr 'movq (list (Global 'free_ptr) v))
                    (Instr 'addq (list (Imm (* 8 (add1 len))) (Global 'free_ptr)))
                    (Instr 'movq (list v (Reg 'r11)))
                    (Instr 'movq (list (Imm tag) (Deref 'r11 0)))))]
           [(Prim 'procedure-arity (list f)) (list (Instr 'movq (list (sel-ins-atm f) (Reg 'r11)))
                                                   (Instr 'movq (list (Deref 'r11 0) v))
                                                   (Instr 'sarq (list (Imm 57) v)))]
           [(Prim 'vector-ref (list vec ind-exp))
            (list (Instr 'movq (list (sel-ins-atm ind-exp) (Reg 'r11)))
                  (Instr 'addq (list (Imm 1) (Reg 'r11)))
                  (Instr 'imulq (list (Imm 8) (Reg 'r11)))
                  (Instr 'addq (list (sel-ins-atm vec) (Reg 'r11)))
                  (Instr 'movq (list (Deref 'r11 0) v)))]
           #;[(Prim 'vector-ref (list atm (HasType (Int n) t)))
            (list (Instr 'movq (list (sel-ins-atm atm) (Reg 'r11))) 
                  (Instr 'movq (list (Deref 'r11 (* 8 (add1 n))) v)))]
           [(Prim 'vector-set! (list atm1 ind-exp atm2))
            (list (Instr 'movq (list (sel-ins-atm ind-exp) (Reg 'r11)))
                  (Instr 'addq (list (Imm 1) (Reg 'r11)))
                  (Instr 'imulq (list (Imm 8) (Reg 'r11)))
                  (Instr 'addq (list (sel-ins-atm atm1) (Reg 'r11)))
                  (Instr 'movq (list (sel-ins-atm atm2) (Deref 'r11 0)))
                  (Instr 'movq (list (Imm 0) v)))]
           #;[(Prim 'vector-set! (list atm1 (HasType (Int n) t) atm2))
            (list (Instr 'movq (list (sel-ins-atm atm1) (Reg 'r11)))
                  (Instr 'movq (list (sel-ins-atm atm2) (Deref 'r11 (* 8 (add1 n)))))
                  (Instr 'movq (list (Imm 0) v)))]
           [(GlobalValue name) (list (Instr 'movq (list (Global name) v)))] 
           [(Void) (list (Instr 'movq (list (Imm 0) v)))]
           [(Prim 'read '())
            (list (Callq 'read_int 0)
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
               (Instr 'set (list 'e (ByteReg 'al)))
               (Instr 'movzbq (list (ByteReg 'al) v_))))]
           [(Prim '< (list atm1 atm2))
           (let ([atm1_ (sel-ins-atm atm1)]
                  [atm2_ (sel-ins-atm atm2)]
                  [v_ (sel-ins-atm v)])
              (list
               (Instr 'cmpq (list atm2_ atm1_))
               (Instr 'set (list 'l (ByteReg 'al)))
               (Instr 'movzbq (list (ByteReg 'al) v_))))]))]))

; sel-ins-tail : C1tail -> pseudo-x86
; takes in a c1 tail and converts it ot pseudo-x86

(define (sel-ins-tail c0t name)
  (match c0t
    [(Exit) (list (Instr 'movq (list (Imm -1) (Reg 'rdi)))
                  (Callq 'exit 0))]
    [(TailCall fun args) (append (assign-arg-regs args 0)
                                 (list (TailJmp (sel-ins-atm fun) (length args))))]
    [(HasType tail type) (sel-ins-tail tail name)]
    [(Return e)
     (let ([conc (string->symbol (string-append (symbol->string name) "conclusion"))])
       (append (sel-ins-stmt (Assign (Reg 'rax) e))
               (list (Jmp conc))))]
    [(Seq stmt tail)
     (define x86stmt (sel-ins-stmt stmt))
     (define x86tail (sel-ins-tail tail name))
     (append x86stmt x86tail)]
    [(Goto label)
     (list (Jmp label)) ]
    [(IfStmt (Prim 'vector-ref (list v ind-exp)) (Goto label1) (Goto label2))
     (let ([v_ (sel-ins-atm v)])
       (list
        (Instr 'movq (list (sel-ins-atm ind-exp) (Reg 'r11)))
        (Instr 'addq (list (Imm 1) (Reg 'r11)))
        (Instr 'imulq (list (Imm 8) (Reg 'r11)))
        (Instr 'addq (list v_ (Reg 'r11)))
        (Instr 'cmpq (list (Imm 1) (Deref 'r11 0)))
        (JmpIf 'e label1)
        (Jmp label2)))]
    #;[(IfStmt (Prim 'vector-ref (list v (HasType (Int i) 'Integer))) (Goto label1) (Goto label2))
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
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds])
                      (match d
                        [(Def label paramtypes returntype info alist)
                         (define args (for/list ([param paramtypes])
                                        (match param
                                          [`(,v : ,t)
                                           (Var v)])))
                         (define new-alist (for/list ([p alist])
                                             (cons (car p) (Block '() (if (equal? (car p) (string->symbol (string-append (symbol->string label) "start")))
									  (append (assign-regs-args args 0) (sel-ins-tail (cdr p) label))
									  (sel-ins-tail (cdr p) label))))))
                         (Def label '() returntype
                              (dict-set info 'num-params (length paramtypes))
                              new-alist)])))
     (ProgramDefs info new-ds)]))


#;(select-instructions (explicate-control (remove-complex-opera* (expose-allocation (limit-functions (reveal-casts (cast-insert (reveal-functions (uniquify (shrink (type-check-R7 r7_16)))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;  Assignment 2 Work (Replaces assign-homes)    ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-live
(define (add-global-CFG-edges label1 instr-ls conclusions)
  (match instr-ls
    ['() '()] ;;does nothing, just ends the function
    [ls 
      (match (car ls)
	[(JmpIf cc label2) (add-directed-edge! globalCFG label1 label2) (add-global-CFG-edges label1 (cdr ls) conclusions)]
        [(Jmp label2) (if (not (member label2 conclusions))
                          (begin
                            (add-directed-edge! globalCFG label1 label2)
                            (add-global-CFG-edges label1 (cdr ls) conclusions))
                         (add-global-CFG-edges label1 (cdr ls) conclusions) )]
        [_ (add-global-CFG-edges label1 (cdr ls) conclusions)])]))

; reg-sym? : Symbol -> Bool
; returns true iff the given symbol is a register name that can be in interference graph

(define (reg-sym? sym)
  (or (symbol=? sym 'rbp)
      (symbol=? sym 'rsp)
      (symbol=? sym 'al)
      (symbol=? sym 'rax)
      (symbol=? sym 'r11)
      (symbol=? sym 'r15)
      (symbol=? sym 'rbx)
      (symbol=? sym 'rcx)
      (symbol=? sym 'rdx)
      (symbol=? sym 'rsi)
      (symbol=? sym 'rdi)
      (symbol=? sym 'r8)
      (symbol=? sym 'r9)
      (symbol=? sym 'r10)
      (symbol=? sym 'r12)
      (symbol=? sym 'r13)
      (symbol=? sym 'r14)))

;; turn association list of blocks in CFG into graph
;; then reverse topo sort said graph, uncover-live that sorted list

(define (instr-arg-varset arg)
  (match arg 
	 [(Var v) (set v)]
         [(Reg r) (if (and (reg-sym? r)
                           (not (symbol=? r 'rax))
                           (not (symbol=? r 'r11))
                           (not (symbol=? r 'rbp))
                           (not (symbol=? r 'rsp))
                           (not (symbol=? r 'al))
                           (not (symbol=? r 'r15)))
                      (set r)
                      (set))]
	 [_ (list->set '())]))

(define (instr-read-varset instr) 
  (match instr
    [(Instr 'set (list e1 e2))
     (list->set '())]
    [(Instr 'movzbq (list e1 e2))
     (list->set '())]
    [(Instr 'movq (list e1 e2))
     (instr-arg-varset e1)]
    [(Instr 'leaq (list e1 e2))
     (instr-arg-varset e1)]
    [(Instr op (list e1 e2))
     (set-union (instr-arg-varset e1) (instr-arg-varset e2))]
    [(Instr 'negq (list e1))
     (instr-arg-varset e1)]
    [(Callq label arity)
     (set 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10
          'rbx  'r12 'r13 'r14)]
    [(IndirectCallq e1 arity)
     (set-union (set 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10
                     'rbx  'r12 'r13 'r14) (instr-arg-varset e1))]
    [(TailJmp e1 arity)
     (set-union (set 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10
                     'rbx  'r12 'r13 'r14) (instr-arg-varset e1))]
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
    [(null? instr-ls) (live-before-set-set! label live-after-set) (list live-after-set)]
    [else (let ([new-live-after-set (set-union (set-subtract live-after-set (instr-written-varset (car instr-ls))) (instr-read-varset (car instr-ls)))]) 
            (append (uncover-live-helper (cdr instr-ls) new-live-after-set label) (list live-after-set)))]
    ))

(define (get-first-live ls)
  (match ls
    ['() (list->set '())]
    [else (set-union (live-before-set (car ls)) (get-first-live (cdr ls)))]))

(define (find-instructions label es)
  (if (eq? label (car (car es))) 
      (match (cdr (car es))
        [(Block b-info ls) ls])
      (find-instructions label (cdr es))))

(define (sort-blocks ordered-vertices es)
  (for/list ([label ordered-vertices]) 
	    (define first-live-after-set (get-first-live (get-neighbors globalCFG label)))
	    (cons label (Block (uncover-live-helper (reverse (find-instructions label es)) first-live-after-set label) (find-instructions label es)))))

(define (uncover-live p)
  (match p
    [(ProgramDefs info ds)
     (define es (append* (for/list ([d ds]) (match d
                                     [(Def label paramtypes rt info ls)
                                      ls]))))
     (define conclusions (for/list ([d ds]) (match d
                                     [(Def label paramtypes rt info ls)
                                      (string->symbol (string-append (symbol->string label) "conclusion"))])))
     (for ([ls es]) (add-global-CFG-edges (car ls) (match (cdr ls)
							       [(Block b-info instr-ls) instr-ls]) conclusions))
     (define new-blocklist (sort-blocks (tsort (transpose globalCFG)) es))
     (for ([vertex (get-vertices globalCFG)]) (remove-vertex! globalCFG vertex))
     (define new-ds (for/list ([d ds]) (match d
                                         [(Def label paramtypes rt info ls)
                                          (Def label paramtypes rt info (filter (λ (v) (not (equal? v '()))) (for/list ([pr new-blocklist]) (if (equal? (function-label (car pr)) label)
                                                                                                                                                pr
                                                                                                                                                '()))))])))
     (ProgramDefs info new-ds)]))

#;(uncover-live (select-instructions (uncover-locals (explicate-control (remove-complex-opera* (expose-allocation (limit-functions (reveal-functions (uniquify (shrink (type-check-R4 jeremytest)))))))))))

;; build-interference

(define caller-save-for-alloc^ '(al rax rdx rcx rsi rdi r8 r9 r10 r11))
(define callee-save-for-alloc^ '(rsp rbp rbx r12 r13 r14 r15))

(define (free-vars^ arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [(Deref r i) (set r)]
    [(Global v) (set)]
    [(Imm n) (set)]
    [(ByteReg r) (set r)]
    [else (error "free vars, unhandled" arg)]))

(define (write-vars^ instr)
  (match instr
    [(Instr 'movq (list s d)) (free-vars^ d)]
    [(Instr name arg*)
     (free-vars^ (last arg*))]
    [(JmpIf cc label) (set)]
    [(Jmp label) (set)]
    [(Callq f arity) (set)]
    [(TailJmp arg arity) (set)]
    [(IndirectCallq arg arity) (set)]
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
      [(or (IndirectCallq f arity) (Callq f arity))
       (define vector-vars
         (filter (lambda (x) (not (equal? x '())))
                 (for/list ([e locals]) (if (and (list? (cdr e))
                                                 (equal? 'Vector (car (cdr e)))) (car e) '()))))
       #;(define vector-vars
           (filter-map (λ (x) (and (list? (cdr x)) (list? (cadr x)) (eqv? 'Vector (caadr x)) (car x))) locals))
       (for ([v live-after])
         (for ([u caller-save-for-alloc^])
           (if (equal? v u)
               (verbose "skip self edge on" v)
               (add-edge! g u v)))
         (for ([u callee-save-for-alloc^])
           (if (or (equal? v u) (not (member v vector-vars)))
               (verbose "skip self edge or non-vector on" v)
               (add-edge! g u v))))
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
            [live-afters lives]
            [new-ss (for/list ([inst ss] [live-after live-afters])
                      ((build-interference-instr^ live-after g locals) inst))]
            [new-info '()])
       (Block info ss))]))

(define build-interference-cfg
  (λ (def)
    (match def
      [(Def label paramtypes returntype info alist)
       (define locals (dict-ref info 'locals))
       (let ([g (undirected-graph '())])
         (for ([v locals]) (add-vertex! g (car v)))
         (for/list ([(label block) (in-dict alist)])
                          (build-interference-block^ block g locals))
         (Def label paramtypes returntype
              (dict-set info 'conflicts g)
              alist))])))

(define (build-interference ast)
  (match ast
    [(ProgramDefs info defns)
     (define new-ds (map build-interference-cfg defns))
     (ProgramDefs info new-ds)]))

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
      (choose-least satset (add1 cand) locals v)))

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

;; color-graph : InterferenceGraph -> [Hash Var SatSet] -> [(Var . Nat)] -> [(Var . Nat)]
;; takes an unweighted/undirected intereference graph and a mutable hashtable of vars to saturation sets
;; in program, returns mapping from var to color (Nat) using an accumulator

(define (color-graph ig hash locals coloring)
  (if (hash-empty? hash)
      coloring
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
        (color-graph ig hash locals (dict-set coloring maxsat-vert col))
        #;(cons `(,maxsat-vert . ,col) (color-graph ig hash locals)))))

;; allocate-registers-exp : pseudo-x86 InterferenceGraph [Var] [Var . Home] -> pseudo-x86
;; takes in pseudo-x86 exp, intereference graph, and list of vars, returns
;; a pseudo-x86 exp with allocated registers according to color-graph

(define REGCOLS '((0 . rbx) (1 . rcx) (2 . rdx) (3 . rsi) (4 . rdi) (5 . r8) (6 . r9)
                            (7 . r10) (8 . r12) (9 . r13) (10 . r14)))


(define spilled-root (mutable-set))
(define spilled-stack (mutable-set))

(define r4_02 (parse-program `(program '()  (define (add8  [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer] [g : Integer] [h : Integer])     : Integer
                                              (+ a (+ b (+ c (+ d (+ e (+ f (+ g h))))))))
                                       (add8 0 1 1 1 1 1 1 35))))

#;(define upto-alloc-reg
  (build-interference
   (uncover-live
    (select-instructions
     (uncover-locals
      (explicate-control
       (remove-complex-opera*
        (expose-allocation
         (limit-functions
          (reveal-functions
           (uniquify
            (shrink
             (type-check-R4 r4_01)))))))))))))

;; change sig to
;; allocate-registers-exp : pseudo-x86 [Var . Nat] -> pseudo-x86

(define (allocate-registers-exp e coloring locals)
    (match e
      [(FunRef lbl) (FunRef lbl)]
      [(Reg reg) (Reg reg)]
      [(ByteReg r) (ByteReg r)]
      [(Imm int) (Imm int)]
      [(Deref v i) (Deref v i)]
      [(Var v) (if (vector-type? locals v)
                  (let ([colnum (dict-ref coloring v)])
                    (if (<= colnum 10)
                        (Reg (dict-ref REGCOLS colnum))
                        (begin 
			  (let ([location (* -8 (add1 (quotient (- colnum 11) 2)))])
                          (set-add! spilled-root location)
                          (Deref 'r15 location)))))
                  (let ([colnum (dict-ref coloring v)])
                    #;(printf "coloring for ~a is ~a\n" v coloring)
                    (if (<= colnum 10)
                        (Reg (dict-ref REGCOLS colnum))
                        (begin
			  (let ([location (* -8 (quotient (- colnum 10) 2))])
                          (set-add! spilled-stack location)
                          (Deref 'rbp (- location 40)))))))]
      [(Instr 'leaq (list arg reg)) (Instr 'leaq (list (allocate-registers-exp arg coloring locals)
                                                       (allocate-registers-exp reg coloring locals)))]
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
      [(IndirectCallq lbl arity) (IndirectCallq (allocate-registers-exp lbl coloring locals) arity)]
      [(TailJmp arg arity) (TailJmp (allocate-registers-exp arg coloring locals) arity)]
      [(Callq l arity) (Callq l arity)]
      [(Retq) (Retq)]
      [(Global var) (Global var)]
      [(Instr 'pushq (list e1)) (Instr 'pushq (list (allocate-registers-exp e1 coloring locals)))]
      [(Instr 'popq (list e1)) (Instr 'popq (list (allocate-registers-exp e1 coloring locals)))]
      [(Jmp e1) (Jmp e1)]
      [(JmpIf cc label) (JmpIf cc label)]
      [(Block info es) (Block info (for/list ([e es]) (allocate-registers-exp e coloring locals)))]))

;; need to store num-spills/stack-space in def info

; color-reg : RegSym -> [Var . Nat]
; colors the register symbol to the correct REGCOL

(define (color-reg reg)
  (cond [(symbol=? reg 'rax) `(,reg . -2)]
        [(symbol=? reg 'r11) `(,reg . -2)]
        [(symbol=? reg 'r15) `(,reg . -2)]
        [(symbol=? reg 'rbp) `(,reg . -2)]
        [(symbol=? reg 'rsp) `(,reg . -2)]
        [(symbol=? reg 'al)  `(,reg . -2)]
        [(symbol=? reg 'rbx) `(,reg . 0)]
        [(symbol=? reg 'rcx) `(,reg . 1)]
        [(symbol=? reg 'rdx) `(,reg . 2)]
        [(symbol=? reg 'rsi) `(,reg . 3)]
        [(symbol=? reg 'rdi) `(,reg . 4)]
        [(symbol=? reg 'r8)  `(,reg . 5)]
        [(symbol=? reg 'r9)  `(,reg . 6)]
        [(symbol=? reg 'r10) `(,reg . 7)]
        [(symbol=? reg 'r12) `(,reg . 8)]
        [(symbol=? reg 'r13) `(,reg . 9)]
        [(symbol=? reg 'r14) `(,reg . 10)]))

; pre-process-reg-hash : InterferenceGraph -> Hash[Var -> SatSet]
; makes the initial hash table that adds reg colors to adjacent vars

(define (pre-process-reg-hash ig coloring)
  (let* ([hash (make-hash)]
         [reg-verts (filter reg-sym? (get-vertices ig))]
         [reg-verts-neighbors (foldr (λ (f r) (append (get-neighbors ig f) r)) empty reg-verts)]
         [adj-to-reg-verts (filter (λ (v) (not (reg-sym? v))) reg-verts-neighbors)])
    (for-each (λ (vert)
                (for-each (λ (neighbor)
                            (if (= -1 (dict-ref coloring neighbor))
                                hash
                                (hash-set! hash vert
                                           (cons (dict-ref coloring neighbor)
                                                 (if (hash-has-key? hash vert)
                                                     (hash-ref hash vert)
                                                     empty)))))
                          (get-neighbors ig vert)))
              adj-to-reg-verts)
    hash))

(define (allocate-registers p)
  (match p
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds])
                      (match d
                        [(Def label paramtypes returntype info alist)
                         (let* ([locals (dict-ref info 'locals)]
                                [ig (dict-ref info 'conflicts)]
                                [pre-color (map (λ (vert) (if (reg-sym? vert)
                                                              (color-reg vert)
                                                              `(,vert . -1)))
                                                (get-vertices ig))]
                                [pre-process-hash (pre-process-reg-hash ig pre-color)]
                                [_ (for-each (λ (v) (if (or (hash-has-key? pre-process-hash v)
                                                            (reg-sym? v))
                                                        'asdf
                                                        (hash-set! pre-process-hash v '()))) (get-vertices ig))]
                                [coloring (begin
                                            #;(printf "hash: ~a\n" pre-process-hash)
                                            (color-graph ig
                                                       pre-process-hash
                                                       locals
                                                       pre-color))]
                                [new-alist (for/list ([pr alist]) (cons (car pr)
                                                                        (allocate-registers-exp
                                                                         (cdr pr)
                                                                         coloring
                                                                         locals)))])
                           #;(printf "coloring for ~a is : ~a\n" label coloring)
                           (define s1 (set-count spilled-stack))
                           (define s2 (set-count spilled-root)) 
                           (set! spilled-root (mutable-set))
                           (set! spilled-stack (mutable-set))
                           (define new-info (append (list (cons 'stack-space (* 8 s1))
                                                          (cons 'num-spills `(,s1 . ,s2))) info))
                           (Def label paramtypes returntype new-info new-alist))])))
     (ProgramDefs info new-ds)]))

;; patch-instructions : psuedo-x86 -> x86

(define (patch-instructions-instr px86instr)
  (match px86instr
    [(Instr 'movq (list (Imm n) (Deref r i))) (if (> n (expt 2 16))
                                                  (list (Instr 'movq (list (Imm n) (Reg 'rax)))
                                                        (Instr 'movq (list (Reg 'rax) (Deref r i))))
                                                  (list px86instr))]
    [(IndirectCallq lbl arity) (list (IndirectCallq lbl arity))] ;; don't need to change this
    [(TailJmp arg arity)
     (match arg
       [(Reg 'rax) (list (TailJmp arg arity))]
       [_ (list (Instr 'movq (list arg (Reg 'rax))) ;; this seems right
                (TailJmp (Reg 'rax) arity))])]
    [(Instr 'leaq (list f shouldbereg))
     (match shouldbereg
       [(Reg r) (list (Instr 'leaq (list f shouldbereg)))]
       [_ (list (Instr 'leaq (list f (Reg 'rax)))
                (Instr 'movq (list (Reg 'rax) shouldbereg)))])] ;; should be good
    [(Instr 'cmpq (list e1 e2))
     (match e2
       [(Imm n) (list (Instr 'movq (list e2 (Reg 'rax))) (Instr 'cmpq (list e1 (Reg 'rax))))]
       [(Deref a b) (list (Instr 'movq (list e2 (Reg 'rax))) (Instr 'cmpq (list e1 (Reg 'rax))))]
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
    [(ProgramDefs info ds)
     (define new-ds
       (for/list ([d ds])
         (match d
           [(Def label paramtypes returntype info alist)
            (define new-alist (for/list ([p alist])
                                (cons (car p)
                                      (patch-instructions-block (cdr p)))))
            (Def label paramtypes returntype info new-alist)])))
     (ProgramDefs info new-ds)]))

(define r1-10 (Let 'x (Prim 'read '()) (Let 'y (Prim 'read '()) (Prim '+ (list (Var 'x) (Prim '- (list (Var 'y))))))))
(define r1-10prog (Program '() r1-10))

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

(define (make-main stack-size root-spills main label)
  (let* ([push-bytes 32]
         [stack-adjust (- (align (+ push-bytes stack-size) 16) push-bytes)])
    (Block '()
           (append (list (Instr 'pushq (list (Reg 'rbp)))
                         (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                   (map (lambda (x) (Instr 'pushq (list x))) (list (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14))) 
                   (list (Instr 'subq (list (Imm stack-adjust) (Reg 'rsp)))) 
                   (if main 
		       (initialize-garbage-collector root-spills)
		       (dont-initialize-garbage-collector root-spills))
                   (list (Jmp (symbol-append label 'start)))))))

(define (make-conclusion stack-size root-spills)
  (let* ([push-bytes 32]
         [stack-adjust (- (align (+ push-bytes stack-size) 16) push-bytes)])
    (Block '()
           (append (list (Instr 'subq (list (Imm (* 8 root-spills)) (Reg 'r15)))
                         (Instr 'addq (list (Imm stack-adjust) (Reg 'rsp))))
                   (map (lambda (x) (Instr 'popq (list x))) (list (Reg 'r14) (Reg 'r13) (Reg 'r12) (Reg 'rbx))) 
                   (list (Instr 'popq (list (Reg 'rbp)))
                         (Retq))))))

(define root-stack-size (expt 2 16))
(define heap-size (expt 2 16))

(define (initialize-garbage-collector root-spills)
  (append (list (Instr 'movq (list (Imm root-stack-size) (Reg 'rdi)))
                (Instr 'movq (list (Imm heap-size) (Reg 'rsi)))
                (Callq 'initialize 2)
                (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
	  (for/list ([i root-spills]) (Instr 'movq (list (Imm 0) (Deref 'r15 (* i 8)))))
	  (list (Instr 'addq (list (Imm (* 8 root-spills)) (Reg 'r15))))))

(define (dont-initialize-garbage-collector root-spills)
  (append (for/list ([i root-spills]) (Instr 'movq (list (Imm 0) (Deref 'r15 (* i 8)))))
	  (list (Instr 'addq (list (Imm (* 8 root-spills)) (Reg 'r15))))))

(define (stringify-arg arg)
  (match arg
    [(FunRef lbl) (format "~a(%rip)" (label-name lbl))]
    [(Global name)
     (format "~a(%rip)" (label-name name))]
    [(Imm n) (format "$~a" n)]
    [(Reg r) (format "%~a" r)]
    [(ByteReg r) (format "%~a" r)]
    [(Deref r n) (format "~a(%~a)" n r)]))

(define (stringify-in instr stack-size)
  (match instr
    [(IndirectCallq arg arity)
     (define st (stringify-arg arg))
     (format "callq\t*~a" st)]
    [(TailJmp arg arity)
     (define popf
       (map (lambda (x) (Instr 'popq (list x)))
            (list (Reg 'r14) (Reg 'r13) (Reg 'r12) (Reg 'rbx) (Reg 'rbp))))
     (define popframe (let ([stack-adjust (- (align (+ 32 stack-size) 16) 32)])
                        (cons (Instr 'addq (list (Imm stack-adjust) (Reg 'rsp))) popf)))
     (define popstring
       (foldr (λ (inst rec) (string-append (stringify-in inst stack-size) "\n" "\t" rec)) "" popframe))
     (define st (stringify-arg arg))
     (format "~ajmp\t*~a" popstring st)]
    [(Instr 'leaq (list arg reg))
     (define st1 (stringify-arg arg))
     (define st2 (stringify-arg reg))
     (format "leaq\t~a, ~a" st1 st2)]
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
    [(Callq lbl arity)
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
(define (format-x86 ins stack-size)
  (foldr (λ (f r) (string-append "\t" f "\n" r)) "" (map (λ (i) (stringify-in i stack-size)) ins)))
     
;(format "~a:\n\t" label)

;; print-x86 : x86 -> string
(define (print-x86 p)
  (match p
    [(ProgramDefs info ds)
      (foldr string-append ""
            (for/list ([d ds])
              (match d [(Def label paramtypes returntype info alist)
                        (define new-alist (cons (cons (string->symbol (string-append (symbol->string label) "conclusion"))
                                                      (make-conclusion (dict-ref info 'stack-space)
                                                                       (cdr (dict-ref info 'num-spills)))) 
                                                (cons (cons label (if (equal? label 'main)
								      (make-main (dict-ref info 'stack-space) (cdr (dict-ref info 'num-spills)) #t label)
								      (make-main (dict-ref info 'stack-space) (cdr (dict-ref info 'num-spills)) #f label))) 
                                                      alist)))
                        (format "~a"
                                (foldr string-append ""
                                       (for/list ([pair new-alist])
                                         (string-append (if (equal? (car pair) label) ;; .align 16 ?
                                                            (format "\n\t.globl ~a\n\t.align 16\n~a"
                                                                    (label-name label)
                                                                    (label-name label))
                                                            (label-name (car pair)))
                                                        ":\n" (format-x86 (Block-instr* (cdr pair)) (dict-ref info 'stack-space))))))])))]))

