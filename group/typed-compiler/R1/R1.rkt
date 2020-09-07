#lang typed/racket/no-check
(require racket/set)
(require racket/stream)
(require racket/fixnum)

(: make-recur (→ Output-Port (U Boolean One Zero) (-> Any Output-Port Void)))
(define (make-recur port mode)
  (case mode
    [(#t) write]
    [(#f) display]
    [else (λ (p (port : Output-Port)) (print p port mode))]))

(: newline-and-indent (→ Output-Port (U Integer False) Index))
(define (newline-and-indent port col)
  (let ([lead : String (if col (make-string col #\space) "")])
    (newline port)
    (write-string lead port)
    ))

(define (print-info info port mode)
  (let ([recur (make-recur port mode)])
    (for ([(label data) (in-dict info)])
      (match label
        ['locals
         (write-string "locals:" port)
         (newline port)
         (cond [(dict? data)
                (write-string "    " port)
                (for ([(var type) (in-dict data)])
                  (write-string (symbol->string var) port)
                  (write-string " : " port)
                  (recur type port)
                  (write-string ", " port)
                  )
                (newline port)]
               [else
                (recur data port)
                (newline port)])]
        [else
         (write-string (symbol->string label) port)
         (write-string ":" port)
         (newline port)
         (recur data port)
         (newline port)
         ]))))

(define-type Val Fixnum)

(struct Int [(value : Val)]
  #:property
  prop:custom-write
  (λ [(int : Int)
      (port : Output-Port)
      (mode :(U Boolean One Zero))]
    (let ([recur (make-recur port mode)])
      (match int
        [(Int n)
         (write n port)]))))

(struct Prim [(op : Op) (arg* : (Listof Exp))]
  #:property
  prop:custom-write
  (λ [(prim : Prim)
      (port : Output-Port)
      (mode :(U Boolean One Zero))]
    (let ([recur (make-recur port mode)])
      (match prim
        [(Prim op arg*)
         (write-string "(" port)
         (write-string (symbol->string op) port)
         (for ([arg arg*])
           (write-string " " port)
           (recur arg port))
         (write-string ")" port)]))))

(struct Var [(name : Symbol)]
  #:property
  prop:custom-write
  (λ [(var : Var)
      (port : Output-Port)
      (mode :(U Boolean One Zero))]
    (let ([recur (make-recur port mode)])
      (match var
        [(Var x)
         (write x port)]))))

(struct Let [(var : Symbol)
             (rhs : Exp)
             (body : Exp)]
  #:property
  prop:custom-write
  (λ [(_let : Let)
      (port : Output-Port)
      (mode :(U Boolean One Zero))]
    (let ([recur (make-recur port mode)])
      (match _let
        [(Let x rhs body)
         (let-values ([((line : (U Integer False)) (col : (U Integer False)) (pos : (U Integer False)))
                       (port-next-location port)])
           (write-string "(let ([" port)
           (write-string (symbol->string x) port)
           (write-string " " port)
           (recur rhs port)
           (write-string "])" port)
           (newline-and-indent port col)
           (write-string "   " port) ;; indent body
           (recur body port)
           (write-string ")" port)
           (newline-and-indent port col)
           )]))))

(struct Program [(info : Env)
                 (body : Exp)]
  #:type-name R1
  #:property
  prop:custom-write
  (λ [(p : Program)
      (port : Output-Port)
      (mode :(U Boolean One Zero))]
    (let ([recur (make-recur port mode)])
      (match p
        [(Program info body)
         (write-string "program:" port)
         (newline port)
         (print-info info port mode)
         (cond [(list? body)
                (for ([def body])
                  (recur def port)
                  (newline port))]
               [else
                (recur body port)])]))))

(define-type Op (U 'read '+ '-))

(define-type Exp (U Int
                    Prim
                    Var
                    Let))

(define-type Env (Immutable-HashTable Symbol Val))

(define-type SymbolTable (Immutable-HashTable Symbol (Listof Symbol)))

;;pseudo x86



;;

;(define-type Arg (U Int Var))

(: interp-exp (→ Env (→ Exp Val)))
(define interp-exp
  (λ (env)
    (λ (e)
      (match e
        [(Int n) n]
        [(Prim 'read '())
         (define r (read))
         (cond [(fixnum? r) r]
               [else (error 'interp-R1 "expected an integer" r)])]
        [(Prim '- (list e))
         (define v ((interp-exp env) e))
         (fx- 0 v)]
        [(Prim '+ (list e1 e2))
         (define v1 ((interp-exp env) e1))
         (define v2 ((interp-exp env) e2))
         (fx+ v1 v2)]
        [(Var x) (get-val env x)]
        [(Let x e body)
         (define new-env (extend-env env x e))
         ((interp-exp new-env) body)]))))

(: interp-R1 (→ R1 Val))
(define (interp-R1 p)
  (match p
    [(Program info e) ((interp-exp (init-env)) e)]))

(: init-env (→ Env))
(define init-env
  (λ ()
    (let ([init : (Immutable-HashTable Symbol Val) (make-immutable-hash)]) init)))

(: extend-env (→ Env Symbol Exp Env))
(define extend-env
  (λ (env x e)
    (hash-set env x ((interp-exp env) e))))

(: get-val (→ Env Symbol Val))
(define get-val
  (λ (env x) (hash-ref env x)))

(: uniquify (→ R1 R1))
(define uniquify
  (λ (p)
    (match p
      [(Program info e)
       (Program info ((uniquify-exp (init-symbol-table)) e))])))

(: uniquify-exp (→ SymbolTable (→ Exp Exp)))
(define uniquify-exp
  (λ (symtab)
    (λ (exp)
      (match exp
        [(Var x)
         (Var (symbol-table-lookup symtab x))]
        [(Int n) (Int n)]
        [(Let x e body)
         (let ([new-x : Symbol (gensym x)]) 
           (Let new-x
                ((uniquify-exp symtab) e)
                ((uniquify-exp (extend-symbol-table symtab x new-x)) body)))]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp symtab) e)))]))))

(: init-symbol-table (→ SymbolTable))
(define init-symbol-table
  (λ ()
    (let ([init : (Immutable-HashTable Symbol (Listof Symbol)) (make-immutable-hash)]) init)))

(: symbol-table-lookup (→ SymbolTable Symbol Symbol))
(define symbol-table-lookup
  (λ (symtab x)
    (let ([lst : (Listof Symbol) (hash-ref symtab x)])
      (if (empty? lst) (error "variable not in scope") (car lst)))))

(: extend-symbol-table (→ SymbolTable Symbol Symbol SymbolTable))
(define extend-symbol-table
  (λ (symtab x new-x)
    (hash-set symtab
              x
              (let [(not-found : (→ (Listof Symbol)) (λ () '()))]
                (cons new-x (hash-ref symtab x not-found))))))


(: map-values (∀ (A B C) (→ (→ A (Values B C)) (Listof A) (Values (Listof B) (Listof C)))))
(define map-values
    (λ (f ls)
      (cond
        [(empty? ls)
         (values '() '())]
        [(cons? ls) (define-values (v1 v2) (f (car ls)))
                    (define-values (ls1 ls2) (map-values f (cdr ls)))
                    (values (cons v1 ls1) (cons v2 ls2))])))

(: remove-complex-opera* (→ R1 R1))
(define remove-complex-opera*
  (λ (p)
    (match p
      [(Program info e)
       (Program info (rco-exp e))])))

(: rco-atom (→ Exp (Values Exp (Listof (Pairof Symbol Exp)))))
(define rco-atom
  (λ (e)
    (match e
      [(Var x) (values e '())]
      [(Int n) (values e '())]
      [(Let x e body)
       (let ([v : Symbol (gensym 'tmp)])
                 (values
                  (Var v)
                  (list (cons (gensym 'tmp) (Let x (rco-exp e) (rco-exp body))))))]
      [(Prim op es)
       (map-values (λ ([exp : Exp]) (rco-atom exp)) es)])))

(: rco-exp (→ Exp Exp))
(define rco-exp
  (λ (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Let x e body) (Let x e (rco-exp body))]
      [(Prim op es)
       (define-values (exps symbols) (map-values rco-atom es))
       (foldr
        (λ (elem acc)
          (foldr
           (λ (e a)
             (if (empty? e) a (Let (car e) (cdr e) a)))
           acc
           elem))
        (Prim op exps)
        symbols)])))



#|

(: patch-instructions (→ R1 R1))
(define patch-instructions
  (λ (p)
    (match p
      [(Program info e)
       (Program info ((patch-instructions-exp (init-symbol-table)) e))])))

(: patch-instructions-exp (→ SymbolTable (→ Exp Exp)))
(define patch-instructions-exp
  (λ (symtab)
    (λ (exp)
      (match exp
        [(Var x)
         (Var (symbol-table-lookup symtab x))]
        [(Int n) (Int n)]
        [(Let x e body)
         (let ([new-x : Symbol (gensym x)]) 
           (Let new-x
                ((uniquify-exp symtab) e)
                ((uniquify-exp (extend-symbol-table symtab x new-x)) body)))]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp symtab) e)))]))))
|#          
          
          

;; TESTS

#;(define process-exp
  (λ (e)
    (match e
      [(Var x) ...]
      [(Int n) ...]
      [(Let x e body) ...]
      [(Prim op es) ...])))

(define p1 (Program (init-env)
                    (Prim '+
                          (list (Int 2) (Int 3)))))
(define p2 (Program (init-env)
                    (Prim '+
                          (list (Int 2) (Prim '- (list (Int 3)))))))

(define p3 (Program (init-env)
                    (Let 'x
                         (Int 32)
                         (Prim '+
                               (list
                                (Let 'x
                                     (Int 10)
                                     (Var 'x))
                                (Var 'x))))))


(remove-complex-opera* (uniquify p1))
(remove-complex-opera* (uniquify p2))
(remove-complex-opera* (uniquify p3))
