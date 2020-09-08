#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-R0.rkt")
(require "interp-R1.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

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
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniquify-exp
  (λ (symtab)
    (λ (exp)
      (match exp
        [(Var x)
         (Var (symbol-table-lookup symtab x))]
        [(Int n) (Int n)]
        [(Let x e body)
         (let ([new-x (gensym x)]) 
           (Let new-x
                ((uniquify-exp symtab) e)
                ((uniquify-exp (extend-symbol-table symtab x new-x)) body)))]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp symtab) e)))]))))


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

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
    (match p
      [(Program info e)
       (Program info (rco-exp e))]))

(define map-values
    (λ (f ls)
      (cond
        [(empty? ls)
         (values '() '())]
        [(cons? ls) (define-values (v1 v2) (f (car ls)))
                    (define-values (ls1 ls2) (map-values f (cdr ls)))
                    (values (cons v1 ls1) (cons v2 ls2))])))

#;(define rco-atom
  (λ (e)
    (match e
      [(Var x) (values e '())]
      [(Int n) (values e '())]
      [(Let x e body)
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (list (cons v (Let x (rco-exp e) (rco-exp body))))))]
      [(Prim op es)
       (define-values (exps syms)
         (map-values
          (λ (e)
            (if (or (Var? e) (Int? e))
                (rco-atom e)
                (let ([v (gensym 'tmp)])
                  (define-values (_1 _2) (rco-atom e))
                  (values (Var v)
                          (cons (cons v _1) _2)))))
          es))
       (let ([v (gensym 'tmp)])
         (values (Var v)
                 (cons (cons v (Prim op exps)) (append* syms))))])))

#;(define rco-exp
  (λ (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Let x e body) (Let x e (rco-exp body))]
      [(Prim op es)
       (define-values (exps symbols) (map-values rco-atom es))
       (foldl
        (λ (elem acc)
          (if (empty? elem) acc (Let (car elem) (cdr elem) acc)))
        (Prim op (reverse exps))
        (append* symbols))])))

(define rco-atom
  (λ (e)
    (match e
      [(Var x) (values e '())]
      [(Int n) (values e '())]
      [(Let x e body)
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (list (cons v (Let x (rco-exp e) (rco-exp body))))))]
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
                 (cons (cons v (Prim op exps)) (append* syms))))])))
(define rco-exp
  (λ (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
      [(Prim op es)
       (define-values (exps symbols) (map-values rco-atom es))
       (foldl
        (λ (elem acc)
          (if (empty? elem) acc (Let (car elem) (cdr elem) acc)))
        (Prim op exps)
        (append* (reverse symbols)))])))

(define rp (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()))) (Prim 'read '())))))

;;Grant's messing around with rco

(define (remove-complex-opera1* p)
    (match p
      [(Program info e)
       (Program info (rco-exp1 e))]))

(define rco-atom1
  (λ (e)
    (match e
      [(Var x) (values e '())]
      [(Int n) (values e '())]
      [(Let x e body)
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (list (cons v (Let x (rco-exp1 e) (rco-exp1 body))))))]
      [(Prim '+ (list e1 e2))
       (define-values (x1 ls1) (rco-atom1 e1))
       (define-values (x2 ls2) (rco-atom1 e2))
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (append (list (cons v (Prim '+ (list x1 x2)))) ls1 ls2)))]
      [(Prim '- (list e1))
       (define-values (x1 ls1) (rco-atom1 e1))
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (append (list (cons v (Prim '- (list x1)))) ls1)))]
      [(Prim 'read '())
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (list (cons v (Prim 'read '())))))]
      )))

(define rco-exp1
  (λ (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Let x e body) (Let x e (rco-exp1 body))]
      [(Prim op es)
       (define-values (exps symbols) (map-values rco-atom1 es))
       (foldl
        (λ (elem acc)
          (if (empty? elem) acc (Let (car elem) (cdr elem) acc)))
        (Prim op (reverse exps))
        (append* symbols))])))

;;(rco-exp1 (Prim '+ (list (Prim '- (list (Int 10))) (Int 4))))
;;(remove-complex-opera1* (Program '() (Prim '+ (list (Prim '- (list (Int 10))) (Int 4)))))
;(remove-complex-opera* (Program '() (Prim '+ (list (Int 1) (Prim '+ (list (Int 1) (Prim '+ (list (Int 1) (Int 1)))))))))
;; Sam

; explicate-tail : R1 -> C0Tail x [Var]
; takes in R1 expression and produces C0 Tail and list of let-bound variables
(define (explicate-tail r1exp)
  (match r1exp
    [(Int n)
     (values (Return (Int n)) '())]
    [(Prim 'read '())
     (values (Return (Prim 'read '())) '())]
    [(Prim '- (list e))
     (values (Return (Prim '- (list e))) '())]
    [(Prim '+ (list e1 e2))
     (values (Return (Prim '+ (list e1 e2))) '())] 
    [(Var x)
     (values (Return (Var x)) '())]
    [(Let x e body) 
     (define-values (c0tail let-binds) (explicate-tail body))
     (define-values (c0tail^ let-binds^) (explicate-assign e (Var x) c0tail))
     (values c0tail^ (cons x (append let-binds let-binds^)))]))


; explicate-assign : R1 Var C0Tail -> C0Tail x [Var]
; takes in R1 expression, the variable where it will be assigned, and a C0Tail that comes
; after the assignment. Returns a C0Tail and list of variables

(define (explicate-assign r1exp v c)
  (match r1exp
    [(Int n)
     (values (Seq (Assign v (Int n)) c) '())]
    [(Prim 'read '())
     (values (Seq (Assign v (Prim 'read '())) c) '())]
    [(Prim '- (list e))
     (values (Seq (Assign v (Prim '- (list e))) c)
             '())] 
    [(Prim '+ (list e1 e2))
     (values (Seq (Assign v (Prim '+ (list e1 e2))) c)
             '())] 
    [(Var x)
     (values (Seq (Assign v (Var x)) c) '())]
    [(Let x e body) 
     (define-values (c0tail let-binds) (explicate-assign body v c))
     (define-values (c0tail^ let-binds^) (explicate-assign e (Var x) c0tail))
     (values c0tail^ (cons x (append let-binds let-binds^)))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e)
     (define-values (c0t let-binds) (explicate-tail e))
     (Program (cons (cons 'locals let-binds) info) (CFG (list (cons 'start c0t))))]))

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
      [(Int n) true]
      [(Var x) true]
      [_ false]))

; sel-ins-atm : C0atm -> pseudo-x86
; takes in a c0 atom and converts to pseudo-x86

(define (sel-ins-atm c0a)
  (match c0a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]))

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
                              (Instr 'addq (list x86atm2 v)))])]))]))

; sel-ins-tail : C0tail -> pseudo-x86
; takes in a c0 tail and converts it ot pseudo-x86

(define (sel-ins-tail c0t)
  (match c0t
    [(Return e)
     (append (sel-ins-stmt (Assign (Reg 'rax) e))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (define x86stmt (sel-ins-stmt stmt))
     (define x86tail (sel-ins-tail tail))
     (append x86stmt x86tail)]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(Program info (CFG es))
     (Program info (CFG (for/list ([ls es]) (cons (car ls) (Block '() (sel-ins-tail (cdr ls)))))))]))

;; I think this is right...
;; todo: check/test !

;; note: select-instructions passes all tests in run-tests.rkt

;; /Sam

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
    [(Instr 'pushq e1) (Instr 'pushq e1)]
    [(Instr 'popq e1) (Instr 'popq e1)]
    [(Jmp e1) (Jmp e1)]
    [(Block info es) (Block info (for/list ([e es]) (assign-homes-exp e ls)))]
    ))

(define (assign-homes p)
  (match p
    [(Program info (CFG es)) (Program (list (cons 'stack-space (calc-stack-space (cdr (car info))))) (CFG (for/list ([ls es]) (cons (car ls) (assign-homes-exp (cdr ls) (car info))))))]
    ))

;; note: assign-homes passes all tests in run-tests.rkt

;;TEST
;;(assign-homes (Program (list (cons 'locals (list (Var 'x) (Var 'y)))) (CFG (list (cons 'start (Block '() (list (Instr 'movq (list (Imm 42) (Var 'y))) (Instr 'negq (list (Var 'y))) (Instr 'movq (list (Var 'y) (Var 'x))) (Instr 'movq (list (Var 'x) (Reg 'rax))) (Instr 'negq (list (Reg 'rax))) (Jmp 'conclusion))))))))
;;(assign-homes (select-instructions (explicate-control r1program-let)))
;;(let ([x (+ (read) (read))]) x)
;(remove-complex-opera* (uniquify (Program '() (Let 'x (Prim '+ (list (Prim 'read '()) (Prim 'read '()))) (Var 'x)))))

;;  (error "TODO: code goes here (assign-homes)"))

;; Grant

;; patch-instructions : psuedo-x86 -> x86

(define (patch-instructions-exp e)
  (match e
    [(Instr 'addq (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (list (Instr 'movq (list e1 (Reg 'rax))) (Instr 'addq (list (Reg 'rax) e2)))]
       [(list x y) (list (Instr 'addq (list e1 e2)))]
       )]
    [(Instr 'subq (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (list (Instr 'movq (list e1 (Reg 'rax))) (Instr 'subq (list (Reg 'rax) e2)))]
       [(list x y) (list (Instr 'subq (list e1 e2)))]
       )]
    [(Instr 'movq (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (list (Instr 'movq (list e1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) e2)))]
       [(list x y) (list (Instr 'movq (list e1 e2)))]
       )]
    [(Instr 'negq (list e1)) (list (Instr 'negq (list e1)))]
    [(Callq l) (list (Callq l))]
    [(Retq) (list (Retq))]
    [(Instr 'pushq e1) (list (Instr 'pushq e1))]
    [(Instr 'popq e1) (list (Instr 'popq e1))]
    [(Jmp e1) (list (Jmp e1))]
    [(Block info es) (Block info (append* (for/list ([e es]) (patch-instructions-exp e))))]
    ))

(define (patch-instructions p)
  (match p
    [(Program info (CFG es)) (Program info (CFG (for/list ([ls es]) (cons (car ls) (patch-instructions-exp (cdr ls))))))]
    ))

;;TEST
;;(patch-instructions (assign-homes (select-instructions (explicate-control r1program-let))))

;;  (error "TODO: code goes here (patch-instructions)"))

;; Grant/Sam

(define x86prog (patch-instructions (assign-homes (select-instructions (explicate-control r1program-let)))))
;x86prog


#;(Program (list (cons 'stack-space 16))
              (CFG (list (cons 'start (Block '() (list (Instr 'movq (list (Imm 42) (Deref 'rpb -16)))
                                                       (Instr 'negq (list (Deref 'rpb -16)))
                                                       (Instr 'movq (list (Deref 'rpb -16) (Reg 'rax)))
                                                       (Instr 'movq (list (Reg 'rax) (Deref 'rpb -8)))
                                                       (Instr 'movq (list (Deref 'rpb -8) (Reg 'rax)))
                                                       (Instr 'negq (list (Reg 'rax)))
                                                       (Jmp 'conclusion)))))))

(define (main-str stacksize)
  (format "\t.globl ~a\n~a:\n\tpushq\t%rbp\n\tmovq\t%rsp, %rbp\n\tsubq\t$~a, %rsp\n\tjmp ~a\n" (label-name "main") (label-name "main") (align stacksize 16) (label-name "start"))) ;; 16 is stack-space

(define (concl-str stacksize)
  (format "~a:\n\taddq\t$~a, %rsp\n\tpopq\t%rbp\n\tretq"
          (label-name "conclusion") (align stacksize 16))) ;; stack-space

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
  (foldr (λ (f r) (string-append "\t" f "\n" r)) "" (map stringify-in ins))
  #;(if (empty? ins)
      "start:\n\tjmp\tconclusion"
      (map)))
     
     ;(format "~a:\n\t" label)

;; print-x86 : x86 -> string
(define (print-x86 p)
  (match p
    [(Program info (CFG es)) (format "~a:\n~a~a~a"
                                     (label-name "start")
                                     (format-x86 (Block-instr* (cdr (car es))))
                                     (main-str (cdr (car info)))
                                     (concl-str (cdr (car info))))]
    ))
;;  (error "TODO: code goes here (print-x86)"))

;;Grant/Sam
