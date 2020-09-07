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
         (let ([new-x ;: Symbol
                (gensym x)]) 
           (Let new-x
                ((uniquify-exp symtab) e)
                ((uniquify-exp (extend-symbol-table symtab x new-x)) body)))]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp symtab) e)))]))))


(define init-symbol-table
  (λ ()
    (let ([init ;: (Immutable-HashTable Symbol (Listof Symbol))
           (make-immutable-hash)]) init)))

(define symbol-table-lookup
  (λ (symtab x)
    (if (empty? (dict-ref x)) (error "variable not in scope") (car (dict-ref x)))))

(define extend-symbol-table
  (λ (symtab x new-x)
    (dict-set symtab
              x
              (let [(not-found ;: (→ (Listof Symbol))
                     (λ () '()))]
                (cons new-x (dict-ref symtab x not-found))))))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e)
     (Program info ((uniquify-exp '()) e))]
    ))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (error "TODO: code goes here (remove-complex-opera*)"))

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

(define (assign-homes-exp e)
  (match e
    [(Reg reg) (Reg reg)]
    [(Imm int) (Imm int)]
    [(Var v) (Deref 'rbp -8)]
    [(Instr 'addq (list e1 e2)) (Instr 'addq (list (assign-homes-exp e1) (assign-homes-exp e2)))]
    [(Instr 'subq (list e1 e2)) (Instr 'subq (list (assign-homes-exp e1) (assign-homes-exp e2)))]
    [(Instr 'movq (list e1 e2)) (Instr 'movq (list (assign-homes-exp e1) (assign-homes-exp e2)))]
    [(Instr 'negq (list e1)) (Instr 'negq (list (assign-homes-exp e1)))]
    [(Callq l) (Callq l)]
    [(Retq) (Retq)]
    [(Instr 'pushq e1) (Instr 'pushq e1)]
    [(Instr 'popq e1) (Instr 'popq e1)]
    [(Jmp e1) (Jmp e1)]
    [(Block info es) (Block info (for/list ([e es]) (assign-homes-exp e)))]
    ))

(define (assign-homes p)
  (match p
    [(Program info (CFG es)) (Program info (CFG (for/list ([ls es]) (cons (car ls) (assign-homes-exp (cdr ls))))))]
    ))

;; note: assign-homes passes all tests in run-tests.rkt

;;TEST
;;(assign-homes (Program '() (CFG (list (cons 'label (Block '() (list (Instr 'addq (list (Imm 10) (Imm 2))))))))))
;;(assign-homes (Program '() (CFG (list (cons 'label (Block '() (list (Instr 'addq (list (Imm 10) (Var 'v))))))))))

;;  (error "TODO: code goes here (assign-homes)"))

;; Grant

;; patch-instructions : psuedo-x86 -> x86

(define (patch-instructions-exp e)
  (match e
    [(Reg reg) (Reg reg)]
    [(Imm int) (Imm int)]
    [(Deref 'rbp x) (Deref 'rbp x)]
    [(Instr 'addq (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (values (Instr 'movq (list e1 (Reg 'rax))) (Instr 'addq (list (Reg 'rax) e2)))]
       [(list x y) (Instr 'addq (list e1 e2))]
       )]
    [(Instr 'subq (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (values (Instr 'movq (list e1 (Reg 'rax))) (Instr 'subq (list (Reg 'rax) e2)))]
       [(list x y) (Instr 'subq (list e1 e2))]
       )]
    [(Instr 'movq (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (values (Instr 'movq (list e1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) e2)))]
       [(list x y) (Instr 'movq (list e1 e2))]
       )]
    [(Instr 'negq (list e1)) (Instr 'negq (list e1))]
    [(Callq l) (Callq l)]
    [(Retq) (Retq)]
    [(Instr 'pushq e1) (Instr 'pushq e1)]
    [(Instr 'popq e1) (Instr 'popq e1)]
    [(Block info es) (Block info (for/list ([e es]) (patch-instructions-exp e)))]
    ))

(define (patch-instructions p)
  (match p
    [(Program info (CFG es)) (Program info (CFG (for/list ([ls es]) (cons (car ls) (patch-instructions-exp (cdr ls))))))]
    ))

;;TEST
;(patch-instructions (assign-homes (Program '() (CFG (list (cons 'label (Block '() (list (Instr 'addq (list (Var 'd) (Var 'v)))))))))))

;;  (error "TODO: code goes here (patch-instructions)"))

;; Grant

;; print-x86 : x86 -> string
(define (print-x86 p)
  (error "TODO: code goes here (print-x86)"))

;;Grant
