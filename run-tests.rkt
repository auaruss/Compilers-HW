#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
#;(require "interp-R1.rkt")
#;(require "interp-R2.rkt")
#;(require "interp-R3.rkt")
(require "interp-R4.rkt")
#;(require "interp-C0.rkt")
#;(require "interp-C1.rkt")
#;(require "interp-C2.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(AST-output-syntax 'abstract-syntax)
(debug-level 0)
;; (AST-output-syntax 'concrete-syntax)

;; Define the passes to be used by interp-tests and the grader
;; Note that your compiler file (or whatever file provides your passes)
;; should be named "compiler.rkt"
#;(define r1-passes
  `( ("uniquify" ,uniquify ,interp-R1)
     ("remove complex opera*" ,remove-complex-opera* ,interp-R1)
     ("explicate control" ,explicate-control ,interp-C0)
     ("instruction selection" ,select-instructions ,R1-interp-x86)
     #;("assign homes" ,assign-homes ,R1-interp-x86)
     ("UL" ,uncover-live ,R1-interp-x86)
     ("BI" ,build-interference ,R1-interp-x86)
     ("AR" ,allocate-registers ,R1-interp-x86)
     ("patch instructions" ,patch-instructions ,R1-interp-x86)
     ("print x86" ,print-x86 #f)
     ))

#;(define r2-passes
  `(
     ("shrink" ,shrink ,interp-R2)
     ("uniquify" ,uniquify ,interp-R2)
     ("remove complex opera*" ,remove-complex-opera* ,interp-R2)
     ("explicate control" ,explicate-control ,interp-C1)
     ("instruction selection" ,select-instructions ,R2-interp-x86)
     ("uncover live" ,uncover-live ,R2-interp-x86)
     ("build interference" ,build-interference ,R2-interp-x86)
     ("allocate registers" ,allocate-registers ,R2-interp-x86)
     ("patch instructions" ,patch-instructions ,R2-interp-x86)
     ("print x86" ,print-x86 #f)
     ))

#;(define r3-passes
  `(
     ("shrink" ,shrink ,interp-R3)
     ("uniquify" ,uniquify ,interp-R3)
     ("expose allocation" ,expose-allocation ,(let ([interp (new interp-R3-class)])
                                                     (send interp interp-scheme '())))
     ("remove complex opera*" ,remove-complex-opera* ,(let ([interp (new interp-R3-class)])
                                                             (send interp interp-scheme '())))
     ("explicate control" ,explicate-control ,interp-C2)
     ("uncover locals" ,uncover-locals ,interp-C2)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-2)
     ("uncover live" ,uncover-live ,interp-pseudo-x86-2)
     ("build interference" ,build-interference ,interp-pseudo-x86-2)
     ("allocate registers" ,allocate-registers ,interp-x86-2)
     ("patch instructions" ,patch-instructions ,interp-x86-2)
     ("print x86" ,print-x86 #f)
     ))

(define interp-F1 
  (lambda (p)
    ((send (new interp-R4-class)
	   interp-F '()) p)))

(define r4-passes
  `(
     ("shrink" ,shrink ,interp-R4)
     ("uniquify" ,uniquify ,interp-R4)
     ("reveal functions" ,reveal-functions ,interp-F1)
     ("limit functions" ,limit-functions ,interp-F1)
     ("expose allocation" ,expose-allocation ,interp-F1)
     ("remove complex opera*" ,remove-complex-opera* ,interp-F1)
     ("explicate control" ,explicate-control ,interp-C3)
     #;("uncover locals" ,uncover-locals ,interp-C2)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
     #;("uncover live" ,uncover-live ,interp-pseudo-x86-2)
     #;("build interference" ,build-interference ,interp-pseudo-x86-2)
     #;("allocate registers" ,allocate-registers ,interp-x86-2)
     #;("patch instructions" ,patch-instructions ,interp-x86-2)
     #;("print x86" ,print-x86 #f)
     ))

(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (cadr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

(interp-tests "r4" type-check-R4 r4-passes interp-R4 "r4" (tests-for "r4"))
#;(compiler-tests "r3" type-check-R3 r3-passes "r3" (tests-for "r3"))

