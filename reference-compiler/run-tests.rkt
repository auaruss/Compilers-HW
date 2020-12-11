#! /usr/bin/env racket 
#lang racket
(require "utilities.rkt")
(require "int_exp.rkt")
(require "register_allocator.rkt")
(require "conditionals.rkt")
(require (only-in "type-check-R2.rkt" type-check-R2))
(require (only-in "type-check-R3.rkt" type-check-R3))
(require (only-in "type-check-R4.rkt" type-check-R4))
(require (only-in "type-check-R5.rkt" type-check-R5))
(require (only-in "type-check-R6.rkt" type-check-R6-vectorof))
(require (only-in "type-check-R8.rkt" type-check-R8-vectorof))
(require "vectors.rkt")
(require "functions.rkt")
(require "lambda.rkt")
(require "any.rkt")
(require "dynamic-typing.rkt")
(require "loop.rkt")
;(require "gradual-typing.rkt")
;; (require "inliner.rkt")
(require "interp.rkt")
(require (only-in "interp-R1.rkt" interp-R1))
(require (only-in "interp-R2.rkt" interp-R2))
(require (only-in "interp-R3.rkt" interp-R3))
(require (only-in "interp-R4.rkt" interp-R4))
(require (only-in "interp-R5.rkt" interp-R5))
(require (only-in "interp-R6.rkt" interp-R6))
(require (only-in "interp-R7.rkt" interp-R7))
(require (only-in "interp-R8.rkt" interp-R8))
(require "runtime-config.rkt")

;; To run all the compilers on all the tests, run the
;; following at the command line.
;;
;;   racket run-tests.rkt
;;
;; To get a description of what options are available pass "-h" for
;; the help message. For example, you can run 

;; Table associating names of compilers with the information for
;; running and testing them.
(define compiler-list
  ;; Name           Typechecker               Compiler-Passes      Initial interpreter  Valid test suites
  `(("int_exp"      #f                        ,int-exp-passes      ,interp-R1           ("int-exp"))
    ("reg_int"      #f                        ,reg-int-passes      ,interp-R1           ("int-exp"))
    ("cond"         ,type-check-R2            ,cond-passes         ,interp-R2           ("int-exp" "cond"))
    ("vectors"      ,type-check-R3            ,vectors-passes      ,interp-R3           ("int-exp" "cond" "vectors"))
    ("functions"    ,type-check-R4            ,functions-passes    ,interp-R4           ("int-exp" "cond" "vectors" "functions"))
    ("lambda"       ,type-check-R5            ,lambda-passes       ,interp-R5           ("int-exp" "cond" "vectors" "functions" "lambda"))
    ("any"          ,type-check-R6-vectorof   ,R6-passes           ,interp-R6           ("int-exp" "cond" "vectors" "functions" "lambda" "any"))
    ("dynamic"      #f                        ,R7-passes           ,interp-R7           ("dynamic"))
    ("loop"         ,type-check-R8-vectorof   ,loop-passes         ,interp-R8           ("loop" "int-exp" "cond" "vectors" "functions" "lambda" "any"))
    ;; ;; ("inliner"      ,R6-typechecker       ,inliner-passes       ,interp-R6           (0 1 2 3 4 6))
    #;("gradual"      ,R8-typechecker           ,R8-passes           ,interp-R6           (0 1 2 3 4 6 7 8))
    ))

#;(define compiler-list
  ;; Name           Typechecker               Compiler-Passes      Initial interpreter  Valid test suites
  `(("int_exp"      #f                        ,int-exp-passes      ,interp-R1           (0))
    ("reg_int"      #f                        ,reg-int-passes      ,interp-R1           (0))
    ("cond"         ,type-check-R2            ,cond-passes         ,interp-R2           (0 1))
    ("vectors"      ,type-check-R3            ,vectors-passes      ,interp-R3           (0 1 2))
    ("functions"    ,type-check-R4            ,functions-passes    ,interp-R4           (0 1 2 3))
    ("lambda"       ,type-check-R5            ,lambda-passes       ,interp-R5           (0 1 2 3 4))
    ("any"          ,type-check-R6            ,R6-passes           ,interp-R6           (0 1 2 3 4 6))
    ;("dynamic"      #f                        ,R7-passes           ,interp-R7           (7))
    ;; ;; ("inliner"      ,R6-typechecker       ,inliner-passes       ,interp-R6           (0 1 2 3 4 6))
    #;("gradual"      ,R8-typechecker           ,R8-passes           ,interp-R6           (0 1 2 3 4 6 7 8))
    ))

(define compiler-table (make-immutable-hash compiler-list))

;; This list serves the same function as the range definitions that were used
;; prior to giving run-tests a command line interfaces.
(define suite-list
  `(("int-exp" . ,(range 1 66))
    ("cond" . ,(range 1 79))
    ("vectors" . ,(range 1 45))
    ("functions" . ,(range 1 50))
    ("lambda" . ,(range 0 32))
    ("any" . ,(range 0 20))
    ("dynamic" . ,(range 0 17))
    ("gradual" . ,(range 0 7))
    ("loop" . ,(range 0 15))
    ))

(define (suite-range x)
  (let ([r? (assoc x suite-list)])
    (unless r?
      (error 'suite-range "invalid suite ~a" x))
    (cdr r?)))

;; test-compiler runs a compiler (list of passes) with a name and
;; typechecker on a list of tests in a particular test-suite.
(define (test-compiler name typechecker use-interp passes test-suite test-nums)
  (display "------------------------------------------------------")(newline)
  (display (format "testing compiler ~a on ~a" name test-suite))(newline)
  ; interpreter bug in tests/s4_12.rkt -Jeremy
  (interp-tests name typechecker passes use-interp test-suite test-nums)
  (if (test-ui)
      (compiler-tests-gui name typechecker passes test-suite test-nums)
      (compiler-tests name typechecker passes test-suite test-nums))
  )

;; These parameters may be altered by passing at the command line if
;; they are not altered then the default is to test everything.
(define compilers-to-test
  (make-parameter #f))
(define suites-to-test
  (make-parameter #f))
(define tests-to-run
  (make-parameter #f))
(define test-ui
  (make-parameter #f))

;; add some object to the end of an optional list stored in a parameter.
;; This seems case specific or else I would put it in utilities. -andre
(define (snoc-to-opt-param param x)
  (unless (parameter? param)
    (error 'snoc-to-opt-param "expected a parameter: ~a" param))
  (param (let ([list? (param)])
           (if list?
               (let snoc ([ls list?] [x x])
                 (cond
                   [(pair? ls)
                    (cons (car ls)
                          (snoc (cdr ls) x))]
                   [else (list x)]))
               (list x)))))

;; The command-line macro is a standard racket function for controlling
;; 
(command-line
 #:multi
 ;; Add a compiler to the set of test to run
 [("-c" "--compiler") name "add a compiler to the test set"
  (unless (hash-ref compiler-table name #f)
    (error 'run-tests
           "compiler flag expects a compiler: ~a\nvalid compilers ~a"
           name (map car compiler-list)))
  (snoc-to-opt-param compilers-to-test name)]
 ;; Add a test suite to the test to run
 [("-s" "--suite") suite-name "suite to run"
    (unless (dict-has-key? suite-list suite-name)
      (error 'run-tests "~a is an invalid suite name, choose among: ~a" suite-name (dict-keys suite-list)))
    (snoc-to-opt-param suites-to-test suite-name)]
 ;; Select individual tests to run
 [("-t" "--test") num "specify specific test numbers to run"
  (let ([test-n (string->number num)])
    (unless (exact-nonnegative-integer? test-n)
      (error 'run-tests "tests are nonnegative integers, got ~a" num))
    (snoc-to-opt-param tests-to-run test-n))]
 ;; turn up the debbugging volume
 ["-d" "increment debugging level" (debug-level (add1 (debug-level)))]

 ;; These are the flags that are each allowed once
 #:once-each
 [("-r" "--rootstack-size") bytes
  "set the size of rootstack for programs compiled"
  (let ([bytes? (string->number bytes)])
    (unless (and (exact-positive-integer? bytes?)
                 (= (remainder bytes? 8) 0))
      (error 'run-tests
             "rootstack-size expected positive multiple of 8: ~v"
             bytes)) 
    (rootstack-size bytes?))]

 [("-m" "--heap-size") bytes
  "set the size of initial heap for programs compiled"
  (let ([bytes? (string->number bytes)])
    (unless (and (exact-positive-integer? bytes?)
                 (= (remainder bytes? 8) 0))
      (error 'run-tests
             "heap-size expected positive multiple of 8: ~v" bytes)) 
    (heap-size bytes?))]
 ["--small-register-set"
  "use a minimal set of registers for register allocation"
  (use-minimal-set-of-registers! #t)]
 ["--gui"
  "use rackunit ui"
  (test-ui #t)]

 [("-a" "--abstract") "Print AST's using abstract syntax"
                      (AST-output-syntax 'abstract-syntax)]

 [("-n" "--concrete") "Print AST's using concrete syntax"
                      (AST-output-syntax 'concrete-syntax)]

 ;; Allows setting the number of columns that the pretty printer
 ;; uses to display s-expressions.
 [("-w" "--pprint-width") columns "set the width for pretty printing"
  (let ([columns (string->number columns)])
    (unless (exact-positive-integer? columns)
      (error 'run-tests "expected positive integer, but found ~v" columns)) 
    (pretty-print-columns columns))]


 #:args ()
 (debug "Code loaded, tests starting.")
 
 ;; default to testing all compilers 
 (unless (compilers-to-test)
   (compilers-to-test (map car compiler-list)))

 ;; default to testing all suites
 (unless (suites-to-test)
   (suites-to-test (map car suite-list)))

 ;; default to testing the first 100 tests in each suite
 (unless (tests-to-run)
   (tests-to-run (range 0 100)))

 ;; This is the loop that calls test compile for each suite
 (for ([compiler (compilers-to-test)])
   (let ([info? (hash-ref compiler-table compiler #f)])
     (unless info?
       (error 'run-tests "invalid compiler: ~a" compiler))
     (match-let ([(list tyck pass use-interp suites) info?])
       (for ([suite (suites-to-test)])
         (when (set-member? suites suite)
           (let* ([sname (format "~a_test" suite)]
                  [test-set (set-intersect (suite-range suite) (tests-to-run))]
                  [tests (sort test-set <)])
             (test-compiler compiler tyck use-interp pass sname tests))))))))

 

