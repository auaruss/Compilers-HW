#lang racket
(require racket/set)
(require graph)
(require "utilities.rkt")
(require "int_exp.rkt")
(require "interp-R1.rkt")
(require "interp-C0.rkt")
(require "interp.rkt")
(require "type-check-R1.rkt")
(require "priority_queue.rkt")

(provide reg-int-passes compile-reg-R1)

(define compile-reg-R1
  (class compile-R1
    (super-new)

    (field [use-move-biasing #t])

    (inherit assign-homes-instr assign-homes-block
             print-x86-instr print-x86-block)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> pseudo-x86 -> pseudo-x86*
    ;; *annotated program with live-after information for each stmt

    (define/public (free-vars arg)
      (match arg
	 [(Var x) (set x)]
	 [(Reg r) (set r)]
	 [(Deref r i) (set r)]
	 [(Imm n) (set)]
	 [else (error "free-vars, unhandled" arg)]))

    (define/public (read-vars instr)
      (match instr
         [(Instr 'movq (list s d)) (free-vars s)]
	 [(Instr name arg*)
	  (apply set-union (for/list ([arg arg*]) (free-vars arg)))]
	 [(Callq f n)
          (vector->set (vector-take arg-registers n))]
         [(Jmp label) (set)]
	 [else (error "read-vars unmatched" instr)]
	 ))
  
    (define/public (write-vars instr)
      (match instr
        [(Instr 'movq (list s d)) (free-vars d)]
        [(Instr name arg*)
         (free-vars (last arg*))]
        [(Jmp label) (set)]
        [(Callq f n) (caller-save-for-alloc)]
        [else (error "write-vars unmatched" instr)]
        ))

    (define/public (uncover-live-instr live-after)
      (lambda (instr)
        (set-union (set-subtract live-after (write-vars instr))
                   (read-vars instr))))

    (define/public (uncover-live-block ast block-live-after)
      (match ast
        [(Block info instrs)
         (define lives 
           (let loop ([ss (reverse instrs)]
                      [live-after block-live-after] 
                      [lives (list block-live-after)])
             (cond [(null? ss) lives]
                   [else
                    (define live-after^
                      ((uncover-live-instr live-after) (car ss)))
                    (loop (cdr ss) live-after^
                          (cons live-after^ lives))])))
         (define new-info (dict-set info 'lives lives))
         (Block new-info instrs)]
        [else
         (error "R1-reg/uncover-live-block unhandled" ast)]
        ))

    (define/public (uncover-live ast)
      (match ast
        [(Program info (CFG `((start . ,block))))
         (define new-block (uncover-live-block block (set 'rax 'rsp)))
         (Program info (CFG `((start . ,new-block))))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph

    (define/public (build-interference-instr live-after G)
      (lambda (ast)
        (verbose "build-interference-instr " ast live-after)
	(match ast
          [(Instr 'movq (list s d))
           (for ([v live-after])
		 (for ([d (free-vars d)])
                   (cond [(equal? (Var v) s)
                          (verbose "same source " s)]
                         [(equal? v d)
                          (verbose "skip self edge on " d)]
                         [else
                          (verbose "adding edge " d v)
                          (add-edge! G d v)])
                   ))
	    ast]
          [else
           (for ([v live-after])
             (for ([d (write-vars ast)])
               (cond [(equal? v d)
                      (verbose "skip self edge on " d)]
                     [else
                      (verbose "adding edge " d v)
                      (add-edge! G d v)])))
           ast])))

    (define/public (build-interference-block ast G)
      (match ast
        [(Block info ss)
         (define lives (dict-ref info 'lives))
         ;; pull off the live-before of the first instruction.
         (define live-afters (cdr lives))
         (define new-ss (for/list ([inst ss] [live-after live-afters])
                          ((build-interference-instr live-after G) inst)))
         (define new-info (dict-remove info 'lives))
         (Block new-info new-ss)]
        [else (error "R1-reg/build-interference-block unhandled" ast)]
        ))
         
    (define/public (build-interference ast)
      (verbose "build-interference " ast)
      (match ast
        [(Program info (CFG cfg))
         (define locals (dict-keys (dict-ref info 'locals-types)))
         (define G (undirected-graph '()))
         (for ([v locals])
           (add-vertex! G v))
         
         (define new-CFG
           (for/list ([(label block) (in-dict cfg)])
             (cons label (build-interference-block block G))))
             
         (print-dot G "./interfere.dot")
         (define new-info (dict-set info 'conflicts G))
         (Program new-info (CFG new-CFG))]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-move-graph : pseudo-x86* -> pseudo-x86*
    ;; *annotate program with move graph

    (define (location? arg)
      (match arg
        [(Var x) #t]
        [(Reg r) #t]
        [else #f]))

    (define (location-name arg)
      (match arg
        [(Var x) x]
        [(Reg r) r]))

    (define/public (build-move-graph-instr G)
      (lambda (ast)
	(match ast
          [(Instr 'movq (list s d))
           #:when (and (location? s) (location? d))
           (if use-move-biasing
               (add-edge! G (location-name s) (location-name d))
               '())
           ast]
          [else ast])))
    
    (define/public (build-move-block ast MG)
      (match ast
        [(Block info ss)
         (define new-ss
           (if use-move-biasing
               (for/list ([inst ss])
                        ((build-move-graph-instr MG) inst))
               ss))
         (Block info new-ss)]
        [else
         (error "R1-reg/build-move-block unhandled" ast)]
        ))
      
    (define/public (build-move-graph ast)
      (match ast
        [(Program info (CFG cfg))
         (define MG (undirected-graph '()))
         (for ([v (dict-keys (dict-ref info 'locals-types))])
           (add-vertex! MG v))
         (define new-CFG
           (for/list ([(label block) (in-dict cfg)])
             (cons label (build-move-block block MG))))
         (print-dot MG "./move.dot")
         (define new-info (dict-set info 'move-graph MG))
         (Program new-info (CFG new-CFG))]
        ))
    

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86
    ;; Replaces variables with registers and stack locations
    ;; using graph coloring based on Suduko heuristics.
    ;; This pass encompasses assign-homes.

    (define/public (valid-color c v unavail-colors info)
      (not (set-member? unavail-colors c)))
      
    (define/public (choose-color v unavail-colors move-related info)
      (copious "choose-color" v unavail-colors move-related)
      (define n (num-registers-for-alloc))
      (define biased-selection
        (for/first ([c move-related]
                    #:when (valid-color c v unavail-colors info))
          c))
      (copious "biased-selection" biased-selection)
      (define unbiased-selection     
        (for/first ([c (in-naturals)]
                    #:when (valid-color c v unavail-colors info))
          c))
      (copious "unbiased-selection" unbiased-selection)
      (cond [(and biased-selection
                  (or (< biased-selection n) (>= unbiased-selection n)))
             (copious "move-biased, for ~a chose ~a" v biased-selection)
             biased-selection]
            [else
             unbiased-selection]))

    (inherit variable-size)

    ;; Take into account space for the callee saved registers.
    (define/override (first-offset num-used-callee)
      (+ (super first-offset num-used-callee)
         (* num-used-callee (variable-size))))

    (define/public (init-num-spills)
      0)

    (define/public (update-num-spills spills c)
      (cond [(>= c (num-registers-for-alloc))
             (add1 spills)]
            [else
             spills]
            ))

    (define/public (record-num-spills info num-spills)
      (dict-set info 'num-spills num-spills))
    
    (define/public (color-graph IG MG info) ;; DSATUR algorithm
      (define locals (dict-keys (dict-ref info 'locals-types)))
      (define num-spills (init-num-spills))
      (define unavail-colors (make-hash)) ;; pencil marks
      (define (compare u v) ;; compare saturation
	(>= (set-count (hash-ref unavail-colors u))
	    (set-count (hash-ref unavail-colors v))))
      (define Q (make-pqueue compare))
      (define pq-node (make-hash)) ;; maps vars to priority queue nodes
      (define color (make-hash)) ;; maps vars to colors (natural nums)
      ;; color the registers to themselves
      (for ([r registers-for-alloc])
        (hash-set! color r (register->color r)))
      (for ([x locals])
	   ;; mark neighboring register colors as unavailable
	   (define adj-reg
	      (filter (lambda (u) (set-member? registers u))
		      (get-neighbors IG x)))
	   (define adj-colors (list->set (map register->color adj-reg)))
	   (hash-set! unavail-colors x adj-colors)
	   ;; add variables to priority queue
	   (hash-set! pq-node x (pqueue-push! Q x)))
      ;; Graph coloring
      (while (> (pqueue-count Q) 0)
	     (define v (pqueue-pop! Q))
             (define move-related 
               (sort (filter (lambda (x) (>= x 0)) 
                             (map (lambda (k) (hash-ref color k -1)) 
                                  (get-neighbors MG v)))
                     <))
	     (define c (choose-color v (hash-ref unavail-colors v)
				     move-related info))
             (verbose "color of ~a is ~a" v c)
             (set! num-spills (update-num-spills num-spills c))
	     (hash-set! color v c)
             ;; mark this color as unavailable for neighbors
	     (for ([u (in-neighbors IG v)])
		  (when (not (set-member? registers u))
			(hash-set! unavail-colors u
				   (set-add (hash-ref unavail-colors u) c))
			(pqueue-decrease-key! Q (hash-ref pq-node u)))))
      (values color num-spills))

    (define/public (identify-home num-used-callee c)
      (define n (num-registers-for-alloc))
      (cond
        [(< c n)
         (Reg (color->register c))]
        [else
         (copious "identify-home: stack: first offset"
                  (first-offset num-used-callee))
         (copious "color " c)
         (copious "num-registers" n)
         (Deref 'rbp (- (+ (first-offset num-used-callee)
                           (* (- c n) (variable-size)))))]))

    (define (callee-color? c)
      (and (< c (num-registers-for-alloc))
           (set-member? callee-save (color->register c))))
    
    (define/public (used-callee-reg locals color)
      (for/set ([x locals] #:when (callee-color? (hash-ref color x)))
        (color->register (hash-ref color x))))

    (define/public (num-used-callee locals color)
      (set-count (used-callee-reg locals color)))

    (define/public (allocate-registers ast)
      (match ast
        [(Program info (CFG G))
         (define locals (dict-keys (dict-ref info 'locals-types)))
         (define IG (dict-ref info 'conflicts))
         (define MG (dict-ref info 'move-graph))
         (define-values (color num-spills) (color-graph IG MG info))
         (define homes
           (for/hash ([x locals])
             (define home (identify-home (num-used-callee locals color)
                                         (hash-ref color x)))
             (copious "home of ~a is ~a" x home)
             (values x home)))
         (define new-CFG
           (for/list ([(label block) (in-dict G)])
             (cons label ((assign-homes-block homes) block))))
         (define info2 (record-num-spills info num-spills))
         (define info3 (dict-set info2 'used-callee
                                 (used-callee-reg locals color)))
         ;; The 'homes is for debugging purposes. -Jeremy
         (define info4 (dict-set info3 'homes
                                 (for/list ([(x home) (in-dict homes)])
                                   (cons x home))))
         ;; The 'colors is for debugging purposes. -Jeremy
         (define info5 (dict-set info4 'color
                                 (for/list ([(x c) (in-dict color)])
                                   (cons x c))))
         (define new-info
           (dict-remove-all info5 (list 'conflicts 'move-graph)))
         (Program new-info (CFG new-CFG))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/override (print-x86 e)
      (match e
        [(Program info (CFG G))
         (define spill-space (* (variable-size) (dict-ref info 'num-spills)))
         (define used-callee (set->list (dict-ref info 'used-callee)))
         (define save-callee-reg
           (for/list ([r used-callee])
             (format "\tpushq\t%~a\n" r)))
         (define restore-callee-reg
           (for/list ([r (reverse used-callee)])
             (format "\tpopq\t%~a\n" r)))
         (define callee-space (* (length used-callee) (variable-size)))
         (debug "print-x86 callee space: ~a" callee-space)
         (debug "print-x86 spill space: ~a" spill-space)
         (debug "print-x86 aligned: ~a" (align (+ callee-space spill-space) 16))
         (define stack-adj (- (align (+ callee-space spill-space) 16)
                              callee-space))
         (debug "print-x86 stack adjust: ~a" stack-adj)         
         (string-append
          (string-append*
           (for/list ([(label block) (in-dict G)])
             (string-append (format "~a:\n" (label-name label))
                            (print-x86-block block))))
          "\n"
          (format "\t.globl ~a\n" (label-name "main"))
          (format "~a:\n" (label-name "main"))
          (format "\tpushq\t%rbp\n")
          (format "\tmovq\t%rsp, %rbp\n")
          (string-append* save-callee-reg)
          (format "\tsubq\t$~a, %rsp\n" stack-adj)
          (format "\tjmp ~a\n" (label-name 'start))
          (format "~a:\n" (label-name 'conclusion))
          (format "\taddq\t$~a, %rsp\n" stack-adj)
          (string-append* restore-callee-reg)
          (format "\tpopq\t%rbp\n")
          (format "\tretq\n"))]
        ))

    )) ;; compile-reg-R1

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define reg-int-passes
  (let ([compiler (new compile-reg-R1)])
    `(
      ("uniquify"
       ,(lambda (p) (send compiler uniquify p))
       ,interp-R1
       ,type-check-R1)
      #;("partial-eval"
       ,(lambda (p) (send compiler partial-eval p))
       ,interp-R1)
      ("remove-complex-opera*"
       ,(lambda (p) (send compiler remove-complex-opera* p))
       ,interp-R1
       ,type-check-R1)
      ("explicate-control"
       ,(lambda (p) (send compiler explicate-control p))
       ,interp-C0
       ,type-check-C0)
      ("select-instructions"
       ,(lambda (p) (send compiler select-instructions p))
       ,interp-pseudo-x86-0)
      ("uncover-live"
       ,(lambda (p) (send compiler uncover-live p))
       ,interp-pseudo-x86-0)
      ("build-interference"
       ,(lambda (p) (send compiler build-interference p))
       ,interp-pseudo-x86-0)
      ("build-move-graph"
       ,(lambda (p) (send compiler build-move-graph p))
       ,interp-pseudo-x86-0)
      ("allocate-registers"
       ,(lambda (p) (send compiler allocate-registers p))
       ,interp-x86-0)
      ("patch-instructions"
       ,(lambda (p) (send compiler patch-instructions p))
       ,interp-x86-0)
      ("print x86"
       ,(lambda (p) (send compiler print-x86 p))
       #f)
      )))

