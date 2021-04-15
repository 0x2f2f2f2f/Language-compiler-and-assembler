#lang racket
;collaborated with Alexander Zhuang

;(require "PRIMPLSIMULATOR.rkt")
;(require "Q7.rkt")
(define ans empty)
(define cnt 0)
(define curfname 'main)
;store function templates for each function we come across, should be a list of lists
(define templates (make-hash))
(define funcnames empty)
; f(a1,b1) <- f(a2,b2) <- f(a3,b3) <- f(a4,b4)
; FS = 5
; SP += FS
; {x1,x2,x3,x4,x5}
; ARG_[function name]_[variable name]
; VAR_[function name]_[variable name]
(define (create-func-data name args vars)
  (begin
    (define allnames empty)
    (set! funcnames (cons name funcnames))
    (for ([i vars])
        (define varname (string->symbol (string-append 
                                        (symbol->string name) "_"
                                        (symbol->string (first i)))))
        (set! ans (cons (list 'data varname 0) ans))
        (set! allnames (cons (first i) allnames))
        ; temporarily initialize local vars to 0
        ; local var pointers change locations every time the function is run
    )
    (for ([arg args])
        (define argname (string->symbol (string-append
                                        (symbol->string name) "_" 
                                        (symbol->string arg))))
        (set! ans (cons (list 'data argname 0) ans))
        (set! allnames (cons arg allnames))
    )
    (if (not (= (length allnames) (length (set->list (list->set allnames)))))
        (error "duplicate")
        empty)
    (if (not (= (length funcnames) (length (set->list (list->set funcnames)))))
        (error "duplicate")
        empty)
  )
)

; Each stack frame is:
; prev FP location
; prev SP location / return address
; prev PC location
; local variables
; argument variables
; temp variable stack
(define (eval-aexp aexp)
  (if(list? aexp)
  (match (car aexp)
    ['+
     (begin
       (eval-aexp (second aexp))
       (eval-aexp (third aexp))
       (set! ans (cons (list 'add (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['*
     (begin
       (eval-aexp (second aexp))
       (eval-aexp (third aexp))
       (set! ans (cons (list 'mul (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['- (begin
       (eval-aexp (second aexp))
       (eval-aexp (third aexp))
       (set! ans (cons (list 'sub (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['div (begin
       (eval-aexp (second aexp))
       (eval-aexp (third aexp))
       (set! ans (cons (list 'div (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
        (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['mod (begin
       (eval-aexp (second aexp))
       (eval-aexp (third aexp))
       (set! ans (cons (list 'mod (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )
    ]
    (else (begin
        (define name (first aexp))
        (define vals (rest aexp))
        (for ([aexp vals])
          (eval-aexp aexp))
        (define cur  (hash-ref templates name))
        (define vars (first cur))
        (define args (second cur))
        ;find function template in templates to see if this ex
        (if (= (length vals) (length args)) empty (error "arguments"))
        (set! ans (cons (list 'move (list 1 'SP) 'FP) ans))
        (set! ans (cons (list 'move (list 2 'SP) 'SP) ans))
        (set! ans (cons (list 'add 'SP 'SP 1) ans))
        (set! ans (cons (list 'move 'FP 'SP) ans))
        (set! ans (cons (list 'add 'SP 'SP 3) ans))
        ; jsr at (2 'FP)
        (for ([arg args])
            (define argname (string->symbol (string-append 
                                        (symbol->string (first aexp)) "_"
                                        (symbol->string arg))))
            (set! ans (cons (list 'move (list 0 'SP) (list (- -4 (length args)) 'SP)) ans))
            (set! ans (cons (list 'move argname 'SP) ans))
            (set! ans (cons (list 'add 'SP 'SP 1) ans))
        )
        (for ([var vars])
          (define varname (string->symbol (string-append 
                                    (symbol->string (first aexp)) "_"
                                    (symbol->string (first var)))))
          (set! ans (cons (list 'move (list 0 'SP) (second var)) ans))
          (set! ans (cons (list 'move varname 'SP) ans))
          (set! ans (cons (list 'add 'SP 'SP 1) ans))
        )
      ;Initialize ARGS in stack frame
        
        (set! ans (cons (list 'jsr (list 2 'FP) name) ans))
      )
    )
  )
  (begin
    (set! ans (cons (list 'move (list 0 'SP)
                                  (if (symbol? aexp)
                                     (list 0 (string->symbol
                                      (string-append (symbol->string curfname) "_" (symbol->string aexp))))
                                     aexp)
                                  )ans))
     (set! ans (cons (list 'add 'SP 'SP 1) ans))
            )
))

(define (eval-bexp bexp)
  (if(list? bexp)
  (match (car bexp)
    ['= (begin
       (eval-aexp (second bexp))
       (eval-aexp (third bexp))
       (set! ans (cons (list 'equal (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['> (begin
       (eval-aexp (second bexp))
       (eval-aexp (third bexp))
       (set! ans (cons (list 'gt (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['< (begin
       (eval-aexp (second bexp))
       (eval-aexp (third bexp))
       (set! ans (cons (list 'lt (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['<= (begin
       (eval-aexp (second bexp))
       (eval-aexp (third bexp))
       (set! ans (cons (list 'le (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['>= (begin
       (eval-aexp (second bexp))
       (eval-aexp (third bexp))
       (set! ans (cons (list 'gt (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
      )]
    ['and (begin
       (if(empty? (cdr bexp)) empty (eval-bexp (second bexp)))
       (for ([be (cdr (cdr bexp))])
         (eval-bexp be)
         (set! ans (cons (list 'land (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
         (set! ans (cons (list 'add 'SP 'SP -1) ans)))
      )]
    ['not (begin
       (eval-bexp (second bexp))
       (set! ans (cons (list 'lnot (list -1 'SP) (list -1 'SP)) ans))
      )]
    (else (begin
       (if(empty? (cdr bexp)) empty (eval-bexp (second bexp)))
       (for ([be (cdr (cdr bexp))])
         (eval-bexp be)
         (set! ans (cons (list 'lor (list -2 'SP) (list -2 'SP) (list -1 'SP)) ans))
         (set! ans (cons (list 'add 'SP 'SP -1) ans)))
      ))
    )
  (begin (set! ans (cons (list 'move (list 0 'SP) (if(eq? bexp 'true) true false)) ans))
            (set! ans (cons (list 'add 'SP 'SP 1) ans))
            )
  )
  )
(define (eval-stmt stmt)
    (match (first stmt)
      ['print
       (if(string? (second stmt))
          (set! ans (cons (list 'print-string (second stmt)) ans))
          (begin
            (eval-aexp (second stmt))
            (set! ans (cons (list 'print-val (list -1 'SP)) ans))
            (set! ans (cons (list 'add 'SP 'SP -1) ans))
           )
          )]
      ['set
       (begin
         (eval-aexp (third stmt))
         (set! ans (cons (list 'move (list 0 (string->symbol (string-append (symbol->string curfname) "_" (symbol->string (second stmt)))))
                               (list -1 'SP)) ans))
         (set! ans (cons (list 'add 'SP 'SP -1) ans))
       )
       ]
      ['seq
       (for ([i (rest stmt)])
         (eval-stmt i))]
      ['iif
       (begin
         (eval-bexp (second stmt))
         (define tmp cnt)
         (set! cnt (+ 3 cnt))
         (set! ans (cons (list 'branch (list -1 'SP) (string->symbol(string-append "LABEL" (number->string tmp)))) ans))
         (set! ans (cons (list 'jump (string->symbol(string-append "LABEL" (number->string (add1 tmp))))) ans))
         (set! ans (cons (list 'label (string->symbol(string-append "LABEL" (number->string tmp)))) ans))
         (set! ans (cons (list 'add 'SP 'SP -1) ans))
         (eval-stmt (third stmt))
         (set! ans (cons (list 'jump (string->symbol(string-append "LABEL" (number->string (+ 2 tmp))))) ans))
         (set! ans (cons (list 'label (string->symbol(string-append "LABEL" (number->string (add1 tmp))))) ans))
         (set! ans (cons (list 'add 'SP 'SP -1) ans))
         (eval-stmt (fourth stmt))
         (set! ans (cons (list 'label (string->symbol(string-append "LABEL" (number->string (+ 2 tmp))))) ans))
         )]
      ['skip
       (void)
       ]
       ['return (begin
          (eval-aexp (second stmt))
          (set! ans (cons (list 'move (list -1 'FP) (list -1 'SP)) ans))
          (set! ans (cons (list 'move 'SP 'FP) ans))
          (set! ans (cons (list 'move 'FP (list 0 'FP)) ans))
          (if (eq? curfname 'main)
              (void)
              (set! ans (cons (list 'jump (list 2 'SP)) ans)))
        )
        ]
      (else (begin
       (define tmp cnt)
       (set! cnt (+ cnt 3))
       (set! ans (cons (list 'label (string->symbol(string-append "LABEL" (number->string tmp)))) ans))
       (eval-bexp (second stmt))
       (set! ans (cons (list 'branch (list -1 'SP) (string->symbol(string-append "LABEL" (number->string (add1 tmp))))) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
       (set! ans (cons (list 'jump (string->symbol(string-append "LABEL" (number->string (+ 2 tmp))))) ans))
       (set! ans (cons (list 'label (string->symbol(string-append "LABEL" (number->string (add1 tmp))))) ans))
       (set! ans (cons (list 'add 'SP 'SP -1) ans))
       (for ([i (rest (rest stmt))])
         (eval-stmt i)
         )
       (set! ans (cons (list 'jump (string->symbol(string-append "LABEL" (number->string tmp)))) ans))
       (set! ans (cons (list 'label (string->symbol(string-append "LABEL" (number->string (+ 2 tmp))))) ans))
      )
      )
    )
 )

; (fun (id id ...) (vars [(id int) ...] stmt ...))
; Stack frame must have:
; prev stack frame location
; argument variables
; local variables
; return address
; temp 

; Each stack frame is:
; prev FP location
; prev SP location / return address
; prev PC location
; local variables
; argument variables
; temp variable stack

(define (compile-simpl funcs)
    (set! ans empty)
    (set! cnt 0)
  (set! funcnames empty)
  (define cnt2 0)
  (hash-clear! templates)
    (define maininst empty) ; when we see the main function, we store it and come back later
  (for ([func funcs])
    (if(hash-has-key? templates (first (second func)))
       (error "duplicate")
       (hash-set! templates (first (second func)) (list (second(third func)) (rest (second func))))
    ))
    (for ([func funcs])
        (if (eq? (first (second func)) 'main)
            (begin (set! maininst func) (set! cnt2 (add1 cnt2)))
            (compile-fun-body (rest func) #f)))
    (define temp (cons (list 'label 'END)
            (cons (list 'data 'SP 'END)
            (cons (list 'data 'FP 'END) ans))))
  (if(> cnt2 1) (error "duplicate") empty)
    (if (empty? maininst) ;; Compiles the main function if it was given
        empty ;; if no main function, dont even generate instructions @847
        (begin
            (set! ans empty)
            (compile-fun-body (rest maininst) #t)
            (append  (reverse ans) (reverse temp))))
)

(define (compile-fun-body s-expr ismain)
    (set! curfname (first (first s-expr)))
    (set! ans (cons (list 'label (first (first s-expr))) ans))
    (define explst (rest (rest (second s-expr))))
    (define len (length explst))
    (define cnt 0)
  (hash-set! templates (first (first s-expr)) (list (second (second s-expr)) (rest (first s-expr))))
    (if (eq? #t ismain)
        (for ([var (second (second s-expr))])
            (define varname (string->symbol (string-append 
                                        (symbol->string (first (first s-expr))) "_"
                                        (symbol->string (first var)))))
            (set! ans (cons (list 'move (list 0 'SP) (second var)) ans))
            (set! ans (cons (list 'move varname 'SP) ans))
            (set! ans (cons (list 'add 'SP 'SP 1) ans))
        ) (void))
    (for ([stmt explst])
        (if (and (= cnt (- len 1)) (not (eq? (first stmt) 'return)))
            (error "return")
            (eval-stmt stmt))
        (set! cnt (add1 cnt)))
  (if (eq? #t ismain) (set! ans (cons (list 'halt) ans)) (void))
    (create-func-data (first (first s-expr)) (rest (first s-expr)) (second (second s-expr)))
  )
;(define test (compile-simpl (list
;'(fun (f c d) (vars [(a 10) (b 1)]
;                    (set a (+ a c))
;                    (set b (+ b d))
;                    (return (+ a b))))
;'(fun (main) (vars [] (print (f 1 2)) (return (f 1 2)))))))

;(define test2 (compile-simpl '(
;(fun (countdown n)
;  (vars [(result 0)]
;    (print n)
;    (print "\n")
;    (iif (> n 0)
;         (set result (countdown (- n 1)))
;         (skip))
;    (return result)))
;(fun (main) 
;  (vars [(n 10)] 
;    (return (countdown n)))))))
;(define test3 (compile-simpl '(
;                               (fun (f n) (vars [] (set n (+ (- 10 2) (mod 2 3)))(return n)))
;                               (fun (g m) (vars [] (set m (+ (- 10 2) (mod 2 3)))(return m)))
;                               (fun (main) (vars[(a 1) (b 2) (x 0) (y 0)]
;                                                (set x (f a))
;                                                (set y (g b))
;                                                (print (+ a y))
;                                                (return 0)
;                                                )) 
;                               )))
;(define test4 (compile-simpl '(
;                               (fun (f n) (vars []  (while(not(= n 0))
;                                                      (set n (- n 1))
;                                                )
;                                                (return n)))
;                               (fun (main) (vars[(ret 5)]
;                                                (while(not(= ret 0))
;                                                      (set ret (f ret))
;                                                      (print ret)
;                                                )
;                                                (return 0)))
;                               )))
;(define test5 (compile-simpl '((fun(main)(vars[] (return (f 0))))
;                               )))
;(define test6 (compile-simpl '((fun(main)(vars[(a 0) (a 1)](return 0)))
;                               )))
;(define test7 (compile-simpl '(
;                              (fun (f a) (vars [] (return (+ a 1))))
;                              (fun (g b) (vars [] (return (+ b 2))))
;                              (fun (main) (vars [(x 0)] (iif (= x 0) (set x (f x)) (set x (g x))) (print x) (return 0)))
;                              )))
;(define test8 (compile-simpl '(
;                              (fun (f a) (vars [] (return (+ a 1))))
;                              (fun (g b) (vars [] (return (+ b 2))))
;                              (fun (main) (vars [(x 1)] (iif (= x 0) (skip) (set x (g x))) (print x) (return 0)))
;                              )))
;(define test9 (compile-simpl '(
;                               (fun (f a) (vars [] (return 0)))
;                               (fun (fa b) (vars [] (return 0)))
;                               (fun (g f) (vars [] (return 0)))
;                               (fun (gf c) (vars [] (return 0)))
;                               (fun (main) (vars [] (return 0)))
;                               (fun (main) (vars [] (return 0)))
;                               (fun (main) (vars [] (return 0)))
;                               )))
;(define test9 (compile-simpl '(
;                               (fun (main) (vars [(a 1) (a 2)] (return 0)))
;                               )))
;(define test9 (compile-simpl '(
;                               (fun (f b) (vars [(a 1)] (return (g a))))
;                               (fun (g a) (vars [] (return 0)))
;                               )))
;(define (run-test lst) (load-primp (primpl-assemble lst)) (run-primp))
