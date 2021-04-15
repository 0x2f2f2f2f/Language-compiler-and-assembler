#lang racket
(define ht (make-hash))
(define vis (make-hash))
(define type (make-hash))
(define symbols empty)
(define ans empty)
(define finalans empty)
(define sz 0)

;data = 3, const = 2, label = 1
(define (symbol-find expr)
  ;(display expr)(display #\space)(display sz)(display #\newline)
  (if(list? expr)
  (match (car expr)
    ['halt
     (begin
       (set! sz (add1 sz))
       (set! ans (cons 0 ans))
       empty
       )
     ]
    ['lit
     (begin
       (set! sz (add1 sz))
       (set! ans (cons (second expr) ans))
       empty
      )]
    ['const
     (if(hash-has-key? ht (second expr))
        (error "duplicate variable")
     (begin
       (hash-set! ht (second expr) (third expr))
       (hash-set! type (second expr) 2)
       (set! symbols (cons (second expr) symbols))
       empty
      )
     )]
    ['data
     (if(hash-has-key? ht (second expr))
        (error "duplicate variable")
     (begin
       (hash-set! type (second expr) 3)
       (hash-set! ht (second expr) sz)
       (set! symbols (cons (second expr) symbols))
       (if(list? (third expr))
          (if(= (length (third expr)) 1)
             (begin
             (set! ans (cons (third expr) ans))
             (set! sz (add1 sz))
             )
          (begin
            (set! sz (+ sz (first(third expr))))
            (for ([i (first(third expr))])
              (set! ans (cons (second(third expr)) ans))
              )
            )
          )
          (begin
            (set! sz (sub1(+ sz (length(rest expr)))))
            (for ([i (rest (rest expr))])
             (set! ans (cons i ans)))
          )
         )
       empty
      ))]
    ['label
     (hash-set! type (second expr) 1)
      (if(hash-has-key? ht (second expr))
        (error "duplicate variable")
     (begin
       (hash-set! ht (second expr) sz)
       empty
      )
     )]
    [x
     (begin
       (set! sz (add1 sz))
       (set! ans (cons expr ans))
       empty
      )]
  )
  (begin
       (set! sz (add1 sz))
       (set! ans (cons expr ans))
       empty ))
) 
(define (resolve singleinstr)
  ;(display singleinstr)(display #\newline)
  (begin
    (hash-set! vis singleinstr #t)
   (cond
     [(and (list? singleinstr) (not(hash-has-key? type (first singleinstr)))) (first singleinstr)]
     [(and (hash-has-key? vis singleinstr) (and (hash-has-key? ht (hash-ref ht singleinstr)) (symbol? (hash-ref ht (hash-ref ht singleinstr))))) (error "circular reference")]
     [(not(hash-has-key? ht singleinstr)) (error "undefined variable")]
     [(number? (hash-ref ht singleinstr)) (hash-ref ht singleinstr)]
     [(symbol? (hash-ref ht singleinstr)) (hash-set! ht singleinstr (resolve (hash-ref ht singleinstr)))]
   )
  )
 )
(define (comp instr)
  (begin
    (for ([i instr])(symbol-find i))
   (for ([i symbols])
     (if(not(hash-has-key? vis i)) (resolve i) empty)
   )
   ;(for([i symbols])(display i)(display #\space)(display (hash-ref ht i))(display #\newline))
   (set! ans (reverse ans))
   (for ([i ans]) (set! finalans (cons (replace i) finalans)))
   empty
  )
)
(define (resolve-helper val)
  (cond
    [(symbol? val)(hash-ref ht val)]
    [(number? val) val]
    (else (resolve-helper (first val)))))
(define (resolve-dest instr)
  (cond
    [(and (symbol? instr) (not (hash-has-key? ht instr))) (error "undefined variable")]
    [(and (symbol? instr) (= (hash-ref type instr) 1)) (error "incorrect")]
    [(and (list? instr) (and (= (length instr) 1)(symbol? (first instr)))) (error "incorrect")]
    [(and (symbol? instr) (and (hash-has-key? ht instr) (= (hash-ref type instr) 2))) (error "incorrect")]
    (else
     (cond
       [(number? instr) instr]
       [(symbol? instr) (list (resolve-helper instr))]
       [(and (list? instr) (= (length instr) 1)) instr]
       (else (list (resolve-helper (first instr))(list (resolve-helper (second instr)))))
       )
     )
  )
)
(define (resolve-opd instr)
   ;(display instr)(display #\newline)
   (cond
      [(number? instr) instr]
      [(and (list? instr) (and (= (length instr) 1) (symbol? (first instr)))) (error "incorrect")]
      [(and (symbol? instr) (not(hash-has-key? ht instr))) (error "undefined variable")]
      [(symbol? instr) (if(or (= (hash-ref type instr) 1) (= (hash-ref type instr) 3)) (list (resolve-helper instr)) (resolve-helper instr))]
      [(and (list? instr) (= (length instr) 1)) (resolve-helper instr)]
      (else (list (resolve-helper (first instr))(list (resolve-helper (second instr)))))
      )
  )
(define (resolve-opd-helper instr)
   ;(display instr)(display #\newline)
   (cond
      [(number? instr) instr]
      [(and (symbol? instr) (not(hash-has-key? ht instr))) (error "undefined variable")]
      [(symbol? instr) (if(or (= (hash-ref type instr) 1) (= (hash-ref type instr) 3)) (list (resolve-helper instr)) (resolve-helper instr))]
      [(and (list? instr) (= (length instr) 1)) (resolve-helper instr)]
      (else (list (resolve-helper (first instr))(list (resolve-helper (second instr)))))
      )
  )
(define (replace instr)
  ;(display instr)(display #\newline)
  (cond
    [(and (symbol? instr)(not(hash-has-key? ht instr))) (error "undefined variable")]
    [(symbol? instr) (hash-ref ht instr)]
    [(number? instr) instr]
    [(and (list? instr) (= (length instr) 1)) instr]
  (else
   (match (car instr)
    ['lnot (list (first instr) (resolve-dest (second instr)) (resolve-opd (third instr)))]
    ['jump (list (first instr) (resolve-opd-helper (second instr)))]
    ['branch (list (first instr) (resolve-opd-helper (second instr)) (resolve-opd-helper (third instr)))]
    ['move (list (first instr) (resolve-dest (second instr)) (resolve-opd (third instr)))]
    ['print-val (list (first instr) (resolve-opd (second instr)))]
    ['print-string instr]
    (else (list (first instr) (resolve-dest (second instr)) (resolve-opd (third instr)) (resolve-opd (fourth instr))))
    )
   )
  )
 )
(define (primpl-assemble instr)
  (begin
    (hash-clear! ht)
    (hash-clear! vis)
    (hash-clear! type)
    (set! symbols empty)
    (set! ans empty)
    (set! finalans empty)
    (set! sz 0)
    (comp instr)
   ;(display ans)(display #\newline)
    (reverse finalans)
  )
)
;(primpl-assemble '((add a b c)))
;PRIMPL: undefined variable
;(primpl-assemble '(a))
;PRIMPL: undefined variable
(primpl-assemble '((data x 12) (add x x 12)))
;PRIMPL: '(12 (add (0) (0) 12))
(primpl-assemble '((const a 1)(const b a)(const c a) a b c))
;PRIMPL: '(1 1 1)
(primpl-assemble '((data a b) (data b c) (data c a)))
;PRIMPL: '(1 2 0)
(primpl-assemble '((data a b)(data b a)))
;PRIMPL: '(1 0)
(primpl-assemble '((add b a a)(data a (3 5))(data b 1 2 3 4)(label x)))
;PRIMPL: '((add (4) (1) (1)) 5 5 5 1 2 3 4)
(primpl-assemble '((const x 10)(data y (3 x))))
;PRIMPL: '(10 10 10)
(primpl-assemble '((label L1)(const c d)(lit L1)(const d 3)(data x 2) (data y x)(data z (3 x))(data k 8 9 2)(add (3 y) (y (2)) (x (10)))))
;PRIMPL: '(0 2 1 1 1 1 8 9 2 (add (3 (2)) (2 (2)) (1 (10))))
(primpl-assemble '((label LOOP-TOP)(gt (c c) (c c) (c c)) (branch (c c) (c c)) (jump (c c)) (const c 8) (data TMP1 0) ))
;PRIMPL: '((gt (8 (8)) (8 (8)) (8 (8))) (branch (8 (8)) (8 (8))) (jump (8 (8))) 0)
(primpl-assemble '((data x 9)(lit x)))
;PRIMPL: '(9 0)
(primpl-assemble '((lit A) (lit B) (lit C) (const A (1)) (data B (2)) (label C)))
;PRIMPL: '(1 3 4 (2))
(primpl-assemble '((const a 1) a a))
;PRIMPL: '(1 1)
(primpl-assemble '((data X 10 10) (const Y X) Y))
;PRIMPL: '(10 10 0)
(primpl-assemble '((const a 1) (const b 2)(add (a (b)) (a (b)) (a (b)))))
;PRIMPL: '((add (1 (2)) (1 (2)) (1 (2))))
;(primpl-assemble '((const x 5)(add x u 2)(data u x)))
;PRIMPL: incorrect
;(primpl-assemble '((const a a)))
;PRIMPL: circuluar reference
;(primpl-assemble '((const x 5)(data x 0)))
;PRIMPL: duplicate error
;(primpl-assemble '((add (X) 145 1)(data X 0)))
;PRIMPL: incorrect
;(primpl-assemble '((label START)(add START START START)))
;PRIMPL: incorrect
;(primpl-assemble '((const C 1)(add C 0 0)))
;PRIMPL: incorrect           
;(primpl-assemble '((const a 1) (const a 2)))
;PRIMPL: circular error
;(primpl-assemble '((cons a 1) b))
;PRIMPL: undefined variable
