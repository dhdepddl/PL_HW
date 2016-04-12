#lang plai

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

(test/exn (string->sexpr 1) "expects argument of type <string>")
(test/exn (string->sexpr ".") "syntax error (bad contents)")
(test/exn (string->sexpr "{} {}") "bad syntax (multiple expressions)")


;; WAE abstract syntax trees
(define-type PWAE
  [num  (num number?)]
  [nlist (nl list?)]
  [add  (left PWAE?) (right PWAE?)]
  [sub  (left PWAE?) (right PWAE?)]
  [with (name symbol?) (init PWAE?) (body PWAE?)]
  [id   (name symbol?)]
  [poohadd (flist list?)]
  [poohsub (flist list?)])



; listof-number? : list -> boolean
; check whether if the input value is list or not
; and is list of number or not
(define (listof-number? l)
  (cond
    [(not (list? l)) #f]
    [(= (length (filter number? l)) (length l)) #t]
    [else #f]))

(test (listof-number? '(3 4 0 9)) #t)
(test (listof-number? 2) #f)
(test (listof-number? '(d v 7)) #f)
(test (listof-number? '(3 4 '(2 0))) #f)
(test (listof-number? (string->sexpr "{2 3 5}")) #t)



; parse-sexpr : sexpr -> WAE
;; to convert s-expressions into WAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(? listof-number?) (nlist sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(cons 'pooh rest)
     (cond
       [(and (symbol=? (last rest) '+) (>= (length rest) 2))
        (poohadd (map (lambda (se) (parse-sexpr se)) (drop-right rest 1)))]
       [(and (symbol=? (last rest) '-) (>= (length rest) 2))
        (poohsub (map (lambda (se) (parse-sexpr se)) (drop-right rest 1)))]
       [else (error 'parse "bad syntax: ~a" sexp)])]
    [(? symbol?) (id sexp)]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a WAE expression to a WAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))


(test (parse "{pooh 2 3 {+ 3 4} -}") (poohsub (list (num 2) (num 3) (add (num 3) (num 4)))))
(test (parse "{with {x {pooh {+ 5 1} 3 +}} {- x 3}}") 
      (with 'x (poohadd (list (add (num 5) (num 1)) (num 3))) (sub (id 'x) (num 3))))
(test (parse "i") (id 'i))
(test (parse "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}")
      (add (add (poohsub (list (num 1) (num 2))) (num 5)) (poohsub (list (num 3) (num 4)))))
(test (parse "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}")
      (poohadd (list (add (poohsub (list (num 1) (num 2))) (num 5)) (sub (num 3) (num 4)))))
(test (parse "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}")
      (poohadd (list (poohadd (list (poohsub (list (num 1) (num 2))) (num 5))) (poohsub (list (num 3) (num 4))))))
(test (parse "{+ {+ {- 1 2} 5} {- 3 4}}")
      (add (add (sub (num 1) (num 2)) (num 5)) (sub (num 3) (num 4))))
(test (parse "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}")
      (with 'x (poohsub (list (num 3) (num 4))) (poohadd (list (add (poohsub (list (num 1) (num 2))) (num 5)) (id 'x)))))
(test/exn (parse "{pooh +}") "parse: bad syntax: (pooh +)")


;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (type-case PWAE expr
    [num (n) expr]
    [nlist (l) expr]
    [add (l r) (add (subst l from to) (subst r from to))]
    [sub (l r) (sub (subst l from to) (subst r from to))]
    [id (name) (if (symbol=? name from) (nlist to) expr)]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]
    [poohadd (l) (poohadd (map (lambda (fwae) (subst fwae from to)) l))]
    [poohsub (l) (poohsub (map (lambda (fwae) (subst fwae from to)) l))]))


;bin-op : (number number -> number) (listof number or number) (listof number or number) -> (listof number))
;; applies a binary numeric function on all combinations of numbers from
;; the two input lists or numbers, and return the list of all of the results
(define (bin-op op ls rs)
  (define (helper l rs)
    ;; f : number -> number
    (define (f r)
      (op l r))
    (map f rs))
  (cond
    [(and (number? ls) (number? rs)) (op ls rs)]
    [(and (number? ls) (listof-number? rs)) (helper ls rs)]
    [(and (number? rs) (listof-number? ls)) (map (lambda (s) (op s rs)) ls)]
    [(and (listof-number? rs) (listof-number? ls))
     (if (null? ls)
         null
         (append (helper (first ls) rs) (bin-op op (rest ls) rs)))]
    [else (error 'bin-op "bad input")]))

(test (bin-op + 3 3) 6)
(test (bin-op + '(2) '(1)) '(3))
(test (bin-op - '(1 3) 5) '(-4 -2))
(test (bin-op - '(3 4) '(0 1 2)) '(3 2 1 4 3 2))
(test/exn (bin-op + 'v 3) "bin-op: bad input")


;; evaluates WAE expressions by reducing them to numbers
;; eval: PWAE -> list of number
(define (eval expr)
  (type-case PWAE expr
    [num (n) (cons n empty)]
    [nlist (l) l]
    [add (l r) (bin-op + (eval l) (eval r))]
    [sub (l r) (bin-op - (eval l) (eval r))]
    [with (bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [id (name) (error 'eval "free identifier: ~s" name)]
    [poohadd (l) (foldl bin-op + (eval (first l)) (map (lambda (pwae) (eval pwae)) (rest l)))]
    [poohsub (l) (foldl bin-op - (eval (first l)) (map (lambda (pwae) (eval pwae)) (rest l)))]))

; run : string -> listof number
;; evaluate a WAE program contained in a string
(define (run str)
  (eval (parse str)))

(test (run "{+ {2 1} {3 4}}") '(5 6 4 5))
(test (run "{+ {- {+ 1 3} 2} {10 -10}}") '(12 -8))
(test (run "{+ 3 7}") '(10))
(test (run "{- 10 {3 5}}") '(7 5))
(test (run "{+ {3 5 0} {- {1 4} {2 0}}}") '(2 4 5 7 4 6 7 9 -1 1 2 4))
(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))
(test (run "{with {x {- {8 4} 3}} {+ 2 x}}") '(7 3))
(test (run "{+ {4 2} {with {y {+ {2 1} 3}} {- y 1}}}") '(8 7 6 5))
(test/exn (run "{with {x y} {+ 3 x}}") "eval: free identifier: y")
(test/exn (run "{+ 3 {- 3 2 1}}") "parse: bad syntax: (- 3 2 1)")
(test/exn (run "{+ {2 3} {0 {- 3 2}}}") "parse: bad syntax: (0 (- 3 2))")