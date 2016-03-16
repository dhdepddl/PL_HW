#lang plai

;for basic

;define type WAE with variant_id num, add, sub
;num with field n of type number
;add with field lhs, rhs of type WAE
;sub with field lhs, rhs of type WAE
;with with field name of type symbol, named-expr, body of type WAE
;id with field name of type symbol
(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?) (named-expr WAE?) (body WAE?)]
  [id (name symbol?)])


;parse : sexp -> WAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(? symbol?) (id sexp)]
    [else (error 'parse "bad syntax: ~a" sexp)]))

(test (parse '{+ 3 {- 5 4}}) (add (num 3) (sub (num 5) (num 4))))
(test (parse '{with {x 3} {+ x x}}) (with 'x (num 3) (add (id 'x) (id 'x))))
(test/exn (parse "a") "bad syntax: a")


;subst : WAE symbol num -> WAE
(define (subst wae x val)
  (cond
    [(or (not (WAE? wae)) (or (not (symbol? x)) (not (number? val))))
     (error 'subst "Wrong type")]
    [else
     (type-case WAE wae
       [num (n) wae]
       [add (l r) (add (subst l x val) (subst r x val))]
       [sub (l r) (sub (subst l x val) (subst r x val))]
       [with (y i b) (with y
                           (subst i x val)
                           (if (symbol=? y x) b
                               (subst b x val)))]
       [id (s) (if (symbol=? s x) (num val) wae)])]))

(test (subst (add (id 'x) (num 3)) 'x 5) (add (num 5) (num 3)))
(test (subst (sub (num 5) (id 'x)) 'x 2) (sub (num 5) (num 2)))
(test (subst (with 'x (num 9) (num 2)) 'x 8) (with 'x (num 9) (num 2)))
(test (subst (with 'x (num 5) (add (id 'x) (id 'y))) 'y 3) (with 'x (num 5) (add (id 'x) (num 3))))
(test/exn (subst 3 5 4) "Wrong type")


;interp : WAE -> number
(define (interp wae)
  (cond
    [(not (WAE? wae)) (error 'interp "Wrong type - not WAE: ~a" wae)]
    [else
     (type-case WAE wae
       [num (n) n]
       [add (l r) (+ (interp l) (interp r))]
       [sub (l r) (- (interp l) (interp r))]
       [with (x i b) (interp (subst b x (interp i)))]
       [id (s) (error 'interp "free variable")])]))

(test (interp (add (num 5) (sub (num 7) (num 2)))) 10)
(test (interp (with 'x (num 3) (add (id 'x) (id 'x)))) 6)
(test/exn (interp 3) "Wrong type - not WAE: 3")
(test/exn (interp (id 'x)) "free variable")


;for HW#3

;all-ids : WAE -> list of symbol
;takes WAE and produces a list of all symbols in the given WAE
;allow duplicate and not sorted
(define (all-ids wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (list* (append (all-ids l) (all-ids r)))]
    [sub (l r) (list* (append (all-ids l) (all-ids r)))]
    [with (x i b)
          (cons x (list* (append (all-ids i) (all-ids b))))]
    [id (s) (list s)]))

(test (all-ids (parse '{with {x {+ 3 4}} {- x 2}})) '(x x))


;symbol<? : symbol1 symbol2 -> boolean
;return true if string(symbol1) < string(symbol2)
(define (symbol<? a b)
  (string<? (symbol->string a) (symbol->string b)))

(test (symbol<? 'o 'b) #f)


;srt-rmdupl : list of symbol -> list of symbol
;takes list of symbol and produces a list of symbols
;with sorted order and removing duplicated symbols
(define (srt-rmdupl l)
  (sort (remove-duplicates l) symbol<?))



;#1
;free-ids : WAE -> list of symbol
;takes WAE and produces a list of symbols for each free identifier in the given WAE
;return error if the input value is not of type WAE
(define (free-ids wae)
  (cond
    [(not (WAE? wae)) (error 'free-ids "Wrong type - not WAE: ~a" wae)]
    [else
     (type-case WAE wae
       [num (n) empty]
       [add (l r) (srt-rmdupl (list* (append (free-ids l) (free-ids r))))]
       [sub (l r) (srt-rmdupl (list* (append (free-ids l) (free-ids r))))]
       [with (x i b)
             (srt-rmdupl (list* (append (free-ids i) (remove x (free-ids b)))))]
       [id (s) (list s)])]))

(test/exn (free-ids 3) "Wrong type - not WAE: 3")
(test (free-ids (id 'x)) '(x))
(test (free-ids (num 5)) empty)
(test (free-ids (parse '{+ {- 3 {with {x 4} {+ y x}}} {with {a {+ x 3}} {- z {+ a x}}}})) '(x y z))
(test (free-ids (parse '{with {x {with {y 5} {+ y x}}}
                              {with {a {+ 3 4}}
                                    {+ a x}}})) '(x))


;#2
;binding-ids : WAE -> list of symbol
;takes WAE and produces a list of symbols for each binding identifier in the given WAE
;return error if the input value is not of type WAE
(define (binding-ids wae)
  (cond
    [(not (WAE? wae)) (error 'binding-ids "Wrong type - not WAE: ~a" wae)]
    [else 
     (type-case WAE wae
       [num (n) empty]
       [add (l r) (srt-rmdupl (list* (append (binding-ids l) (binding-ids r))))]
       [sub (l r) (srt-rmdupl (list* (append (binding-ids l) (binding-ids r))))]
       [with (x i b) (srt-rmdupl (list* (append (binding-ids i) (cons x (binding-ids b)))))]
       [id (s) empty])]))

(test/exn (binding-ids (+ 3 3)) "Wrong type - not WAE: 6")
(test (binding-ids (id 'x)) '())
(test (binding-ids (num 5)) empty)
(test (binding-ids (parse '{+ {- 3 {with {x 4} {+ y x}}} {with {a {+ x 3}} {- z {+ a x}}}})) '(a x))
(test (binding-ids (parse '{with {x {with {y 5} {+ y x}}}
                              {with {a {+ 3 4}}
                                    {+ a x}}})) '(a x y))


;#3
;bound-ids : WAE -> list of symbol
;takes WAE and produces a list of symbols for each bound identifier in the given WAE
;return error if the input value is not of type WAE
(define (bound-ids wae)
  (cond
    [(not (WAE? wae)) (error 'bound-ids "Wrong type - not WAE: ~a" wae)]
    [else 
     (type-case WAE wae
       [num (n) empty]
       [add (l r) (srt-rmdupl (list* (append (bound-ids l) (bound-ids r))))]
       [sub (l r) (srt-rmdupl (list* (append (bound-ids l) (bound-ids r))))]
       [with (x i b)
             (cond
               [(and (member x (all-ids b)) (not (member x (binding-ids b))))
                (srt-rmdupl (list* (append (bound-ids i) (cons x (bound-ids b)))))]
               [else (srt-rmdupl (list* (append (bound-ids i) (bound-ids b))))])]
       [id (s) empty])]))

(test/exn (bound-ids 'a) "Wrong type - not WAE: a")
(test (bound-ids (id 'x)) '())
(test (bound-ids (num 5)) empty)
(test (bound-ids (parse '{+ {- 3 {with {x 4} {+ y x}}} {with {a {+ x 3}} {- z {+ a x}}}})) '(a x))
(test (bound-ids (parse '{with {x {with {y 5} {+ y x}}}
                              {with {a {+ 3 4}}
                                    {+ a x}}})) '(a x y))
(test (bound-ids (parse '{with {x
                                {with {x 5} {+ 3 4}}} {- 5 2}})) '())
(test (bound-ids (parse '{with {x {with {x 3} {+ x x}}} {- 7 2}})) '(x))

