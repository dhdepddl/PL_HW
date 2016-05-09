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

; uniq?: list-of-symbol -> bool
; for given list of symbols,
; return true if the list does not have duplicate symbols
; and return false if the list has duplicate symbols
; and return error if input is not a list or not a list of symbols
(define (uniq? x)
  (cond
    [(not (list? x)) (error 'uniq? "Not a list")]
    [(not (= (length (filter symbol? x)) (length x))) (error 'uniq? "Not a list of symbols")]
    [else
     (for/and ([i x]) (andmap (lambda (j) (not (symbol=? i j))) (remove i x)))]))

(test (uniq? '(e r t f name fun)) #t)
(test (uniq? '(e r t e)) #f)
(test/exn (uniq? 3) "uniq?: Not a list")
(test/exn (uniq? '(1 2 3)) "uniq?: Not a list of symbols")


(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (param list?)
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (arg-expr list?)]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)]
  [trycatch (first-ae KCFAE?)
            (second-ae KCFAE?)]
  [throw])

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (param list?)
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV (proc procedure?)]
  [errorV])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

;; ----------------------------------------

;; parse : S-expr -> KCFAE
(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse (second sexp)) (parse (third sexp)))]
       [(-) (sub (parse (second sexp)) (parse (third sexp)))]
       [(fun) (unless (uniq? (second sexp)) (error 'parse "bad-syntax"))
              (fun (second sexp) (parse (third sexp)))]
       [(if0) (if0 (parse (second sexp))
                   (parse (third sexp))
                   (parse (fourth sexp)))]
       [(withcc) (withcc (second sexp) (parse (third sexp)))]
       [(try) (unless (symbol=? (third sexp) 'catch) (error 'parse "bad-syntax"))
              (trycatch (parse (second sexp)) (parse (fourth sexp)))]
       [(throw) (unless (empty? (cdr sexp)) (error 'parse "bad-syntax")) (throw)]
       [else (app (parse (first sexp)) (map parse (rest sexp)))])]))

(test (parse 3) (num 3))
(test (parse 'x) (id 'x))
(test (parse '{+ 1 2}) (add (num 1) (num 2)))
(test (parse '{- 1 2}) (sub (num 1) (num 2)))
(test (parse '{fun {x} x}) (fun '(x) (id 'x)))
(test (parse '{1 2}) (app (num 1) (list (num 2))))
(test (parse '{if0 0 1 2}) (if0 (num 0) (num 1) (num 2)))
(test (parse '{withcc x 2}) (withcc 'x (num 2)))
(test (parse '{fun {x y} y}) (fun '(x y) (id 'y)))
(test (parse '{try {- 0 {throw}} catch 5}) (trycatch (sub (num 0) (throw)) (num 5)))
(test (parse '{try {try {throw} catch {+ 3 5}} catch {throw}}) (trycatch (trycatch (throw) (add (num 3) (num 5))) (throw)))

;; ----------------------------------------

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) -> alpha
(define (interp a-fae ds e k)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds e
                       (lambda (v1)
                         (interp r ds e
                                 (lambda (v2)
                                   (k (num+ v1 v2))))))]
    [sub (l r) (interp l ds e
                       (lambda (v1)
                         (interp r ds e
                                 (lambda (v2)
                                   (k (num- v1 v2))))))]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
         (interp fun-expr ds e
                 (lambda (fun-val)
                   (type-case KCFAE-Value fun-val
                     [closureV (param body ds2)
                               (interp-closure arg-expr param body ds ds2 e k)]
                     [contV (k)
                            (interp (first arg-expr) ds e (lambda (arg-val) (k arg-val)))]
                     [else (interp (first arg-expr) ds e
                                   (lambda (arg-val) (error 'interp "not a function")))])))]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds e
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds e k)
                       (interp else-expr ds e k))))]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    e k)]
    [trycatch (try catch)
              (interp try ds (interp catch ds e k) k)]
    [throw () e]))


(define (interp-closure args params body ds ds2 e k)
  (cond
    [(and (= (length params) 0) (not (= (length args) 0))) (error 'interp "arity mismatch")]
    [(and (not (= (length params) 0)) (= (length args) 0)) (error 'interp "arity mismatch")]
    [(if (empty? args) (interp body ds2 e k)
         (interp (first args) ds e
                 (lambda (arg-val)
                   (interp-closure (rest args) (rest params) body ds (aSub (first params) arg-val ds2) e k))))]))


;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))

;(test/exn (lookup 'x (mtSub)) "free variable")
;(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
;(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))

;; interp-expr : KCFAE -> KCFAE-Value
(define (interp-expr a-fae)
  (type-case KCFAE-Value (interp a-fae (mtSub) (errorV) (lambda (x) x))
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]
    [errorV () 'undefined]))

;; Check for eager evaluation:
(test/exn (interp-expr (parse '{{fun {x} 0}
                                {1 {fun {y} y}}}))
          "not a function")

;; run string list-of-FunDef -> number
(define (run str)
  (interp-expr (parse (string->sexpr str))))



(test (interp-expr (parse '{withcc k {k 10}}))
      10)

(test (interp-expr (parse 10))
      10)
(test (interp-expr (parse '{fun {x} x}))
      'function)
(test (interp-expr (parse '{withcc x x}))
      'function)

(test (interp-expr (parse '{+ 10 7}))
      17)
(test (interp-expr (parse '{- 10 7}))
      3)
(test (interp-expr (parse '{{fun {x} {+ x 12}}
                            {+ 1 17}}))
      30)

(test (interp-expr (parse'{{fun {x} {{fun {f} {+ {f 1}
                                                 {{fun {x} {f 2}}
                                                  3}}}
                                     {fun {y} {+ x y}}}}
                           0}))
      3)

(test (interp-expr (parse '{withcc k {k 10}}))
      10)

(test (interp-expr (parse '{withcc k
                                   {+ {k 10}
                                      17}}))
      10)

(test (interp-expr
       (parse
        '{{fun {mk-list}
               {{fun {list}
                     ; list has 2 numbers and k;
                     ; is first zero? 
                     {if0 {list 0}
                          ; return second:
                          {list 1} 
                          ; else recur...
                          {0 ; <- never actually applied!
                           ; recur by jumping to k:
                           {{list 2} {{{mk-list 
                                        {- {list 0} 1}} ; -1 to first
                                       {+ {list 1} 2}} ; +2 to second
                                      {list 2}}}}}} ; keep k as third
                {withcc k
                        ; make list with 2 numbers and k
                        {{{mk-list 3} 0} k}}}}                 
          ; mk-list - represent a list pf 3 items as a function, where
          ;  the function argument is a selector
          {fun {a}
               {fun {b}
                    {fun {c}
                         {fun {sel}
                              {if0 sel
                                   a
                                   {if0 {- sel 1}
                                        b
                                        c}}}}}}}))
      6)

(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{- 0 {withcc k {+ {k 10} 17}}}") -10)
(test (run "{- 0 {withcc k {+ 1 {withcc c {k {+ {c 10} 17}}}}}}") -11)
(test (run "{+ 5 {withcc k {+ 1000 {k 5}}}}") 10)
(test (run "{- 0 {withcc k {+ 15 {k 3}}}}") -3)
(test (run "{withcc a {- 0 {withcc b {b 15}}}}") -15)
(test (run "{{{fun {x y} {fun {c} {+ {+ x y} c}}} 1 2} 3}") 6)
(test (run "{if0 {withcc esc {+ 3 {esc 1}}} 10 {- 0 10}}") -10)
(test (run "{if0 {withcc esc {+ 3 {esc 0}}} 10 {- 0 10}}") 10)
(test (run "{- 0 {withcc esc {{fun {f} {f 3}} esc}}}") -3)
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{+ 3 {withcc k {+ 5 {k 9}}}}") 12)
(test (run "{{withcc k {fun {x y} {+ x y}}} 4 5}") 9)
(test (run "{+ {withcc k {k 5}} 4}" ) 9)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}") 55) ; recursive function
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}") 100) ; 
(test (run "{withcc k {- 0 {k 100}}}" ) 100)
(test (run "{withcc k {k {- 0 100}}}" ) -100)
(test (run "{withcc k {k {+ 100 11}}}" ) 111)
(test (run "{try {- 0 {throw}} catch 5}") 5)
(test (run "{try {if0 {throw} 3 4} catch 5}") 5)
(test (run "{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}") -1)
(test (run "{try {try {throw} catch {throw}} catch 9}") 9)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}") 5)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}") 10)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}") 42)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}") 3)
(test (run "{withcc esc {try {+ {throw} {esc 3}} catch 4}}") 4)
(test (run "{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}") 15)
(test (run "{try {withcc x {+ {x 1} {throw}}} catch 0}") 1)
(test (run "{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}") 19)
(test (run "{{{fun {x y} {fun {c} {+ {+ x y} c}}} 1 2} 3}") 6)
(test (run "{if0 {withcc esc {+ 3 {esc 1}}} 10 {- 0 10}}") -10)
(test (run "{if0 {withcc esc {+ 3 {esc 0}}} 10 {- 0 10}}") 10)
(test (run "{- 0 {withcc esc {{fun {f} {f 3}} esc}}}") -3)
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{+ 3 {withcc k {+ 5 {k 9}}}}") 12)
(test (run "{{withcc k {fun {x y} {+ x y}}} 4 5}") 9)
(test (run "{+ {withcc k {k 5}} 4}" ) 9)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}") 55) ; recursive function
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}") 100) 
(test (run "{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}" ) 0)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}") 20)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}") 110)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}") 54)
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}") 2)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}") 20110464)
(test (run "{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}") 0)
(test (run "{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}") 8)
(test (run "{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}") 89)
(test (run "{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}") 11)
(test (run "{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}") 5)
(test (run "{+ {try {- 10 {throw}} catch 3} 10}") 13)
(test (run "{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}") 54)
(test (run "{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}") 10)
(test (run "{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}") -1)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}") 5)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}") 10)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}") 42)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}") 3)
(test (run "{withcc esc {try {+ {throw} {esc 3}} catch 4}}") 4)
(test (run "{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}") 15)
(test (run "{try {withcc x {+ {x 1} {throw}}} catch 0}") 1)
(test (run "{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}") 19)
(test (run "{+ {try {+ 1 {throw}} catch 3} {throw}}") 'undefined)
(test (run "{{fun {x y} {+ x y}} {throw}}") 'undefined)
(test (run "{try {+ 2 {withcc k {+ 4 {{fun {x y} y} 3 {k {throw}} }}}} catch { + 2 4 }}" ) 6)
(test (run "{{fun {a b c} {+ a b}} {try {+ 3 {withcc e {+ {throw} {e 4}}}} catch 4}  5  3}") 9)
(test (run "{try {withcc done {{withcc esc {done {+ 1 {withcc k {esc k}}}}} 3}} catch 18}") 4)
(test (run "{try {{throw} {withcc done {{withcc esc {done {+ 1 {withcc k {esc k}}}}} 3}}} catch 18}") 18)
(test (run "{try {{throw} {withcc done {{withcc esc {done {+ 1 {withcc k {esc {throw}}}}}} 3}}} catch 18}") 18)
(test (run "{withcc esc {try {+ 1 {withcc k {{throw} k}}} catch {esc 3}}}") 3)
(test (run "{{fun {x y z} {+ x {- y z}}} {withcc x {x 3}} {try {+ 3 {withcc y {y {throw}}}} catch 32} 32}") 3)
(test (run "{withcc esc {+ {throw} {esc 3}}}") 'undefined)
(test (run "{{{fun {f} {throw}} {fun {x} {+ x 1}}} 2}") 'undefined)
(test (run "{{fun {t c} {t 10 c 30}} {fun {y a b} {+ y b}} 42}") 40)
(test (run "{try {throw} catch {try {+ 3 {throw}} catch {try {throw} catch 2}}}") 2)
(test (run "{{fun {a b} {a b}} {fun {x} {try x catch x}} {throw}}") 'undefined)