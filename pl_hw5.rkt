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


; FnWAE
; for multiple arguements, the type of field arg of variant app has changed to list
; add record and get
(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)
       (rhs FnWAE?)]
  [sub (lhs FnWAE?)
       (rhs FnWAE?)]
  [id (name symbol?)]
  [with (name symbol?)
        (named-expr FnWAE?)
        (body FnWAE?)]
  [record (recs list?)]
  [get (record FnWAE?)
       (param symbol?)]
  [app (ftn symbol?)
       (arg list?)])

;FunDef
(define-type FunDef
  [fundef (fun-name symbol?)
    (arg-name list?)
    (body FnWAE?)])


; FnWAE Values
; for record, make FnWAE-Value
; with variant numV with field n of type number
; and recV with field recs of type list of pairs
(define-type FnWAE-Value
  [numV (n number?)]
  [recV (recs list?)])


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


; parse-sexpr : sexp -> FnWAE
; parse arg of app by using map
; to parse record, firstly check it is record or not
; and the list of record has duplicate fields or not
; and parse by using map
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(list 'rec x ...) 
     (cond
       [(not (for/and ([e x]) (= 2 (length e)))) (error 'parse-sexpr "Not a record")]
       [(not (= (length x) (length (remove-duplicates (for/list ([e x]) (first e)))))) (error 'parse-sepxr "duplicate fields")]
       [else
        (record (map (lambda (e) (cons (parse-sexpr (first e)) (parse-sexpr (second e)))) x))])]
    [(list 'get rec x) (get (parse-sexpr rec) x)]
    [(? symbol?) (id sexp)]
    [(list f a ...) (app f (map parse-sexpr a))]
    [else (error 'parse-sexpr "bad syntax: ~a" sexp)]))


;; parses a string containing a WAE expression to a WAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

(test (parse "{f 1 2}") (app 'f (list (num 1) (num 2))))
(test (parse "{fun}") (app 'fun empty))
(test (parse "{rec {a 10} {b {+ 1 2}}}")
      (record (list (cons (id 'a) (num 10)) (cons (id 'b) (add (num 1) (num 2))))))
(test/exn (parse "{rec {a b c}}") "parse-sexpr: Not a record") 
(test/exn (parse "{rec {a 1} {a 2}}") "duplicate fields")
(test (parse "{get {rec {a 10}} b}") (get (record (list (cons (id 'a) (num 10)))) 'b))
    


; parse-defn : sexp -> FunDef
(define (parse-defn sexp)
  (match sexp
    [(list 'deffun (list f x ...) body)
     (unless (uniq? x)
       (error 'parse-defn "bad syntax"))
     (fundef f x (parse-sexpr body))]))

(test (parse-defn '(deffun (f x y) (+ x y))) (fundef 'f '(x y) (add (id 'x) (id 'y))))
(test/exn (parse-defn '(deffun (f x x) (+ x 2))) "parse-defn: bad syntax")



; lookup-fundef : symbol list-of-FunDef -> FunDef
(define (lookup-fundef name fundefs)
  (cond
    [(not (symbol? name)) (error 'lookup-fundef "Wrong type - not symbol: ~a" name)]
    [(not (list? fundefs)) (error 'lookup-fundef "Wrong type - not list: ~a" fundefs)]
    [(not (= (length (filter FunDef? fundefs)) (length fundefs)))
     (error 'lookup-fundef "Wrong type - not list of FunDef: ~a" fundefs)]
    [(empty? fundefs)
     (error 'lookup-fundef "unknown function")]
    [else
     (if (symbol=? name (fundef-fun-name (first fundefs)))
         (first fundefs)
         (lookup-fundef name (rest fundefs)))]))


;subst: FnWAE symbol FnWAE-Value -> FnWAE
; to implement FnWAE with record and get, use substitution instead of defrdSub
; subst record, map, list of function parameters with map
; and get input for val in type of numV and recV
(define (subst fnwae x val)
  (cond
    [(not (FnWAE? fnwae)) (error 'subst "Wrong type - not F1WAE: ~a" fnwae)]
    [(not (symbol? x)) (error 'subst "Wrong type - not symbol: ~a" x)]
    [(not (FnWAE-Value? val)) (error 'subst "Wrong type - not FnWAE-Value: ~a" val)]
    [else
     (type-case FnWAE fnwae
       [num (n) fnwae]
       [add (l r) (add (subst l x val) (subst r x val))]
       [sub (l r) (sub (subst l x val) (subst r x val))]
       [with (y i b) (with y
                           (subst i x val)
                           (if (symbol=? y x) b
                               (subst b x val)))]
       [id (s) (if (symbol=? s x) 
                   (type-case FnWAE-Value val
                     [numV (n) (num n)]
                     [recV (r) (record r)])
                     fnwae)]
       [app (f a) (app f (map (lambda (e) (subst e x val)) a))]
       [record (r) (record (map (lambda (e) (cons (car e) (subst (cdr e) x val))) r))]
       [get (r z) (get (subst r x val) z)])]))

; help function for interp get
(define (pick-rec l x)
  (if (symbol=? x (id-name (car (first l)))) (cdr (first l))
      (pick-rec (rest l) x)))

;interp: FnWAE list-of-FunDef -> FnWAE-Value
; interprete multiple parameters of function by using recursive call of subst function
; interprete record by using map function
(define (interp fnwae fundefs)
  (cond
    [(not (FnWAE? fnwae)) (error 'interp "Wrong type - not FnWAE: ~a" fnwae)]
    [(not (list? fundefs)) (error 'interp "Wrong type - not list: ~a" fundefs)]
    [(not (= (length (filter FunDef? fundefs)) (length fundefs)))
     (error 'interp "Wrong type - not list of FunDef: ~a" fundefs)]
    [else
     (type-case FnWAE fnwae
       [num (n) (numV n)]
       [add (l r) (numV (+ (numV-n (interp l fundefs)) (numV-n (interp r fundefs))))]
       [sub (l r) (numV (- (numV-n (interp l fundefs)) (numV-n (interp r fundefs))))]
       [with (x i b) (interp (subst b x 
                                    (cond
                                      [(record? i) (recV (record-recs i))]
                                      [else (interp i fundefs)])) fundefs)]
       [id (s) (error 'interp "free variable")]
       [app (f a)
            (local
              [(define a-fundef (lookup-fundef f fundefs))]
              (unless (= (length a) (length (fundef-arg-name a-fundef)))
                (error 'interp "wrong arity"))
                (interp
                 (local [(define sub
                                  (lambda (body x a)
                                    (if (empty? a)
                                        body
                                        (sub (subst body (first x) (first a)) (rest x) (rest a)))))]
                   (sub (fundef-body a-fundef) (fundef-arg-name a-fundef) (map (lambda (e) 
                                                                                 (cond
                                                                                   [(record? e) (recV (record-recs e))]
                                                                                   [else
                                                                                    (interp e fundefs)])) a))) fundefs))]
       [record (r) (recV (map (lambda (e) (cons (car e) (interp (cdr e) fundefs))) r))]
       [get (re x) (cond
                   [(for/or ([e (recV-recs (interp re fundefs))]) (symbol=? x (id-name (car e))))
                    (pick-rec (recV-recs (interp re fundefs)) x)]
                   [else
                      (error 'interp "no such field")])])]))


; interp-expr: FnWAE-Value -> number or symbol
(define (interp-expr fval)
  (type-case FnWAE-Value fval
    [numV (n) n]
    [recV (r) 'record]))

(test (interp-expr (numV 3)) 3)
(test (interp-expr (recV '((cons 'a (num 3))))) 'record)



; run string list-of-FunDef -> number
(define (run str fundefs)
  (interp-expr (interp (parse str) fundefs)))





(test (parse "{f 10}") (app 'f (list (num 10))))
(test (parse-defn '{deffun {f x} {+ x x}}) (fundef 'f '(x) (add (id 'x) (id 'x))))
(test (run "{f}" (list (parse-defn '{deffun {f} 5}))) 5)
(test (run "{f 10}" (list (parse-defn '{deffun {f x} {+ x x}}))) 20)
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test/exn (run "{f 1}" (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test (run "{rec {a 10} {b {+ 1 2}}}" empty)
      'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty)
      3)
(test/exn (run "{get {rec {b 10} {b {+ 1 2}}} b}" empty)
          "duplicate fields")
(test/exn (run "{get {rec {a 10}} b}" empty)
          "no such field")
(test (run "{g {rec {a 0} {c 12} {b 7}}}"
           (list (parse-defn '{deffun {g r} {get r c}})))
      12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty)
      'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty)
      0)
(test/exn (run "{rec {z {get {rec {z 0}} y}}}" empty)
          "no such field")
(test (run "{with {x {f 2 5}} {g x}}" (list (parse-defn '{deffun {f a b} {+ a b}}) (parse-defn '{deffun {g x} {- x 5}}))) 2)
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test (run "{h 1 4 5 6}" (list (parse-defn '{deffun {h x y z w} {+ x w}}) (parse-defn '{deffun {g x y z w} {+ y z}}))) 7)
(test (run "{with {x 10} {- {+ x {f}} {g 4}}}" (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) 6)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {x 3} {with {y 5} {get {rec {a x} {b y}} a}}}" empty) 3)
(test (run "{with {x {f {rec {a 10} {b 5}} 2}} {g x}}" (list (parse-defn '{deffun {f a b} {+ {get a a} b}}) (parse-defn '{deffun {g x} {+ 5 x}}))) 17)
(test (run "{get {f 1 2 3 4 5} c}" (list (parse-defn '{deffun {f a b c d e} {rec {a a} {b b} {c c} {d d} {e e}}}))) 3)
(test (run "{get {f 1 2 3} b}" (list (parse-defn '{deffun {f a b c} {rec {a a} {b b} {c c}}}))) 2)
(test (run "{get {f 1 2 3} y}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{get {f 1 2 3} d}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{f {get {get {rec {a {rec {a 10} {b {- 5 2}}}} {b {get {rec {x 50}} x}}} a} b}}" (list (parse-defn '{deffun {f x} {+ 5 x}}))) 8)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {+ 1 2}}} a}" empty) 3)
(test (run "{rec }" empty) `record)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{rec {a {- 2 1}}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {- 2 1}}} a}" empty) 1)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y y}}" empty) 2)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y z}}" empty) 3)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
