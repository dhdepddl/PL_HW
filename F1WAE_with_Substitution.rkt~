#lang plai

;define type F1WAE
;with variants named num, add, sub, with, id, app
(define-type F1WAE
  [num (n number?)]
  [add (lhs F1WAE?) (rhs F1WAE?)]
  [sub (lhs F1WAE?) (rhs F1WAE?)]
  [with (name symbol?) (named-expr F1WAE?) (body F1WAE?)]
  [id (name symbol?)]
  [app (ftn symbol?) (arg F1WAE?)])


;defien type FunDef
;with constructor fundef: symbol(fun-name) symbol(arg-name) body(F1WAE) -> FunDef
(define-type FunDef
  [fundef (fun-name symbol?)
          (arg-name symbol?)
          (body F1WAE?)])


; parse: sexp -> F1WAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(? symbol?) (id sexp)]
    [(list f a) (app f (parse a))]
    [else (error 'parse "bad syntax: ~a" sexp)]))


;parse-fd: sexp ->  FunDef
(define (parse-fd sexp)
  (match sexp
    [(list 'deffun (list f x) b) (fundef f x (parse b))]))


;lookup-fundef: symbol list-of-FunDef -> FunDef
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
     

;subst: F1WAE symbol number -> F1WAE
(define (subst f1wae x val)
  (cond
    [(not (F1WAE? f1wae)) (error 'subst "Wrong type - not F1WAE: ~a" f1wae)]
    [(not (symbol? x)) (error 'subst "Wrong type - not symbol: ~a" x)]
    [(not (number? val)) (error 'subst "Wrong type - not number: ~a" val)]
    [else
     (type-case F1WAE f1wae
       [num (n) f1wae]
       [add (l r) (add (subst l x val) (subst r x val))]
       [sub (l r) (sub (subst l x val) (subst r x val))]
       [with (y i b) (with y
                           (subst i x val)
                           (if (symbol=? y x) b
                               (subst b x val)))]
       [id (s) (if (symbol=? s x) (num val) f1wae)]
       [app (f a) (app f (subst a x val))])]))


;interp: F1WAE list-of-FunDef -> number
(define (interp f1wae fundefs)
  (cond
    [(not (F1WAE? f1wae)) (error 'interp "Wrong type - not F1WAE: ~a" f1wae)]
    [(not (list? fundefs)) (error 'interp "Wrong type - not list: ~a" fundefs)]
    [(not (= (length (filter FunDef? fundefs)) (length fundefs)))
     (error 'interp "Wrong type - not list of FunDef: ~a" fundefs)]
    [else
     (type-case F1WAE f1wae
       [num (n) n]
       [add (l r) (+ (interp l fundefs) (interp r fundefs))]
       [sub (l r) (- (interp l fundefs) (interp r fundefs))]
       [with (x i b) (interp (subst b x (interp i fundefs)) fundefs)]
       [id (s) (error 'interp "free variable")]
       [app (f a)
            (local
              [(define a-fundef (lookup-fundef f fundefs))]
              (interp (subst (fundef-body a-fundef)
                             (fundef-arg-name a-fundef)
                             (interp a fundefs)) fundefs))])]))
