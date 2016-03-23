#lang plai

; F1WAE
(define-type F1WAE
  [num (n number?)]
  [add (lhs F1WAE?)
       (rhs F1WAE?)]
  [sub (lhs F1WAE?)
       (rhs F1WAE?)]
  [id (name symbol?)]
  [with (name symbol?)
        (named-expr F1WAE?)
        (body F1WAE?)]
  [app (ftn symbol?)
       (arg F1WAE?)])


;DefFun
(define-type FunDef
  [fundef (fun-name symbol?)
    (arg-name symbol?)
    (body F1WAE?)])


;DefrdSub
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value number?)
        (rest DefrdSub?)])
  

;parse: sexp -> F1WAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'with (list 'x i) b) (with 'x (parse i) (parse b))]
    [(list f a) (app f (parse a))]
    [else (error 'parse "bad syntax: ~a" sexp)]))


;parse-fd: sexp -> FunDef
(define (parse-fd sexp)
  (match sexp
    [(list 'deffun (list f x) b) (fundef f x (parse b))]))


;lookup: symbol DefrdSub -> number
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (x val rest)
          (if (symbol=? name x) val
              (lookup name rest))]))


;lookup-fundef: symbol list-of-FunDef -> FunDef
(define (lookup-fundef fname fundefs)
  (cond
    [(empty? fundefs) (error 'lookup-fundef "unknown function")]
    [else
     (symbol=? fname (fundef-fun-name (first fundefs))) (first fundefs)
     (lookup-fundef fname (rest fundefs))]))


;interp: F1WAE DefrdSub list-of-FunDef -> number
(define (interp wae ds fundefs)
  (type-case F1WAE wae
    [num (n) n]
    [add (l r) (+ (interp l ds fundefs) (interp r ds fundefs))]
    [sub (l r) (- (interp l ds fundefs) (interp r ds fundefs))]
    [id (s) (lookup s ds)]
    [with (x i b) (interp b (aSub x (interp i) ds) fundefs)]
    [app (f a)
         (local [(define a-fundef (lookup-fundef f fundefs))]
           (interp (fundef-body a-fundef)
                   (aSub (fundef-arg-name a-fundef)
                   (interp a ds fundefs)
                   (mtSub))
                   fundefs))]))