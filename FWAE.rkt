#lang plai

; FWAE
(define-type FWAE
  [num (n number?)]
  [add (lhs FWAE?)
       (rhs FWAE?)]
  [sub (lhs FWAE?)
       (rhs FWAE?)]
  [id (name symbol?)]
  [with (name symbol?)
        (named-expr FWAE?)
        (body FWAE?)]
  [fun (param symbol?)
       (body FWAE?)]
  [app (ftn FWAE?)
       (arg FWAE?)])
  

;parse: sexp -> FWAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(list f a) (app f (parse a))]
    [(list 'fun p b) (fun p (parse b))]
    [else (error 'parse "bad syntax: ~a" sexp)]))



;subst: FWAE symbol FWAE -> FWAE
(define (subst exp sub-id val)
  (type-case FWAE fwae
    [num (n) fwae]
    [add (l r) (add (subst l x val) (subst r x val))]
    [sub (l r) (sub (subst l x val) (subst r x val))]
    [with (y i b) (with y
                       (subst i x val)
                       (if (symbol=? y x) b
                           (subst b x val)))]
    [id (name) (cond
                 [(equal? name sub-id) val]
                 [else exp])]
    [app (f arg) (app (subst f sub-id val)
                      (subst arg sub-id val))]
    [fun (id body) (if (equal? sub-id id)
                       exp
                       (fun id (subst body sub-id val)))]))

; num+: FWAE FWAE -> FWAE
; to check the type of parameters
(define (num+ x y)
  (num (+ (num-n x) (num-n y))))

(define (num- x y)
  (num (- (num-n x) (num-n y))))


;interp: FWAE -> number
(define (interp fwae)
  (type-case FWAE fwae
    [num (n) fwae]
    [add (l r) (num+ (interp l) (interp r))]
    [sub (l r) (num- (interp l) (interp r))]
    [id (s) (error 'interp "free variable")]
    [with (x i b) (interp (subst b x (interp i)))]
    [fun (x b) fwae]
    [app (f a)
         (local [(define ftn (interp f))]
           (interp (subst (fun-body ftn)
                          (fun-param ftn)
                          (interp a))))]))



;(interp (parse '{with {y 2} {fun 10}}) (mtSub) empty)
(interp (parse '{with {y 2} {fun 10}}) (mtSub) (cons (parse-fd '{deffun {fun x} {+ 1 x}}) empty))