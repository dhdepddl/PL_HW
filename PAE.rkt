#lang plai

; FAE
(define-type FAE
  [num (n number?)]
  [add (lhs FAE?)
       (rhs FAE?)]
  [sub (lhs FAE?)
       (rhs FAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body FAE?)]
  [app (ftn FAE?)
       (arg FAE?)])
  

; FAE-Value
(define-type FAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body FAE?) (ds DefrdSub?)])

;DefrdSub
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FAE-Value?) (ds DefrdSub?)])


;parse: sexp -> FAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list f a) (app f (parse a))]
    [(list 'fun p b) (fun p (parse b))]
    [else (error 'parse "bad syntax: ~a" sexp)]))



;subst: FAE symbol FAE -> FAE
(define (subst exp sub-id val)
  (type-case FAE fae
    [num (n) fae]
    [add (l r) (add (subst l x val) (subst r x val))]
    [sub (l r) (sub (subst l x val) (subst r x val))]
    [id (name) (cond
                 [(equal? name sub-id) val]
                 [else exp])]
    [app (f arg) (app (subst f sub-id val)
                      (subst arg sub-id val))]
    [fun (id body) (if (equal? sub-id id)
                       exp
                       (fun id (subst body sub-id val)))]))

; num+: FAE FAE -> FAE
; to check the type of parameters
(define (num+ x y)
  (num (+ (num-n x) (num-n y))))

(define (num- x y)
  (num (- (num-n x) (num-n y))))


; lookup: symbol DefrdSub -> number
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (x val rest)
          (if (symbol=? name x) vals
              (lookup name rest))]))



;interp: FAE DefrdSub -> FAE-Value
(define (interp fae ds)
  (type-case FAE fae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (s) (lookup s ds)]
    [fun (x b) (closureV x b ds)]
    [app (f a)
         (local [(define f-val (interp f ds))
                 (define a-val (interp a ds))]
           (interp (closureV-bpdy f-val)
                   (aSub (closureV-param f-val)
                         a-val
                         (closureV-ds f-val))))]))