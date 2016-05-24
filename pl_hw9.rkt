#lang plai-typed
(define-type TMFAE
  [bool (b : boolean)]
  [num (n : number)]
  [add (lhs : TMFAE)
       (rhs : TMFAE)]
  [sub (lhs : TMFAE)
       (rhs : TMFAE)]
  [eq (lhs : TMFAE)
      (rhs : TMFAE)]
  [id (name : symbol)]
  [ifthenelse (if : TMFAE)
              (then : TMFAE)
              (else : TMFAE)]
  [with (name : (listof symbol))
        (namety : (listof TE))
        (inits : (listof TMFAE))
        (body : TMFAE)]
  [fun (param : (listof symbol))
       (paramty : (listof TE))
       (body : TMFAE)]
  [app (fun-expr : TMFAE)
       (arg-expr : (listof TMFAE))]
  [pair (lhs : TMFAE)
        (rhs : TMFAE)]
  [fst (val : TMFAE)]
  [snd (val : TMFAE)]
  [try1 (try-expr : TMFAE)
        (catch-expr : TMFAE)]
  [throw])

(define-type TE
  [numTE]
  [boolTE]
  [crossTE (left : TE)
         (right : TE)]
  [arrowTE (param : (listof TE))
           (result : TE)])

(define-type TMFAE-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [pairV (left : TMFAE)
         (right : TMFAE)]
  [closureV (param : (listof symbol))
            (body : TMFAE)
            (ds : DefrdSub)]
  [contV (proc : ('_a -> '_b))]
  [errorV])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TMFAE-Value)
        (rest : DefrdSub)])

(define-type Type
  [numT]
  [boolT]
  [crossT (left : Type)
        (right : Type)]
  [arrowT (param : (listof Type))
          (result : Type)]
  [anyT])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

;; ----------------------------------------

;; interp : TFAE DefrdSub -> TFAE-Value
(define (interp tmfae ds e k)
  (type-case TMFAE tmfae
    [bool (b) (k (boolV b))]
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
    [eq (l r) (interp l ds e
                      (lambda (v1)
                        (interp r ds e
                                (lambda (v2)
                                  (k (num= v1 v2))))))]
    [id (name) (k (lookup name ds))]
    [ifthenelse (i t el)
                (interp i ds e
                        (lambda (v1)
                          (if (boolV-b v1)
                              (interp t ds e (lambda (v) (k v)))
                              (interp el ds e (lambda (v) (k v))))))]
    [with (name te tfae body)
          (numV 3)]
    [fun (param param-te body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
         (interp fun-expr ds e
                 (lambda (fun-val)
                   (type-case TMFAE-Value fun-val
                     [closureV (param body ds2)
                               (interp-closure arg-expr param body ds ds2 e k)]
                     [contV (k)
                            (interp (first arg-expr) ds e (lambda (arg-val) (k arg-val)))]
                     [else (interp (first arg-expr) ds e
                                   (lambda (arg-val) (error 'interp "not a function")))])))]
    [pair (l r) (k (pairV l r))]
    [fst (v) (interp v ds e
                     (lambda (val) 
                       (interp (pairV-left val) ds e
                               (lambda (val2)
                                 (k val2)))))]
    [snd (v) (interp v ds e
                     (lambda (val) 
                       (interp (pairV-right val) ds e
                               (lambda (val2)
                                 (k val2)))))]
    [try1 (t c)
          (interp t ds (interp c ds e k) k)]
    [throw () e]))

(define (interp-closure args params body ds ds2 e k)
        (if (empty? args) (interp body ds2 e k)
         (interp (first args) ds e
                 (lambda (arg-val)
                   (interp-closure (rest args) (rest params) body ds (aSub (first params) arg-val ds2) e k)))))

;; num-op : (number number -> number) -> (TFAE-Value TFAE-Value -> TFAE-Value)
(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))
(define (num= x y)
  (boolV (= (numV-n x) (numV-n y))))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-ds)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-ds))]))

;; ----------------------------------------

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]))

;; ----------------------------------------

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [crossTE (l r) (crossT (parse-type l)
                         (parse-type r))]
    [arrowTE (a b) (arrowT 
                    (parse-arr a empty)
                    (parse-type b))]))

(define (parse-arr a new)
  (if (empty? a) new
      (parse-arr (rest a) (cons (parse-type (first a)) new))))

(define (type-error tmfae msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string tmfae)
                      (string-append " not "
                                     msg)))))

(define typecheck : (TMFAE TypeEnv -> Type)
  (lambda (tmfae env)
    (type-case TMFAE tmfae
      [bool (b) (boolT)]
      [num (n) (numT)]
      [add (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [sub (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [eq (l r) (type-case Type (typecheck l env)
                  [numT ()
                        (type-case Type (typecheck r env)
                          [numT () (boolT)]
                          [else (type-error r "num")])]
                  [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [ifthenelse (i t e)
                  (type-case Type (typecheck i env)
                    [boolT ()
                           (type-case Type (typecheck t env)
                             [anyT () (typecheck e env)]
                             [else
                              (type-case Type (typecheck e env)
                                [anyT () (typecheck t env)]
                                [else
                                 (if (equal? (typecheck t env) (typecheck e env))
                                     (typecheck t env)
                                     (type-error tmfae "Not same type"))])])]
                    [anyT ()
                          (if (equal? (typecheck t env) (typecheck e env))
                                     (typecheck t env)
                                     (type-error tmfae "Not same type"))]
                    [else (type-error i "bool")])]
      [with (name te tfae body)
            (type-case Type (mk-type name te empty body env)
              [arrowT (param-type result-type) result-type]
              [else (type-error tmfae "No type")])]
      [fun (name te body)
           (mk-type name te empty body env)]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (param-type result-type)
                     (if (equal? param-type
                                 (mk-arg arg empty env))
                         result-type
                         (type-error arg
                                     (to-string param-type)))]
             [else (type-error fn "function")])]
      [pair (l r) (crossT (typecheck l env)
                        (typecheck r env))]
      [fst (v) (type-case Type (typecheck v env)
                 [crossT (l r) l]
                 [anyT () (anyT)]
                 [else (type-error v "pair")])]
      [snd (v) (type-case Type (typecheck v env)
                 [crossT (l r) r]
                 [anyT () (anyT)]
                 [else (type-error v "pair")])]
      [try1 (t c)
            (type-case Type (typecheck t env)
              [anyT () (typecheck c env)]
              [else
               (if (or (equal? (typecheck t env) (typecheck c env)) (equal? (anyT) (typecheck c env)))
                   (typecheck t env)
                   (error 'typecheck "no type"))])]
      [throw () (anyT)])))

(define (mk-type name te teo body env)
  (if (empty? te)
      (arrowT teo (typecheck body env))
      (local [(define val (parse-type (first te)))]
        (mk-type (rest name) (rest te) (cons val teo) body (aBind (first name) val env)))))

(define (mk-arg args new env)
  (if (empty? args) new
      (mk-arg (rest args) (cons (typecheck (first args) env) new) env)))

(define run : (TMFAE -> TMFAE-Value)
  (lambda (tmfae)
    (interp tmfae (mtSub) (errorV) (lambda (x) x))))

(define eval : (TMFAE -> TMFAE-Value)
  (lambda (tmfae)
    (begin
      (try (typecheck tmfae (mtEnv))
           (lambda () (error 'type-error "typecheck")))
      (run tmfae))))



;; ----------------------------------------
(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE))
                        (sub (id 'x) (id 'y))) (list (num 10) (num 20))))
      (numV -10))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                           (id 'y))
                      (list (num 10) (bool false)))
                 (mtEnv))
      (boolT))
(test/exn (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                               (id 'y))
                          (list (num 10) (num 10)))
                     (mtEnv))
          "no type")

(test (typecheck (throw) (mtEnv)) (anyT))
(test (typecheck (try1 (num 8) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 10)) (mtEnv)) (numT))
(test/exn (typecheck (try1 (num 8) (bool false)) (mtEnv)) "no type")
(test (typecheck (ifthenelse (throw) (num 1) (num 2)) (mtEnv)) (numT))
(test/exn (typecheck (app (throw) (list (ifthenelse (num 1) (num 2) (num 3)))) (mtEnv)) "no type")
(test/exn (typecheck (add (bool true) (throw)) (mtEnv)) "no type")
(test (typecheck (fst (throw)) (mtEnv)) (anyT))
(test (typecheck (ifthenelse (bool true) (pair (num 1) (throw)) (pair (throw) (bool false))) (mtEnv)) (crossT (numT) (boolT)))
(test (typecheck (bool true) (mtEnv)) (boolT))
(test (typecheck (ifthenelse (bool false) (num 2) (throw)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (num 2)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (throw)) (mtEnv)) (anyT))
(test (typecheck (pair (num 2) (bool false)) (mtEnv)) (crossT (numT) (boolT)))
(test (typecheck (pair (num 2) (throw)) (mtEnv)) (crossT (numT) (anyT)))
(test (typecheck (snd (throw)) (mtEnv)) (anyT))
(test (typecheck (fst (pair (num 2) (bool false))) (mtEnv)) (numT))
(test (typecheck (snd (pair (num 2) (bool false))) (mtEnv)) (boolT))
(test (typecheck (fun empty empty (num 2)) (mtEnv)) (arrowT empty (numT)))
(test (typecheck (fun (list 'x) (list (numTE)) (throw)) (mtEnv)) (arrowT (list (numT)) (anyT)))
(test (typecheck (app (fun empty empty (num 2)) empty) (mtEnv)) (numT))
(test (typecheck (app (throw) (list (num 2) (bool false))) (mtEnv)) (anyT))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y))) (list (num 2) (num 3))) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (num 2)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'x 'y 'z) (list (boolTE) (numTE) (numTE)) (list (bool false) (num 2) (num 3)) (ifthenelse (id 'x) (id 'y) (id 'z))) (mtEnv)) (numT))
(test (typecheck (with empty empty empty (num 2)) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (throw)) (num 2)) (mtEnv)) (numT))
(test (run (eq (num 2) (num 3))) (boolV false))
(test (run (eq (num 2) (num 2))) (boolV true))
(test (run (ifthenelse (bool true) (num 2) (num 3))) (numV 2))
(test (run (ifthenelse (bool false) (num 2) (num 3))) (numV 3))
(test (run (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 2) (num 3) (num 4)) (add (id 'x) (id 'y)))) (numV 5))
(test (run (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y)))) (closureV (list 'x 'y) (add (id 'x) (id 'y)) (mtSub)))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y))) (list (num 2) (num 3)))) (numV 5))
(test (run (fst (pair (num 2) (num 3)))) (numV 2))
(test (typecheck (try1 (throw) (throw)) (mtEnv)) (anyT))
(test (typecheck (app (throw) (list (num 1))) (mtEnv)) (anyT))
(test (typecheck (fst (throw)) (mtEnv)) (anyT))
(test (typecheck (ifthenelse (bool true) (fun (list 'x 'y) (list (numTE) (numTE)) (throw)) (fun (list 'z 'a) (list (numTE) (numTE)) (add (id 'z) (id 'a)))) (mtEnv)) (arrowT (list (numT) (numT)) (numT)))
(test (typecheck (try1 (num 2) (throw)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 2)) (mtEnv)) (numT))
(test (typecheck (try1 (num 2) (num 2)) (mtEnv)) (numT))
(test (typecheck (app (fun (list 'a) (list (numTE)) (add (throw) (num 10))) (list (throw))) (mtEnv)) (numT))
(test (typecheck (try1 (with (list 'map 'foo) (list (arrowTE (list (arrowTE (list (numTE)) (boolTE)) (crossTE (numTE) (numTE))) (crossTE (boolTE) (boolTE))) (crossTE (numTE) (numTE)))          (list (fun (list 'f 'p) (list (arrowTE (list (numTE)) (boolTE)) (crossTE (numTE) (numTE))) (pair (app (id 'f) (list (fst (id 'p)))) (app (id 'f) (list (snd (id 'p)))))) (pair (num 10) (num 42))) (app (id 'map) (list (throw) (id 'foo)))) (pair (bool false) (bool false))) (mtEnv))     (crossT (boolT) (boolT)))
(test (typecheck (try1 (add (throw) (num 8)) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (pair (num 8) (num 2)) (throw)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (eq (num 42) (try1 (ifthenelse (bool true) (throw) (throw)) (num 10))) (mtEnv)) (boolT))
(test (typecheck (ifthenelse (throw) (pair (throw) (num 42)) (pair (bool false) (throw))) (mtEnv)) (crossT (boolT) (numT)))
(test (typecheck (with (list 'x 'y 'z) (list (boolTE) (numTE) (numTE)) (list (bool false) (num 2) (num 3)) (ifthenelse (id 'x) (id 'y) (id 'z))) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (num 2)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'dup) (list (arrowTE (list (numTE)) (crossTE (numTE) (numTE)))) (list (fun (list 'n) (list (numTE)) (pair (id 'n) (id 'n)))) (app (id 'dup) (list (throw)))) (mtEnv))   (crossT (numT) (numT)))
(test/exn (typecheck (app (throw) (list (add (bool true) (throw)))) (mtEnv)) "no type")
(test/exn (typecheck (app (throw) (list (ifthenelse (num 1) (num 2) (num 3)))) (mtEnv)) "no type")
(test/exn (typecheck (app (throw) (list (app (bool true) (list (throw))))) (mtEnv)) "no type")

