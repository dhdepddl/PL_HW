#lang racket
(define table empty)
(define (remember v)
  (local [(define n (length table))]
    (begin (set! table (append table (list v)))
           n)))
(define (lookup key)
  (list-ref table key))

(define (web-read/k prompt cont)
  (local [(define key (remember cont))]
    (quasiquote ((unquote prompt) "To continue, call resume/k with " (unquote key) " and value"))))

(define (resume/k key val)
  (local [(define cont (lookup key))]
    (cont val)))

(define (f)
  (do-f 0))

(define (do-f total)
  (web-read/k
   (format "Total is ~a\nNext number...\n" total)
   (lambda (val)
     (do-f (+ total val)))))

(define (g)
  (web-read/k "First number"
              (lambda (v1)
                (web-read/k "Second number"
                            (lambda (v2)
                              (+ v1 v2))))))

(define (h)
  (+ (num-read "First number")
     (num-read "Second number")))
(define (num-read prompt)
  (begin
    (printf "~a\n" prompt)
    (read)))

(define (gg)
  (begin (g) (g)))
(define (hh)
  (begin (h) (h)))
(define (gh)
  (begin (g) (h)))
(define (hg)
  (begin (h) (g)))

(define (p) (do-p identity))
(define (do-p cont)
  (web-read/k "First number"
              (lambda (v1)
                (web-read/k "Second number"
                            (lambda (v2)
                            (cont (+ v1 v2)))))))
(define (p2) (do-p2 identity))
(define (do-p2 cont)
  (do-p (lambda (sum)
          (web-pause/k sum
                       (lambda ()
                         (do-p cont))))))
(define (identity x) x)
(define (web-pause/k prompt cont)
  (local [(define key (remember cont))]
    (quasiquote ((unquote prompt) "To continue, call p-resume/k with " (unquote key)))))
(define (p-resume/k key)
  ((lookup key)))

; implemnting web-read
(define (web-read prompt)
  (let/cc cont
    (local [(define key (remember cont))]
      (error 'web-read
             "~a; to continue, call resume with ~a and value"
             prompt key))))

(define (web-pause prompt)
  (let/cc cont
    (local [(define key (remember cont))]
      (error 'web-pause
             "~a; to continue, call p-resume with ~a"
             prompt key))))
(define (p-resume key)
  (local [(define cont (lookup key))]
    (cont (void))))

(define (i)
  (web-pause (h))
  (h))

(define (web-read-each prompts)
  (map web-read prompts))

(define (m)
  (apply format "my ~a saw a ~a rock"
         (web-read-each '("noun" "adjective"))))

