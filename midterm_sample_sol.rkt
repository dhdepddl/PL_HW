#lang plai

(define-type weed
  [leaf]
  [branch (left weed?)
          (right weed?)]
  [stem (next weed?)])

(define (weed-forks w)
  (type-case w
    [leaf 1]
    [branch (l r) (+ (weed-forks l) (weed-forks r))]
    [stem (n) (weed-forks n)]))