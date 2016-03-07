#lang plai
;#1
;dollar->won: number -> number

;to compute amount of won equivalent to a given number of dollars
;won/dollar conversion is rate of 11000 won per dollar

(define (dollar->won dol)
  (* dol 1100))

(test (dollar->won 7/22) 350)
(test (dollar->won 50) 55000)


;#2
;volume-cuboid: number number number -> number

;to compute to volume of a cuboid 
;which has given three integer numbers as its lengths of three sides
;if input value is not positive integer, return -1

(define (volume-cuboid a b c)
  (cond
    [(and (and (integer? a) (>= a 0))
          (and (and (integer? b) (>= b 0))
               (and (integer? c) (>= c 0)))) (* a (* b c))]
    [else -1]))

(test (volume-cuboid 3 5 2) 30)
(test (volume-cuboid 9 3 8) 216)
(test (volume-cuboid 0 3 -2) -1)


;#3
;is-even?: number -> boolean

;return true if given integer is even
;and return false if given integer is odd
;and return false if given number is not integer

(define (is-even? num)
  (cond
    [(integer? num) (= 0 (remainder num 2))]
    [else false]))

(test (is-even? 3) false)
(test (is-even? 258738) true)
(test (is-even? 1.3) false)


;#4
;gcd: number number -> number

;compute greatest common divisor of given two integer
;if the input number is not integer, return -1
;if the input number is negative integer, change the number to its absolute value

(define (euclid m n)
  (cond
    [(= n 0) m]
    [(= (remainder m n) 0) n]
    [else (euclid n (remainder m n))]))

(define (gcd a b)
  (cond
    [(and (integer? a) (integer? b)) (euclid (max (abs a) (abs b)) (min (abs a) (abs b)))]
    [else -1]))

(test (gcd 372 42) 6)
(test (gcd -39 201) 3)
(test (gcd 0 99) 99)
(test (gcd 1.89 2) -1)


;#5
;lcm: number number -> number

;compute least common multiple of given two integer
;if at least one of the input number is zero, return zero
;if at least one of the input number is not integer, return -1
;if the input number is negative integer,
;sign of return value follow the sign of multiple of two input value
;by using gcd function

(define (lcm a b)
  (cond
    [(or (= a 0) (= b 0)) 0]
    [(and (integer? a) (integer? b)) (* a (/ b (gcd a b)))]
    [else -1]))

(test (lcm 50 2) 50)
(test (lcm 249 72) 5976)
(test (lcm -39 201) -2613)
(test (lcm 0 1) 0)
(test (lcm 3 3) 3)
(test (lcm 1 -1) -1)
(test (lcm 0.5 3/4) -1)