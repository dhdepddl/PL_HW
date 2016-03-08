#lang plai

;#1
;make type with type_id : ANIMAL
;and variant_id : spider, elephant, monkey such that
;spider has two attributes: legs of type integer, space of type integer
;elephant has one attributes: space of type integer
;monkey has two attributes: intelligence of type boolean, space of type integer

(define-type ANIMAL
  [spider (legs integer?)
          (space integer?)]
  [elephant (space integer?)]
  [monkey (intelligence symbol?)
          (space integer?)])

(define mon (monkey 'smart 4))
(test (monkey? mon) true)
(test (spider? mon) false)
(test (ANIMAL? 3) false)
(test (ANIMAL? mon) true)
(test (monkey-intelligence mon) 'smart)


;#2
;need-space : ANIMAL -> number

;for given animal by input,
;return the number of space units needed to transport the given animal
;just make runtime error if the input value is not ANIMAL

(define (need-space an)
  (type-case ANIMAL an
    [spider (l s) s]
    [elephant (s) s]
    [monkey (i s) s]))

(test (need-space (spider 8 6)) 6)
(test (need-space (monkey 'dumb 2)) 2)
(test (need-space (elephant 4)) 4)


;#3
;can-talk : ANIMAL -> boolean

;for given animal by input,
;return boolean value true if the animal is monkey which intelligence is smart
;and return false otherwise
;just make runtime error if the input value is not ANIMAL


(define (can-talk an)
  (type-case ANIMAL an
    [monkey (i s)
            (cond
              [(symbol=? i 'smart) true]
              [else false])]
    [else false]))

(test (can-talk (monkey 'smart 4)) true)
(test (can-talk (monkey 'dumb 2)) false)
(test (can-talk (spider 8 4)) false)
(test (can-talk (elephant 10)) false)


;#4
;name-toys : listof symbol -> listof symbol

;by using for/list loop which return list
;and check the element by using conditional functions whether is 'robot or 'doll or 'bear or not
;if the element is 'robot, change the element to 'bb8 of type symbol
;if the element is 'doll, change the element to 'baymax of type symbol
;if the element is 'bear, change the element to 'pooh of type symbol
;just make runtime error if the input value is not list of symbol
(define (name-toys names)
  (for/list ([name names])
    (cond
      [(symbol=? name 'robot) 'bb8]
      [(symbol=? name 'doll) 'baymax]
      [(symbol=? name 'bear) 'pooh]
      [else name])))

(test (name-toys (list 'robot 'doll 'machine 'candy 'bear)) (list 'bb8 'baymax 'machine 'candy 'pooh))
(test (name-toys '(doll doll bear)) (cons 'baymax (cons 'baymax (cons 'pooh empty))))
(test (name-toys '(bb8 bb8 robot)) '(bb8 bb8 bb8))


;#5
;give-name : symbol symbol listof symbol -> listof symbol

;use same logic flow to function name-toys
;use for/list loop and conditional function to check if the element is same to old
;if it is, change the element to new
;just make runtime error if the input value is not symbol symbol list of symbol

(define (give-name old new names)
  (for/list ([name names])
    (cond
      [(symbol=? name old) new]
      [else name])))

(test (give-name 'robot 'hubo (cons 'doll (cons 'robot (cons 'bear empty)))) (list 'doll 'hubo 'bear))
(test (give-name 'candy 'chupachups '(doll candy robot)) '(doll chupachups robot))