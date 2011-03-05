#lang racket

(require "minikanren.rkt")

(define-syntax comment
  (syntax-rules ()
   ((_ x ...) #f)))

(define repeat
  (lambda (n)
    (lambda (x)
      (conde
       ((== x n))
       ((ones x))))))

(define ones (repeat 1))
(define twos (repeat 2))
(define threes (repeat 3))

(define test
  (lambda (x)
    (conde
     (ones)
     (twos)
     (threes))))

(comment
 (run 4 [q] (ones q))
 (run 4 [q] (twos q))
 )
