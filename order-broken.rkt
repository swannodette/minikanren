#lang racket

(require "minikanren-broken.rkt")

(define-syntax comment
  (syntax-rules ()
   ((_ x ...) #f)))

(define repeat
  (lambda (n)
    (define repeater
      (lambda (x)
        (conde
         ((== x n))
         ((repeater x)))))
    repeater))

(define ones (repeat 1))
(define twos (repeat 2))
(define threes (repeat 3))
(define fours (repeat 4))

(define test
  (lambda (x)
    (conde
     ((ones x))
     ((twos x))
     ((threes x))
     ((fours x)))))

(comment
 (run 4 [q] (ones q))
 (run 4 [q] (twos q))
 (run 4 [q] (threes q))

 ;; miniKanren's interleaving strategy is not great
 ;; it suffers from the same problem that mplus-concat had
 ;; when dealing with many recursive goals generators
 ;; goals further down the conde don't actually get their
 ;; results interleaved fairly
 (run 16 [q] (test q))
 )
