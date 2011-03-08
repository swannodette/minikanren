#lang racket

(require "utils.rkt")
(require "minikanren.rkt")
(require "matche.rkt")

(define build-num
  (lambda (n)
    (cond
     ((zero? n) '())
     ((and (not (zero? n)) (even? n))
      (cons 0 (build-num (quotient n 2))))
     ((odd? n)
      (cons 1 (build-num (quotient (- n 1) 2)))))))

(define poso
  (lambdae (n)
    (((,a . ,d)))
    ((0))))

(comment (matche '(1 2 3) ((,a ,b ,c) 1) ((,x d ,y) 2) (5) (,w) ((a b c))))