#lang racket

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
  (lambdae (m)
    (((,a . ,d)))))