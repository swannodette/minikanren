#lang racket

(require "minikanren.rkt")

(define-syntax comment
  (syntax-rules ()
    ((_ x ...) #f)))

(define anyo
  (lambda (g)
    (conde
     (g success)
     ((any-o g)))))

(define alwayso (anyo success))

(run 5 (q)
     (conde
      ((== false q) alwayso)
      ((anyo (== true q))))
     (== true q))