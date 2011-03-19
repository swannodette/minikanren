#lang racket

(require "minikanren.rkt")

(define-syntax comment
  (syntax-rules ()
    ((_ x ...) #f)))

(define-syntax conda
  (syntax-rules ()
      ((_ (g0 g ...) (g1 gp ...))
       (lambdag@ (a)
                 (inc
                  (ifa ((g0 a) g ...)
                        ((g1 a) gp ...)))))))

(define-syntax condu
  (syntax-rules ()
    ((_ (g0 g ...) (g1 gp ...) ...)
     (lambdag@ (a)
               (inc
                (ifu ((g0 a) g ...)
                      ((g1 a) gp ...) ...))))))

(define-syntax ifa
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
                 (() (ifa b ...))
                 ((f) (inc (loop (f))))
                 ((a) (bind* a-inf g ...))
                 ((a f) (bind* a-inf g ...)))))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
                 (() (ifu b ...))
                 ((f) (inc (loop (f))))
                 ((a) (bind* a-inf g ...))
                 ((a f) (bind* (unit a) g ...)))))))

(run false (x)
  (conda
    ((== 'olive x) succeed)
    ((== 'oil x) succeed)))