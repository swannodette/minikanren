#lang racket

(provide comment)

(define-syntax comment
  (syntax-rules ()
    ((_ x ...) #f)))