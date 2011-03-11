#lang racket

(require "minikanren-broken.rkt")

(define-syntax comment
  (syntax-rules ()
    ((_ x ...) #f)))

;; =============================================================================
;; EXIST NEEDS INC

(define exist-needs-inc
  (lambda ()
   (letrec ((f (exist () f)))
     (run 1 (q)
          (conde
           (f)
           ((== #f #f)))))))

(define-syntax debug
  (syntax-rules ()
    ((_ x ...)
     (lambdag@ (a) (display x ...) a))))

(comment
 ;; adding inc to exist is all we need to get the first result
 (exist-needs-inc)
 )

;; =============================================================================
;; RUN NEEDS AN INC WITH CONDE

(define run-needs-an-inc-with-conde
  (lambda ()
    (letrec ((f (exist () f)))
     (run 1 (q)
          (conde
           ((debug "clause 1\n") f (== #f #f) (debug "end clause1\n"))
           ((debug "clause 2\n") (== #f #f)))))))

(comment
 ;; we can get the first result
 ;; but we just need an inc with exist, not conde
 (run-needs-an-inc-with-conde)

 ;; we can't get any more results because the second clause is exhausted
 ;; the first clause cannot generate a goal to pass to the next part of the line
 )

;; =============================================================================
;; CONDE NEEDS INC

(define conde-needs-inc
  (conde 
   (conde-needs-inc (conde 
                     (conde-needs-inc) 
                     ((== #f #f)))) 
   ((== #f #f))))

(comment
 ;; SMOKE
 ;; conde needs an inc
 ;; and mplus and bind need to preserve it!
 (run 5 (q)
      conde-needs-inc)
 )