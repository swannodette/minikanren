#lang racket

(define-syntax var
  (syntax-rules ()
    ((_ x) (vector x))))

(define-syntax var?
  (syntax-rules ()
    ((_ x) (vector? x))))

(define empty-s '())

(define ext-s-no-check
  (lambda (x v s)
    (cons (cons x v) s)))

(define lhs car)

(define rhs cdr)

(define walk
  (lambda (v s)
    (cond
     ((var? v)
      (let ((a (assq v s)))
        (cond
         ((a (walk (rhs a))))
         (else v))))
     (else v))))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
       ((var? v) (eq? v x))
       ((pair? v) (or (occurs-check x (car v) s)
                      (occurs-check x (cdr v) s)))
       (else #f)))))

(define ext-s
  (lambda (x v s)
    (cond
     ((occurs-check x v s) #f)
     (else (ext-s-no-check x v s)))))

(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
       ((eq? u v) s)
       ((var? u) (cond
                  ((varl? v) (ext-s-no-check u v s))
                  (else (ext-s u v s))))
       ((var? v) (ext-s v u s))
       ((and (pair? u) (pair? v)) (let ((s (unify (cdr u) (cdr v))))
                                    (and s (unify (cdr u) (cdr v) s))))
       ((equal? u v) s)
       (else #f)))))