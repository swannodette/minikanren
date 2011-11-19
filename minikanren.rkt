#lang racket

(provide var
         run
         ==
         ==-no-check
         fresh
         conde
         succeed
         fail
         lambdaf@
         lambdag@
         bind*
         case-inf)

(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))

(define-syntax comment
  (syntax-rules ()
    ((_ ...) #f)))

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
           (a (walk (rhs a) s))
           (else v))))
      (else v))))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v)
         (or (occurs-check x (car v) s)
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
                    ((var? v) (ext-s-no-check u v s))
                    (else (ext-s u v s))))
        ((var? v) (ext-s v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify (car u) (car v) s)))
           (and s (unify (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

(define unify-no-check
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) s)
        ((var? u) (ext-s-no-check u v s))
        ((var? v) (ext-s-no-check v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify-no-check (car u) (car v) s)))
           (and s (unify-no-check (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

(define reify
  (lambda (v s)
    (let ((v (walk* v s)))
      (walk* v (reify-s v empty-s)))))

(define walk*
  (lambda (v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) v)
        ((pair? v) (cons (walk* (car v) s)
                         (walk* (cdr v) s)))
        (else v)))))

(define reify-name
  (lambda (n)
    (string->symbol (string-append "_." (number->string n)))))

(define reify-s
  (lambda (v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (ext-s v (reify-name (length s)) s))
        ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
        (else s)))))

(define-syntax lambdag@
  (syntax-rules ()
    ((_ (s) e) (lambda (s) e))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define succeed
  (lambdag@ (a) a))

(define fail
  (lambdag@ (a) (mzero)))

(define-syntax mzero
  (syntax-rules ()
    ((_) #f)))

(define-syntax unit
  (syntax-rules ()
    ((_ a) a)))

(define-syntax choice
  (syntax-rules ()
    ((_ a f) (cons a f))))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((fp) e1) ((vp) e2) ((ap) e3) ((a f) e4))
     (let ((a-inf e))
       (cond
         ((not a-inf) e0)
         ((procedure? a-inf) (let ((fp a-inf))
                               e1))
         ((vector? a-inf) (let ((vp a-inf))
                            e2))
         ((and (pair? a-inf) (procedure? (cdr a-inf)))
          (let ((a (car a-inf)) (f (cdr a-inf))) e4))
         (else (let ((ap a-inf)) e3)))))))

(define-syntax ==
  (syntax-rules ()
    ((_ u v)
     (lambdag@ (a)
       (cond
         ((unify u v a) => (lambda (a) (unit a)))
         (else (mzero)))))))

(define-syntax ==-no-check
  (syntax-rules ()
    ((_ u v)
     (lambdag@ (a)
       (cond
         ((unify-no-check u v a) => (lambda (a) (unit a)))
         (else (mzero)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 gp ...) ...)
     (lambdag@ (a)
       (inc
        (mplus* (lazy-bind* (g0 a) g ...)
                (lazy-bind* (g1 a) gp ...)
                ...))))))

(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0 (lambdaf@ () (mplus* e ...))))))

(define mplus
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((fp) (inc (mplus (f) fp)))
      ((v) (let ((ap (vector-ref v 0))
                 (gp (vector-ref v 1)))
             (inc (mplus (f) (lambdaf@ () (bind ap gp))))))
      ((a) (choice a f))
      ((a fp) (choice a (lambdaf@ () (mplus (f) fp)))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (a)
       (inc
        (let ((x (var 'x)) ...)
          (lazy-bind* (g0 a) g ...)))))))

(define-syntax lazy-bind*
  (syntax-rules ()
    ((_ (g s)) (vector s g))
    ((_ (g0 s) g1 ...)
     (vector s
       (lambdag@ (a)
         (bind* (g0 a) g1 ...))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g1 ...)
     (vector e
       (lambdag@ (a)
         (bind* (g0 a) g1 ...))))))

(define bind
  (lambda (a-inf g)
    (case-inf a-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((v) (let ((ap (vector-ref v 0))
                 (gp (vector-ref v 1)))
             (vector (inc (bind ap g)) gp)))
      ((a) (g a))
      ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (let ((x (var 'x)))
       (map (lambda (a)
              (reify x a))
            (take n
                  (lambdaf@ ()
                    ((fresh () g0 g ...)
                     empty-s))))))))

(define take
  (lambda (n f)
    (if (and n (zero? n))
        '()
        (case-inf (f)
          (() '())
          ((f) (take n f))
          ((v) (let ((ap (vector-ref v 0))
                     (gp (vector-ref v 1)))
                 (take n (lambda () (bind ap gp)))))
          ((a) (list a))
          ((a f) (cons a (take (and n (- n 1)) f)))))))

(define appendo
   (lambda (l s out)
     (conde
       ((== l '()) (== s out))
       ((fresh (a d res)
          (== `(,a . ,d) l)
          (appendo d s res)
          (== `(,a . ,res) out))))))

(define nullo
  (lambda (x)
    (== '() x)))

(define membo
  (lambda (elt ls)
    (fresh (d a)
      (conde
        ((nullo ls) fail)
        ((== (cons elt d) ls))
        ((== (cons a d) ls) (membo elt d))))))

(define on-righto
  (lambda (e1 e2 ls)
    (fresh (d a r)
      (conde
        ((nullo ls) fail)
        ((== (cons a '()) ls) fail)
        ((== (cons e1 d) ls) (== (cons e2 r) d))
        ((== (cons a d) ls) (on-righto e1 e2 d))))))

(define next-too
  (lambda (e1 e2 ls)
    (conde
      ((on-righto e1 e2 ls))
      ((on-righto e2 e1 ls)))))

(define test-zebra
  (lambda (n)
    (cond
      ((zero? n) '())
      (else (begin
              (zebrao)
              (test-zebra (sub1 n)))))))

(define zebrao
  (lambda ()
    (run #f (h)
         (fresh (a1 a2 a3 a4 a5
                    b1 b2 b3 b4 b5
                    c1 c2 c3 c4 c5
                    d1 d2 d3 d4 d5
                    e1 e2 e3 e4 e5)
                (== h `((,a1 ,a2 ,a3 ,a4 ,a5)
                        (,b1 ,b2 ,b3 ,b4 ,b5)
                        (,c1 ,c2 ,c3 ,c4 ,c5)
                        (,d1 ,d2 ,d3 ,d4 ,d5)
                        (,e1 ,e2 ,e3 ,e4 ,e5)))
                (== a1 'norwegian)
                (== c3 'milk)
                (fresh (t1 t2 t3)
                       (membo `(englishman ,t1 ,t2 ,t3 red) h))
                (fresh (t1 t2 t3 t4 t5 t6 t7 t8)
                  (on-righto `(,t1 ,t2 ,t3 ,t4 ivory)
                             `(,t5 ,t6 ,t7 ,t8 green) h))
                (fresh (t1 t2 t3 t4 t5 t6 t7 t8)
                  (next-too `(norwegian ,t1 ,t2 ,t3 ,t4)
                            `(,t5 ,t6 ,t7 ,t8 blue) h))
                (fresh (t1 t2 t3)
                       (membo `(,t1 kools ,t2 ,t3 yellow) h))
                (fresh (t1 t2 t3)
                       (membo `(spaniard ,t1 ,t2 dog ,t3) h))
                (fresh (t1 t2 t3)
                       (membo `(,t1 ,t2 coffee ,t3 green) h))
                (fresh (t1 t2 t3)
                       (membo `(ukrainian ,t1 tea ,t2 ,t3) h))
                (fresh (t1 t2 t3)
                       (membo `(,t1 luckystrikes oj ,t2 ,t3) h))
                (fresh (t1 t2 t3)
                       (membo `(japanese parliaments ,t1 ,t2 ,t3) h))
                (fresh (t1 t2 t3)
                       (membo `(,t1 oldgolds ,t2 snails ,t3) h))
                (fresh (t1 t2 t3 t4 t5 t6 t7 t8)
                  (next-too `(,t1 ,t2 ,t3 horse ,t4) 
                            `(,t5 kools ,t6 ,t7 ,t8) h))
                (fresh (t1 t2 t3 t4 t5 t6 t7 t8)
                  (next-too `(,t1 ,t2 ,t3 fox ,t4)
                            `(,t5 chesterfields ,t6 ,t7 ,t8) h))
                (fresh (t1 t2 t3 t4)
                       (membo `(,t1 ,t2 water ,t3 ,t4) h))
                (fresh (t1 t2 t3 t4)
                       (membo `(,t1 ,t2 ,t3 zebra ,t4) h))))))


(define rember*o
  (lambda (x ls out)
    (conde
      ((== '() ls) (== ls out))
      ((fresh (a d b e)
         (== `(,a . ,d) ls)
         (conde
           ((== `(,b . ,e) a)
            (fresh (res0 res1)
             (rember*o x a res0)
             (rember*o x d res1)
             (== `(,res0 . ,res1) out)))
           ((== x a)
             (rember*o x d out))
           ((fresh (res)
              (rember*o x d res)
              (== `(,a . ,res) out)))))))))

(comment
 (time (zebrao))

 (time
  (run 100 (q)
       (fresh (x l)
         (rember*o x l '((b) c d))
         (== `(,x ,l) q))))

 (define nevero
   (lambda ()
     (fresh ()
       (nevero))))

 (run #f (q)
   (nevero)
   (== #t #f))

 )

(comment
 ;; works!
 ;; but not if appendo is the first goal
 (run 7 (q)
      (fresh (l s)
        (appendo l s '(a b c d e))
        (== `(,l ,s) q)))

 ;; ~1000ms slightly slower
 (time
  (do ((i 0 (+ i 1))) ((> i 4000)) 
    (run 7 (q)
         (fresh (l s)
           (appendo l s '(a b c d e))
           (== `(,l ,s) q)))))
 )

(comment
 (define rember*o
  (lambda (x ls out)
    (conde
      ((== '() ls) (== ls out))
      ((fresh (a d b e)
         (== `(,a . ,d) ls)
         (conde
           ((== `(,b . ,e) a)
            (fresh (res0 res1)
             (rember*o x a res0)
             (rember*o x d res1)
             (== `(,res0 . ,res1) out)))
           ((== x a)
             (rember*o x d out))
           ((fresh (res)
              (rember*o x d res)
              (== `(,a . ,res) out)))))))))
 (run 6 (q)
      (fresh (l s)
        (appendo l s '(a b c d e))
        (== `(,l ,s) q)))

 ;; 915ms
 (time
  (do ((i 0 (+ i 1))) ((> i 4000)) 
    (run 6 (q)
         (fresh (l s)
           (appendo l s '(a b c d e))
           (== `(,l ,s) q)))))

 (define f1 (fresh () f1))

 (run 1 (q)
      (conde
        (f1)
        ((== #f #f))))

 (define f2
   (fresh ()
     (conde
       (f2 (conde
             (f2)
             ((== #f #f))))
       ((== #f #f)))))

 (run 5 (q)
      f2)

 )
