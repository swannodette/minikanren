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
         inc
         case-inf)

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

(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((fp) e1) ((ap) e2) ((a f) e3))
     (let ((a-inf e))
       (cond
         ((not a-inf) e0)
         ((procedure? a-inf) (let ((fp a-inf))
                               e1))
         ((and (pair? a-inf) (procedure? (cdr a-inf)))
          (let ((a (car a-inf)) (f (cdr a-inf))) e3))
         (else (let ((ap a-inf)) e2)))))))

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
        (mplus* (bind* (g0 a) g ...)
                (bind* (g1 a) gp ...)
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
      ((a) (choice a f))
      ((a fp) (choice a (lambdaf@ () (mplus (f) fp)))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (a)
       (inc
        (let ((x (var 'x)) ...)
          (bind* (g0 a) g ...)))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

(define bind
  (lambda (a-inf g)
    (case-inf a-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((a) (g a))
      ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
           (lambdaf@ ()
             ((fresh (x) g0 g ...
                     (lambdag@ (a)
                       (cons (reify x a) '())))
              empty-s))))))

(define take
  (lambda (n f)
    (if (and n (zero? n))
        '()
        (case-inf (f)
          (() '())
          ((f) (take n f))
          ((a) a)
          ((a f) (cons (car a) (take (and n (- n 1)) f)))))))

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
           (fresh (t1 t2 t3 t4)
             (membo `(,t1 ,t2 water ,t3 ,t4) h))
           (fresh (t1 t2 t3 t4)
             (membo `(,t1 ,t2 ,t3 zebra ,t4) h))
           (== h `((,a1 ,a2 ,a3 ,a4 ,a5)
                   (,b1 ,b2 ,b3 ,b4 ,b5)
                   (,c1 ,c2 ,c3 ,c4 ,c5)
                   (,d1 ,d2 ,d3 ,d4 ,d5)
                   (,e1 ,e2 ,e3 ,e4 ,e5)))
           (== a1 'norwegian)
           (== c3 'milk)
           (fresh (t1 t2 t3 t4 t5 t6 t7 t8)
             (next-too `(,t1 ,t2 ,t3 horse ,t4) 
                       `(,t5 kools ,t6 ,t7 ,t8) h))
           (fresh (t1 t2 t3 t4 t5 t6 t7 t8)
             (next-too `(,t1 ,t2 ,t3 fox ,t4)
                       `(,t5 chesterfields ,t6 ,t7 ,t8) h))
           ))))

(comment
 (time (zebrao))

 ;; ~70ms
 (time
  (run 60 (q)
       (fresh (x l)
         (rember*o x l '((b) c d))
         (== `(,x ,l) q))))

 (time
  (do ((i 0 (+ i 1))) ((> i 1000))
    (run #f (q)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #f #f)
       (== #t #f))))
 )

(comment
 ;; 915ms, the same!
 (time
  (do ((i 0 (+ i 1))) ((> i 4000)) 
    (run 6 (q)
         (fresh (l s)
           (appendo l s '(a b c d e))
           (== `(,l ,s) q)))))
 )

;; =============================================================================
;; arithmetic

(define appendo
  (lambda (l s out)
    (conde
      ((nullo l) (== s out))
      ((fresh (a d res)
         (caro l a)
         (cdro l d)   
         (appendo d s res)
         (conso a res out))))))

(define caro
  (lambda (p a)
    (fresh (d)
      (== (cons a d) p))))

(define cdro
  (lambda (p d)
    (fresh (a)
      (== (cons a d) p))))

(define conso
  (lambda (a d p)
    (== (cons a d) p)))

(define pairo
  (lambda (p)
    (fresh (a d)
      (conso a d p))))

(define build-num
  (lambda (n)
    (cond
      ((odd? n)
       (cons 1
         (build-num (quotient (- n 1) 2))))    
      ((and (not (zero? n)) (even? n))
       (cons 0
         (build-num (quotient n 2))))
      ((zero? n) '()))))

(define bit-xoro
  (lambda (x y r)
    (conde
      ((== 0 x) (== 0 y) (== 0 r))
      ((== 0 x) (== 1 y) (== 1 r))
      ((== 1 x) (== 0 y) (== 1 r))
      ((== 1 x) (== 1 y) (== 0 r)))))


(define bit-ando
  (lambda (x y r)
    (conde
      ((== 0 x) (== 0 y) (== 0 r))
      ((== 1 x) (== 0 y) (== 0 r))
      ((== 0 x) (== 1 y) (== 0 r))
      ((== 1 x) (== 1 y) (== 1 r)))))

(define addero
  (lambda (d n m r)
    (conde
      ((== 0 d) (== '() m) (== n r))
      ((== 0 d) (== '() n) (== m r)
       (poso m))
      ((== 1 d) (== '() m)
       (addero 0 n '(1) r))
      ((== 1 d) (== '() n) (poso m)
       (addero 0 '(1) m r))
      ((== '(1) n) (== '(1) m)
       (fresh (a c)
         (== `(,a ,c) r)
         (full-addero d 1 1 a c)))
      ((== '(1) n) (gen-addero d n m r))
      ((== '(1) m) (>1o n) (>1o r)
       (addero d '(1) n r))
      ((>1o n) (gen-addero d n m r)))))

(define half-addero
  (lambda (x y r c)
    (fresh ()
      (bit-xoro x y r)
      (bit-ando x y c))))

(define full-addero
  (lambda (b x y r c)
    (fresh (w xy wz)
      (half-addero x y w xy)
      (half-addero w b r wz)
      (bit-xoro xy wz c))))

(define gen-addero
  (lambda (d n m r)
    (fresh (a b c e x y z)
      (== `(,a . ,x) n)
      (== `(,b . ,y) m) (poso y)
      (== `(,c . ,z) r) (poso z)
      (full-addero d a b c e)
      (addero e x y z))))

(define poso
  (lambda (n)
    (fresh (a d)
      (== `(,a . ,d) n))))

(define >1o
  (lambda (n)
    (fresh (a ad dd)
      (== `(,a ,ad . ,dd) n))))

(define pluso
  (lambda (n m k)
    (addero 0 n m k)))

(define minuso
  (lambda (n m k)
    (pluso m k n)))

(define *o
  (lambda (n m p)
    (conde
      ((== '() n) (== '() p))
      ((poso n) (== '() m) (== '() p))  
      ((== '(1) n) (poso m) (== m p))   
      ((>1o n) (== '(1) m) (== n p))
      ((fresh (x z)
         (== `(0 . ,x) n) (poso x)
         (== `(0 . ,z) p) (poso z)
         (>1o m)
         (*o x m z)))
      ((fresh (x y)
         (== `(1 . ,x) n) (poso x)
         (== `(0 . ,y) m) (poso y)
         (*o m n p)))
      ((fresh (x y)
         (== `(1 . ,x) n) (poso x)      
         (== `(1 . ,y) m) (poso y)
         (odd-*o x n m p))))))

(define odd-*o
  (lambda (x n m p)
    (fresh (q)
      (bound-*o q p n m)
      (*o x m q)
      (pluso `(0 . ,q) m p))))

(define bound-*o
  (lambda (q p n m)
    (conde
      ((nullo q) (pairo p))
      ((fresh (x y z)
         (cdro q x)
         (cdro p y)
         (conde
           ((nullo n)
            (cdro m z)
            (bound-*o x y z '()))
           ((cdro n z) 
            (bound-*o x y z m))))))))

(define =lo
  (lambda (n m)
    (conde
      ((== '() n) (== '() m))
      ((== '(1) n) (== '(1) m))
      ((fresh (a x b y)
         (== `(,a . ,x) n) (poso x)
         (== `(,b . ,y) m) (poso y)
         (=lo x y))))))

(define <lo
  (lambda (n m)
    (conde
      ((== '() n) (poso m))
      ((== '(1) n) (>1o m))
      ((fresh (a x b y)
         (== `(,a . ,x) n) (poso x)
         (== `(,b . ,y) m) (poso y)
         (<lo x y))))))

(define <=lo
  (lambda (n m)
    (conde
      ((=lo n m))
      ((<lo n m)))))

(define <o
  (lambda (n m)
    (conde
      ((<lo n m))
      ((=lo n m)
       (fresh (x)
         (poso x)
         (pluso n x m))))))

(define <=o
  (lambda (n m)
    (conde
      ((== n m))
      ((<o n m)))))

(define /o
  (lambda (n m q r)
    (conde
      ((== r n) (== '() q) (<o n m))
      ((== '(1) q) (=lo n m) (pluso r m n)
       (<o r m))
      ((<lo m n)                        
       (<o r m)                        
       (poso q)                 
       (fresh (nh nl qh ql qlm qlmr rr rh)
         (splito n r nl nh)
         (splito q r ql qh)
         (conde
           ((== '() nh)
            (== '() qh)
            (minuso nl r qlm)
            (*o ql m qlm))
           ((poso nh)
            (*o ql m qlm)
            (pluso qlm r qlmr)
            (minuso qlmr nl rr)
            (splito rr r '() rh)
            (/o nh m qh rh))))))))

(define splito
  (lambda (n r l h)
    (conde
      ((== '() n) (== '() h) (== '() l))
      ((fresh (b n^)
         (== `(0 ,b . ,n^) n)
         (== '() r)
         (== `(,b . ,n^) h)
         (== '() l)))
      ((fresh (n^)
         (==  `(1 . ,n^) n)
         (== '() r)
         (== n^ h)
         (== '(1) l)))
      ((fresh (b n^ a r^)
         (== `(0 ,b . ,n^) n)
         (== `(,a . ,r^) r)
         (== '() l)
         (splito `(,b . ,n^) r^ '() h)))
      ((fresh (n^ a r^)
         (== `(1 . ,n^) n)
         (== `(,a . ,r^) r)
         (== '(1) l)
         (splito n^ r^ '() h)))
      ((fresh (b n^ a r^ l^)
         (== `(,b . ,n^) n)
         (== `(,a . ,r^) r)
         (== `(,b . ,l^) l)
         (poso l^)
         (splito n^ r^ l^ h))))))

(define logo
 (lambda (n b q r)
   (conde
     ((== '(1) n) (poso b) (== '() q) (== '() r))
     ((== '() q) (<o n b) (pluso r '(1) n))
     ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
     ((== '(1) b) (poso q) (pluso r '(1) n))
     ((== '() b) (poso q) (== r n))
     ((== '(0 1) b)
      (fresh (a ad dd)
        (poso dd)
        (== `(,a ,ad . ,dd) n)
        (exp2 n '() q)
        (fresh (s)
          (splito n dd r s))))
     ((fresh (a ad add ddd)
        (conde
          ((== '(1 1) b))
          ((== `(,a ,ad ,add . ,ddd) b))))
      (<lo b n)
      (fresh (bw1 bw nw nw1 ql1 ql s)
        (exp2 b '() bw1)
        (pluso bw1 '(1) bw)
        (<lo q n)
        (fresh (q1 bwq1)
          (pluso q '(1) q1)
          (*o bw q1 bwq1)
          (<o nw1 bwq1))
          (exp2 n '() nw1)
          (pluso nw1 '(1) nw)
          (/o nw bw ql1 s)
          (pluso ql '(1) ql1)
          (<=lo ql q)
          (fresh (bql qh s qdh qd)
            (repeated-mul b ql bql)
            (/o nw bw1 qh s)
            (pluso ql qdh qh)
            (pluso ql qd q)
            (<=o qd qdh)
            (fresh (bqd bq1 bq)
              (repeated-mul b qd bqd)
              (*o bql bqd bq)
              (*o b bq bq1)
              (pluso bq r n)
              (<o n bq1))))))))

(define exp2
  (lambda (n b q)
    (conde
      ((== '(1) n) (== '() q))
      ((>1o n) (== '(1) q)
       (fresh (s)
         (splito n b s '(1))))
      ((fresh (q1 b2)
         (== `(0 . ,q1) q)
         (poso q1)
         (<lo b n)
         (appendo b `(1 . ,b) b2)
         (exp2 n b2 q1)))
      ((fresh (q1 nh b2 s)
         (== `(1 . ,q1) q)
         (poso q1)
         (poso nh)
         (splito n b s nh)
         (appendo b `(1 . ,b) b2)
         (exp2 nh b2 q1))))))

(define repeated-mul
  (lambda (n q nq)
    (conde
      ((poso n) (== '() q) (== '(1) nq))
      ((== '(1) q) (== n nq))
      ((>1o q)
       (fresh (q1 nq1)
         (pluso q1 '(1) q)
         (repeated-mul n q1 nq1)
         (*o nq1 n nq))))))

(define expo
  (lambda (b q n)
    (logo n b q '())))

(comment
 (run #f (s)
   (fresh (x y)
     (pluso x y '(1 0 1))
     (== `(,x ,y) s)))

 (time
  (run 34 (t)
    (fresh (x y r)
      (*o x y r)
      (== `(,x ,y ,r) t))))

 ;; 17s
 (time
  (run 9 (s)
    (fresh (b q r)
      (logo '(0 0 1 0 0 0 1) b q r)
      (>1o q)
      (== `(,b ,q ,r) s))))
 )
