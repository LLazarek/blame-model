#lang racket

(require redex)

(module+ test
  (require rackunit))


(define-language taint-lang
  [e (e e)
     (if e e e)
     (op e e)
     v/labeled
     x
     meta-e]
  [meta-e (labeled L e)
          (to-label/fn L (l L) e)
          (to-label/if L e)]
  [v/labeled (labeled L v)]
  [v (λ x e)
     number
     #t
     #f]
  [(x l) variable-not-otherwise-mentioned]
  [L l
     (op L L)
     (fn L (l L) ⟶ L)
     (if L L)
     (∘ L L)]
  #;[l #;label
     a b c d e f g h i j k m n o p q r s t u v w
     arg9 arg8 arg7 arg6 arg5 arg4 arg3 arg2 arg1 arg0]
  [op + -
      or and]

  [E hole
     (E e)
     (v/labeled E)
     (if E e e)
     (op E e)
     (op v/labeled E)
     (labeled L E)
     (to-label/if L E)
     (to-label/fn L (l L) E)]

  #:binding-forms (λ x e #:refers-to x) (fn L (l L) ⟶ L #:refers-to l))

(define-metafunction taint-lang
  label-not-present-in : L L e -> l
  [(label-not-present-in L_1 L_2 e)
   ,(first (set-subtract (term (a b c d e f g h i j k m n
                                  o p q r s t u v w
                                  arg9 arg8 arg7 arg6 arg5
                                  arg4 arg3 arg2 arg1 arg0))
                         (term (labels-in/L L_1))
                         (term (labels-in/L L_2))
                         (term (labels-in/e e))))])

(define-metafunction taint-lang
  labels-in/L : L -> (l ...)
  [(labels-in/L (fn L_1 (l L_2) ⟶ L_3))
   (∪ (labels-in/L L_1)
      (labels-in/L L_2)
      (labels-in/L L_3)
      (l))]
  [(labels-in/L (if L_1 L_2))
   (∪ (labels-in/L L_1)
      (labels-in/L L_2))]
  [(labels-in/L (∘ L_1 L_2))
   (∪ (labels-in/L L_1)
      (labels-in/L L_2))]
  [(labels-in/L (op L_1 L_L))
   (∪ (labels-in/L L_1)
      (labels-in/L L_2))]
  [(labels-in/L l)
   (l)])
(define-metafunction taint-lang
  labels-in/e : e -> (l ...)
  [(labels-in/e (labeled L e))
   (∪ (labels-in/L L) (labels-in/e e))]
  [(labels-in/e (to-label/if L_1 e))
   (∪ (labels-in/L L_1)
      (labels-in/e e))]
  [(labels-in/e (to-label/fn L_1 (l L_2) e))
   (∪ (labels-in/L L_1)
      (labels-in/L L_2)
      (l)
      (labels-in/e e))]
  [(labels-in/e e)
   ()])

(define-metafunction taint-lang
  ∪ : (l ...) ... -> (l ...)
  [(∪ (l_1 ...) (l_2 ...) (l_3 ...) ...)
   (∪ (l_1 ... l_2 ...) (l_3 ...) ...)]
  [(∪ (l_1 ...))
   (l_1 ...)]
  [(∪) ()])


(define-metafunction taint-lang
  δ : (op v v) -> v
  [(δ (+ v_1 v_2))
   ,(apply + (term (v_1 v_2)))]
  [(δ (- v_1 v_2))
   ,(apply - (term (v_1 v_2)))]
  [(δ (or v_1 v_2))
   ,(or (term v_1) (term v_2))]
  [(δ (and v_1 v_2))
   ,(and (term v_1) (term v_2))])

;; taint-red-->> goes from e --> v/labeled
(define taint-red
  (reduction-relation
   taint-lang
   (==> (labeled L_2 (labeled L_1 v))
        (labeled (∘ L_1 L_2) v)
        extend-trace)

   (==> (if (labeled L #t) e_2 e_3)
        (to-label/if L e_2)
        if-true)
   (==> (if (labeled L #f) e_2 e_3)
        (to-label/if L e_3)
        if-false)
   (==> (to-label/if L_1 (labeled L_2 v))
        (labeled (if L_1 L_2) v))

   (==> ((labeled L_1 (λ x e)) (labeled L_2 v))
        (to-label/fn L_1 (l L_2) (substitute e x (labeled l v)))
        (where l (label-not-present-in L_1 L_2 e))
        app/wrap)
   (==> (to-label/fn L_1 (l L_2) (labeled L_3 v))
        (labeled (fn L_1 (l L_2) ⟶ L_3) v)
        unwrap)

   (==> (op (labeled L_1 v_1) (labeled L_2 v_2))
        (labeled (op L_1 L_2) (δ (op v_1 v_2)))
        δ)

   with
   [(--> (in-hole E a) (in-hole E b))
    (==> a b)]))


(module+ test
  ;; lltodo: want to have these tests not really depend on what label
  ;; is picked for functions

  (test-->> taint-red
            (term (labeled a (labeled b 1)))
            (term (labeled (∘ b a) 1)))

  (test-->> taint-red
            (term (+ (labeled a 1) (labeled b 2)))
            (term (labeled (+ a b) 3)))
  (test-->> taint-red
            (term (- (labeled a 1) (labeled b 2)))
            (term (labeled (- a b) -1)))
  (test-->> taint-red
            (term (and (labeled a #t) (labeled b #f)))
            (term (labeled (and a b) #f)))
  (test-->> taint-red
            (term (or (labeled a #t) (labeled b #f)))
            (term (labeled (or a b) #t)))

  (test-->> taint-red
            (term (if (labeled a #t) (labeled b 1) (labeled c -1)))
            (term (labeled (if a b) 1)))
  (test-->> taint-red
            (term (if (labeled a #f) (labeled b 1) (labeled c -1)))
            (term (labeled (if a c) -1)))

  (test-->> taint-red
            (term ((labeled a (λ x x)) (labeled b #t)))
            (term (labeled (fn a (arg0 b) ⟶ arg0) #t)))
  (test-->> taint-red
            (term ((labeled k (λ x x)) (labeled j #t)))
            (term (labeled (fn k (arg0 j) ⟶ arg0) #t)))

  (test-->> taint-red
            (term ((labeled a (λ x (+ x
                                    (labeled b 2))))
                 (labeled c 3)))
            (term (labeled (fn a (arg0 c) ⟶ (+ arg0 b)) 5)))
  (test-->> taint-red
            (term ((labeled a (λ x (+ x
                                    (labeled b 2))))
                 (labeled (if c (- d b)) 3)))
            (term (labeled (fn a (arg0 (if c (- d b))) ⟶ (+ arg0 b))
                           5)))
  (test-->> taint-red
            (term ((labeled (if a (fn e (arg0 g) ⟶ arg0))
                            (λ x (+ x (labeled b 2))))
                 (labeled (if c (- d b)) 3)))
            (term (labeled (fn (if a (fn e (arg0 g) ⟶ arg0))
                             (arg1 (if c (- d b)))
                             ⟶ (+ arg1 b))
                           5)))

  (test-->> taint-red
            (term ((labeled a (λ x x))
                   (if (labeled b #t) (labeled c 1) (labeled d 2))))
            (term (labeled (fn a (arg0 (if b c)) ⟶ arg0) 1)))
  (test-->> taint-red
            (term ((labeled a (λ x x))
                   (+ (labeled c 1) (labeled d 2))))
            (term (labeled (fn a (arg0 (+ c d)) ⟶ arg0) 3)))

  (test-->> taint-red
            (term ((if (labeled a #t)
                       ((labeled f (λ x x))
                        (labeled g (λ y (+ y (labeled m 2)))))
                       (labeled h 1))
                   (if (labeled c #f)
                       (labeled d -3)
                       (- (labeled e 5) (labeled i 2)))))
            (term (labeled (fn (if a (fn f (arg0 g) ⟶ arg0))
                             (arg1 (if c (- e i)))
                             ⟶ (+ arg1 m))
                           5))))
#|
;; Need to come up with what distance means in this context.
(define-metafunction taint-lang
  distance : L L L -> number
  [(distance (∘ L_1 L_2) L_1 L_2)
   1]
  [(distance (op L_1 L_2) L_1 L_2)
   1]
  [(distance (∘ L_10 L_20) L_1 L_2)
   ])
(module+ test
  (check-equal? (term (distance (∘ a b) a b))
                1)
  (check-equal? (term (distance (+ a b) a b))
                1)
  (check-equal? (term (distance (- a b) a b))
                1)
  (check-equal? (term (distance (and a b) a b))
                1)

  (check-equal? (term (distance (if a b) a b))
                2)
  (check-equal? (term (distance (if (and a b) c) a c))
                3)
  (check-equal? (term (distance (if (and a b) (+ c d)) a c))
                4)

  (check-equal? (term (distance (fn f (arg0 a) ⟶ arg0) a f))
                2)
  (check-equal? (term (distance (fn f (arg0 (and a b)) ⟶ arg0) a f))
                3)
  (check-equal? (term (distance (fn f (arg0 (and a b)) ⟶ (or arg0 c)) a c))
                4)

  (check-equal? (term (distance (∘ a (fn f (arg0 (if b (+ c d)))
                                         ⟶ (fn g (arg1 arg0)
                                               ⟶ (+ arg1 e))))
                                a b))
                5)
  (check-equal? (term (distance (∘ a (fn f (arg0 (if b (+ c d)))
                                         ⟶ (fn g (arg1 arg0)
                                               ⟶ (+ arg1 e))))
                                e d))
                6))

|#

;; idea: just compare size of trees

(define-judgment-form taint-lang
  #:mode (linearize I O)
  )
