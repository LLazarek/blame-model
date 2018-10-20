#lang racket

;; wiw: trying to work out the kinks in the reduction relation below.
;; Just tried (and doesn't work)
#;(traces taint-red
          (term ((labeled a (λ x (+ x
                                    (labeled b 2))))
                 (labeled c 3))))

(require redex)

(module+ test
  (require rackunit))


(define-language taint-lang
  [e (e e)
     (if e e e)
     (op e e)
     v
     x
     meta-e]
  [meta-e (to-label L e)
          (to-label/fn L (l L) e)]
  [v (λ x e)
     number
     #t
     #f
     (labeled L v)]
  [x variable-not-otherwise-mentioned]
  [L l
     (op L L)
     (fn L (l L) ⟶ L)
     (if L L)
     (∘ L L)]
  [l #;label
     a b c d e f g h i j k]
  [op + -
      or and]

  [E hole
     (E e)
     (v E)
     (if E e e)
     (to-label L E)
     (to-label/fn L (l L) E)]

  #:binding-forms (λ x e #:refers-to x))

(define-metafunction taint-lang
  label-not-present-in : L L e -> l
  [(label-not-present-in L_1 L_2 e)
   ,(first (set-subtract (term (a b c d e f g h i j k))
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
  [(labels-in/L l)
   (l)])
(define-metafunction taint-lang
  labels-in/e : e -> (l ...)
  [(labels-in/e (to-label L e))
   (∪ (labels-in/L L) (labels-in/e e))]
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

(require (for-syntax syntax/parse))
(define-syntax (define-builtin-metafunction stx)
  (syntax-parse stx
    [(_ name op-nonterminal operator ...)
     #'(define-metafunction taint-lang
         name : (op-nonterminal v v) -> v
         [(name (operator v_1 v_2))
          (apply operator (term (v_1 v_2)))] ...)]))
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
;; (define-builtin-metafunction δ op
;;   + - or and)

(define taint-red
  (reduction-relation
   taint-lang
   (==> (to-label L_2 (labeled L_1 v))
        (labeled (∘ L_1 L_2) v)
        extend-trace)
   (==> (to-label L v)
        (labeled L v)
        add-label)

   (==> (if (labeled L_1 #t) (labeled L_2 e_2) e_3)
        (to-label (if L_1 L_2) e_2)
        if-true)
   (==> (if (labeled L_1 #f) e_2 (labeled L_3 e_3))
        (to-label (if L_1 L_3) e_3)
        if-false)

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
  (define-syntax (test-taint-red stx)
    (syntax-parse stx
      #:datum-literals (-->>)
      [(_ t1 -->> t2)
       (syntax/loc stx
         (test-->> taint-red (term t1) (term t2)))]))


  (test-taint-red (to-label a 1)
                  -->>
                  (labeled a 1))
  (test-taint-red (to-label a (labeled b 1))
                  -->>
                  (labeled (∘ b a) 1))

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
            (term ((labeled a (λ x (+ x
                                    (labeled b 2))))
                 (labeled c 3)))
            (term (labeled (fn a (k c) ⟶ (+ k b)) 5))))
