#lang racket

(require redex
         racket/match
         redex/reduction-semantics)

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
  [(x l arg f) variable-not-otherwise-mentioned]
  [L l
     (op L L)
     (fn L (l L) ⟶ L)
     (if L L)
     (∘ L L)
     ;; seq is just there so that an ls can be an L for linearize
     (seq ls)
     op]
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


  ;; linearization terms
  [ls (l ... => l ...)
      ls/simple]
  [ls/simple (=> l ...)]

  ;; compilation
  [e/unlabeled e
               (e/unlabeled e/unlabeled)
               (if e/unlabeled e/unlabeled e/unlabeled)
               (op e/unlabeled e/unlabeled)
               v
               x]
  [def/unlabeled (define (f x) e/unlabeled)]
  [P/unlabeled {def/unlabeled ... e/unlabeled}]

  [P {def ... e}]
  [def (define (f x) e)]

  #:binding-forms
  (λ x e #:refers-to x)
  (fn L_1 (l L_2) ⟶ L_3 #:refers-to l))

;; Compare expressions modulo alpha equivalence
(default-language taint-lang)

;; Not used currently, using `fresh` in reduction-relation instead
#;(define-metafunction taint-lang
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

   ;; This causes shadowing bindings to be created
   ;; ⟶ confusing
   #;(==> ((labeled L_1 (λ x e)) (labeled L_2 v))
        (to-label/fn L_1 (l L_2) (substitute e x (labeled l v)))
        (where l (label-not-present-in L_1 L_2 e))
        app/wrap)
   ;; So use builtin fresh instead, which makes fresh labels that
   ;; aren't present in the whole program (ie including the ctx)
   (==> ((labeled L_1 (λ x e)) (labeled L_2 v))
        (to-label/fn L_1 (arg L_2) (substitute e x (labeled arg v)))
        (fresh arg)
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
                             (arg0 (if c (- d b)))
                             ⟶ (+ arg0 b))
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
                             (arg0 (if c (- e i)))
                             ⟶ (+ arg0 m))
                           5))))

(define-metafunction taint-lang
  reverse : ls/simple -> ls/simple
  [(reverse (=> l_1 l_2 ...))
   (extend (reverse (=> l_2 ...)) l_1)]
  [(reverse (=> l))
   (=> l)]
  [(reverse (=>))
   (=>)])

(define-metafunction taint-lang
  extend : ls l -> ls
  [(extend (l_1a ... => l_1b ...) l_2)
   (l_1a ... => l_1b ... l_2)])

(define-metafunction taint-lang
  append : ls ls/simple -> ls
  [(append (l_1a ... => l_1b ...) (=> l_2b ...))
   (l_1a ... => l_1b ... l_2b ...)])

(define-metafunction taint-lang
  prepend : ls ls -> ls
  [(prepend ls_1 ls_2)
   (reverse (append (reverse ls_2) (reverse ls_1)))])


(define-judgment-form taint-lang
  #:mode (linearize I O)
  #:contract (linearize L ls)
  [(linearize L_1 (l_1a ... => l_1b ...))
   (linearize L_2 ls_2)
   (linearize (substitute L_3
                          l
                          (seq (append ls_2 (reverse (=> l_1b ...)))))
              (l_3a ... => l_3b ...))
   ---
   (linearize (fn L_1 (l L_2) ⟶ L_3)
              (l_1a ... l_3a ... => l_3b ... l_1b ...))]

  [(linearize L_1 (l_1a ... => l_1b ...))
   (linearize L_2 ls_2)
   ---
   (linearize (if L_1 L_2)
              (prepend ls_2 (=> l_1a ... l_1b ...)))]

  [(linearize L_1 ls_1)
   (linearize L_2 ls_2)
   (where/error (=> l_1b ...) ls_1)
   (where/error (=> l_2b ...) ls_2)
   ---
   (linearize (∘ L_1 L_2) (=> l_1b ... l_2b ...))]

  [(linearize L_1 (l_1a ... => l_1b ...))
   (linearize L_2 (l_2a ... => l_2b ...))
   ---
   (linearize (op L_1 L_2) (l_1a ... l_1b ... l_2a ... l_2b ... => op))]

  [---
   (linearize l (=> l))]

  [---
   (linearize (seq ls) ls)])


(module+ test
  ;; linearize sanity check
  (check-equal?
   (apply-reduction-relation*
    linearize
    (term (fn (∘ g t) (arg1 (fn (∘ m t) (arg0 t)
                                ⟶ (∘ f m)))
              ⟶
              (fn arg1 (arg0 g)
                  ⟶
                  (fn (∘ i f) (arg1 arg0)
                      ⟶
                      arg1)))))
   (list (term (=> g g t t m m f f i i f f m m t t g g t)))))


(define-metafunction taint-lang
  auto-label : P/unlabeled -> P
  [(auto-label {e/unlabeled})
   {(propogate-label top e/unlabeled #t)}]
  [(auto-label {(define (f x) e/unlabeled_1) def/unlabeled ... e/unlabeled})
   {(define (f x) (propogate-label f e/unlabeled_1 #f))
    ,@(term (auto-label {def/unlabeled ... e/unlabeled}))}])

(define-metafunction taint-lang
  ;;                               ,-- top label?
  propogate-label : l e/unlabeled v -> e
  [(propogate-label l (labeled L e/unlabeled) #t)
   (labeled l (labeled L e/unlabeled))]
  [(propogate-label l v v_top?)
   (labeled l v)]
  [(propogate-label l x #f)
   x]
  [(propogate-label l x #t)
   (labeled l x)]
  [(propogate-label l (e/unlabeled_1 e/unlabeled_2) v_top?)
   ((propogate-label l e/unlabeled_1 v_top?)
    (propogate-label l e/unlabeled_2 v_top?))]
  [(propogate-label l (if e/unlabeled_1 e/unlabeled_2 e/unlabeled_3) v_top?)
   (if (propogate-label l e/unlabeled_1 v_top?)
       (propogate-label l e/unlabeled_2 v_top?)
       (propogate-label l e/unlabeled_3 v_top?))]
  [(propogate-label l (op e/unlabeled_1 e/unlabeled_2) v_top?)
   (op (propogate-label l e/unlabeled_1 v_top?)
       (propogate-label l e/unlabeled_2 v_top?))])

(module+ test
  (check-equal? (term (auto-label {((λ x x) 5)}))
                '{((labeled top (λ x x))
                   (labeled top 5))})
  (check-equal? (term (auto-label {(define (f x) x) (f 5)}))
                '{(define (f x) x)
                  ((labeled top f) (labeled top 5))}))

(define-metafunction taint-lang
  compile : P -> e
  [(compile {e})
   e]
  [(compile {(define (f x) e_body) def ... e})
   (compile (substitute {def ... e}
                        f
                        (labeled f (λ x e_body))))])

(define-metafunction taint-lang
  compile* : P/unlabeled -> e
  [(compile* P/unlabeled)
   (compile (auto-label P/unlabeled))])

(module+ test
  (check-equal? (term (compile* {((λ x x) 5)}))
                '((labeled top (λ x x))
                  (labeled top 5)))
  (check-equal? (term (compile* {(define (f x) x) (f 5)}))
                '((labeled top (labeled f (λ x x)))
                  (labeled top 5)))
  (check-equal?
   (term (compile*
          {(define (add1 x) (+ x 1))
           (define (f x) (add1 x))
           (f 5)}))
   '((labeled
      top
      (labeled f (λ x ((labeled add1 (λ x (+ x
                                             (labeled add1 1))))
                       x))))
     (labeled top 5)))
  (check-true
   (alpha-equivalent?
    taint-lang
    (term (compile*
           {(define (add1 x) (+ x 1))
            (define (f x) (add1 x))
            (define (g h) (λ x (h x)))
            ((g f) 5)}))
    '(((labeled top
                (labeled g (λ h (labeled g (λ x (h x))))))
       (labeled top
                (labeled f (λ y ((labeled add1 (λ z (+ z (labeled add1 1))))
                                 y)))))
      (labeled top 5)))))

(define (compile-and-run p)
  (apply-reduction-relation* taint-red
                             (term (compile* ,p))))

(define value-trace
  (compose1 first
            (term-match taint-lang
                        [(labeled L v) (term L)])))

(define (trace p)
  (let ([results (compile-and-run p)])
    (if (empty? results)
        (error 'trace "Program ~v does not reduce" p)
        (value-trace (first results)))))

(module+ test
  (check-equal? (trace (term {(define (f x) x) (f 5)}))
                '(fn (∘ f top) (arg top) ⟶ arg)))

(define (trace/linear p)
  (first (apply-reduction-relation* linearize (trace p))))


(define-metafunction taint-lang
  collapse : ls -> ls
  [(collapse (l_a_a ... l l l_a_b ... => l_b ...))
   (collapse (l_a_a ... l l_a_b ... => l_b ...))]
  [(collapse (l_a ... => l_b_a ... l l l_b_b ...))
   (collapse (l_a ... => l_b_a ... l l_b_b ...))]
  [(collapse ls)
   ls])

(define (trace/linear* p)
  (term (collapse ,(trace/linear p))))

(module+ test
  (check-equal?
   (trace/linear* (term {(define (f x) x) (f 5)}))
   '(=> top f top))

  (check-equal?
   (trace/linear*
    (term {(define (g h) (h 5))
           (define (i x) x)
           (define (f x) (i x))
           (define (m x) f)
           (g (m 1))}))
   '(=> g top m f i f m top g top)))




(module+ test
  ;; lltodo:
  ;; The trace produced by this program is interesting:
  ;; The argument bound here: [[<<A>][link]] is referenced
  ;; /outside/ of the label of the function's body,
  ;; here: [[<<B>][link]]
  ;; How?
  ;; Basicallly, the function f returns a λ which captures the
  ;; argument value (and its trace!), and that λ is used later
  ;; on after the function returns.
  ;; IE, just as λs can capture values because of substitution,
  ;; λs can also capture their argument trace bindings.
  ;;
  ;; This cannot be resolved by just foregoing the argument relabeling
  ;; because our linearization rule depends on the knowledge of the
  ;; argument's labels in order to do the right thing for reversal
  (test-->>
   taint-red
   (term ((labeled (∘ g top) (λ h (h (labeled g 5))))
          ((labeled
            (∘ m top)
            (λ x«115»
              ((labeled
                f
                (λ c«116»
                  (labeled
                   f
                   (λ x«117»
                     ((if c«116»
                          (labeled add1 (λ x«118» (+ x«118» (labeled add1 1))))
                          (labeled i (λ x«119» x«119»)))
                      x«117»)))))
               (labeled m #t))))
           (labeled top 1))))
   (term (labeled
          (fn (∘ g top)
            (arg2 (fn (∘ m top)
                    (arg top)
                    ⟶ (fn f
                        (arg1 m) ;; <<A>>
                        ⟶ f)))
            ⟶
            (fn arg2
              (arg3 g)
              ⟶ (fn (if arg1 add1) ;; <<B>>
                  (arg4 arg3)
                  ⟶ (+ arg4 add1))))
          6)))

  ;; here's a simpler program demonstrating the same problem
  (test-->>
   taint-red
   (term (((labeled f (λ z (labeled f (λ y z))))
           (labeled t 5))
          (labeled t 0)))
   (term (labeled (fn (fn f
                        (arg t)
                        ⟶ f)
                    (arg1 t)
                    ⟶ arg)
                  5))))


(module+ test
  (test-results))
