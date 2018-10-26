#lang racket

(provide linearize)

(require redex
         "taint-lang.rkt")

(module+ test
  (require rackunit))

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
