#lang racket

(require redex)

(module+ test
  (require rackunit))

(require "taint-lang.rkt"
         "linearize-trace.rkt"
         "util.rkt")


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
                  5)))

  (check-equal?
   (trace/linear* (term {(define (f z) (λ y z))
                         ((f 5) 0)}))
   '(=> arg f top)))


(module+ test
  (test-results))
