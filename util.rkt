#lang racket

(provide compile*
         compile-and-run
         trace
         trace/linear*)

(require redex
         "taint-lang.rkt"
         "linearize-trace.rkt")

(module+ test
  (require rackunit))

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
