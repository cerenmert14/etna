#lang racket

(require "../src/impl.rkt")
(require "../src/spec.rkt")
(require rackcheck)
(require rackcheck/shrink-tree)
(require data/maybe)
(require racket/trace)

(require racket/dict)
(require (for-syntax racket/base racket/set syntax/transformer))

;; vars is a list of pairs of keywords to #f or a domain checker/possible generator
(struct property-data (env-param vars pres test-vars test)
  #:sealed
  #:authentic
  #:reflection-name 'property)

(define (check-property/skip-preconds p env)
  (parameterize ([(property-data-env-param p) env])
    ((property-data-test p))))

(define (check-property p env)
  (parameterize ([(property-data-env-param p) env])
    (cond
      [(ormap (λ (pre) (not ((cdr pre)))) (property-data-pres p)) 'discard]
      [((property-data-test p)) 'pass]
      [else 'fail])))

(define-for-syntax (find-vars stx vars)
  (define (top-vars stx)
    (syntax-case stx (#%top)
      [(#%top . x)
       (if (memf (λ (y) (free-identifier=? y #'x)) vars)
           (list (syntax->datum #'x))
           '())]
      [(s . rst) (foldl (λ (stx st) (set-union st (top-vars stx)))
                        (top-vars #'s)
                        (syntax->list #'rst))]
      [_ '()]))
  (top-vars (expand stx)))

(define-for-syntax (parse-property stx)
  #`(let ([env (make-parameter #f)])
      #,(let loop ([stx stx]
                   [vars '()]
                   [pres '()])
          (syntax-case stx (forall implies)
            [((forall x) . rst)
             (when (memf (λ (y) (free-identifier=? #'x y)) vars)
               (raise-syntax-error 'forall "duplicate identifier" #'x))
             #`(let-syntax ([x (make-variable-like-transformer
                                (λ (stx)
                                  #'(dict-ref (env) 'x)))])
                 #,(loop #'rst (cons #'x vars) pres))]
            [((forall x . ys) . rst)
             (loop #'((forall x) (forall . ys) . rst) vars pres)]
            [((implies e) . rst)
             (let ([used (find-vars #'e vars)]
                   [p (car (generate-temporaries #'(impl)))])
               #`(let ([#,p (thunk e)])
                   #,(loop #'rst vars (cons #`(cons '#,used #,p) pres))))]

            [(e)
             #`(property-data env
                              '#,(reverse vars)
                              (list #,@(reverse pres))
                              '#,(find-vars #'e vars)
                              (thunk e))]
            [(e . rst) (raise-syntax-error 'property "undefined property form" #'e)]))))

(define-syntax property
  (lambda (stx)
    (syntax-case stx ()
      [(property e . rst)
       (parse-property #'(e . rst))])))


(define (run-generator g sz) (shrink-tree-val (g (current-pseudo-random-generator) sz)))

(define (run-generators generators n)
  (let ([result (make-hash)]
        [size (inexact->exact (round (log n 2)))])
    (for ([p (in-dict-pairs generators)])
      (dict-set! result (car p) (run-generator (cdr p) size)))
    result))


(struct run-result (time foundbug passed discards counterexample)
  #:transparent)

(define (run-result->json-str rr)
  (format "[|{\"time\": ~a, \"foundbug\": ~a, \"passed\": ~a, \"discards\": ~a, \"counterexample\": \"~a\"}|]"
          (run-result-time rr)
          (if (run-result-foundbug rr) "true" "false")
          (run-result-passed rr)
          (run-result-discards rr)
          (run-result-counterexample rr))
  )

(define (run-loop tests p generators)
  (let ([start (current-inexact-milliseconds)]
        [foundbug #f]
        [passed 0]
        [discards 0]
        [counterexample ""])
    (let loop ([n 1])
      (if (= n tests)
          'passed
          (let ([env (run-generators generators n)])
            (case (check-property p env)
              [(fail) (set! foundbug #t) (set! counterexample (~v env))]
              [(pass) (set! passed (+ 1 passed)) (loop (+ n 1)) ]
              [(discard) (set! discards (+ 1 discards)) (loop (+ n 1))]))))
    (displayln (run-result->json-str (run-result (- (current-inexact-milliseconds) start) foundbug passed discards counterexample)))))

(define (blacken-correct t)
    (match t 
        [(E) (E)]
        [(T c a k v b) (T (B) a k v b)]
    )
)

(define (balance-correct col tl k v tr)
    (match (list col tl k v tr)
        [(list (B) (T (R) (T (R) a x vx b) y vy c) z vz d) 
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list (B) (T (R) a x vx (T (R) b y vy c)) z vz d)
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list (B) a x vx (T (R) (T (R) b y vy c) z vz d)) 
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list (B) a x vx (T (R) b y vy (T (R) c z vz d)))
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list rb a x vx b) (T rb a x vx b)]
    )
)

(define (insert-aux kv t)
    (let ([x (first kv)])
     (let([vx (second kv)])
        (match t 
            [(E) (T (R) (E) x vx (E))]
            [(T rb a y vy b) (cond  [(< x y) (balance-correct rb (insert-aux kv a) y vy b)]
                                    [(< y x) (balance-correct rb a y vy (insert-aux kv b))]
                                    [else (T rb a y vx b)])]
        )))
)

(define (insert-correct kv s)
    (blacken-correct (insert-aux kv s))
)

(define gen:kv (gen:tuple gen:natural gen:natural))

(define gen:kvlist (gen:list gen:kv))

(define bespoke
    (gen:let ([kvs gen:kvlist])
        (foldl insert-correct (E) kvs))       
)

#| Validity Properties |#

(define test_prop_InsertValid
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k v)
                (equal? (prop_InsertValid t k v) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))
               )))


(define test_prop_DeleteValid
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k)
                (equal? (prop_DeleteValid t k) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural)))))


#| Post-condition Properties |#

(define test_prop_InsertPost
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v)
                (equal? (prop_InsertPost t k1 k2 v) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))
               )))



(define test_prop_DeletePost
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2)
                (equal? (prop_DeletePost t k1 k2) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural))
               )))

#| Model-based Properties |#

(define test_prop_InsertModel
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k v)
                (equal? (prop_InsertModel t k v) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))
               )))

(define test_prop_DeleteModel
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k)
                (equal? (prop_DeleteModel t k) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural))
               )))

#| Metamorphic Properties |#

(define test_prop_InsertInsert
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v1 v2)
                (equal? (prop_InsertInsert t k1 k2 v1 v2) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v1 . ,gen:natural) (v2 . ,gen:natural))
               )))

(define test_prop_InsertDelete
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v)
                (equal? (prop_InsertDelete t k1 k2 v) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))
               )))

(define test_prop_DeleteInsert
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v)
                (equal? (prop_DeleteInsert t k1 k2 v) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))
               )))

(define test_prop_DeleteDelete
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2)
                (equal? (prop_DeleteDelete t k1 k2) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural))
               )))

(provide
 test_prop_InsertValid
 test_prop_DeleteValid
 test_prop_InsertPost
 test_prop_DeletePost
 test_prop_InsertModel
 test_prop_DeleteModel
 test_prop_InsertInsert
 test_prop_InsertDelete
 test_prop_DeleteInsert
 test_prop_DeleteDelete
 )