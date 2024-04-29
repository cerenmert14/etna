#lang racket

(provide (all-defined-out))

(require "./impl.rkt")
(require rackcheck)
(require data/maybe)
(require data/functor)

(define/contract (is-BST-helper p t)
  (-> (-> integer? boolean?) tree? boolean?)
  (match t 
    [(E) #t]
    [(T c a x v b) (and (p x) (is-BST-helper p a) (is-BST-helper p b))]
  )
)

(define/contract (is-BST t)
(-> tree? boolean?)
  (match t 
    [(E) #t]
    [(T _ a x _ b) (and (is-BST a) (is-BST b) 
                        (is-BST-helper (lambda (v) (< v x)) a)
                        (is-BST-helper (lambda (v) (> v x)) b)
                   )
    ]
  )
)

(define (black-root t)
  (match t 
    [(T (R) _ _ _ _) #f]
    [_ #t]
  )
)

(define/contract (no-red-red t)
(-> tree? boolean?)
  (match t 
    [(E) #t]
    [(T (B) a _ _ b) (and (no-red-red a) (no-red-red b))]
    [(T (R) a _ _ b) (and (black-root a) (black-root b) (no-red-red a) (no-red-red b))]
  )
)

(define/contract (is-black rb)
  (color? . -> . number?)
  (match rb 
    [(B) 1]
    [(R) 0]
  )
)

(define/contract (consistent-black-height_ t)
  (tree? . ->  . pair?)
  (match t 
    [(E) (cons #t 1)]
    [(T rb a k _ b)
          (let*
            ([aRes (consistent-black-height_ a)]
             [bRes (consistent-black-height_ b)]
             [aBool (car aRes)]
             [aHeight (cdr aRes)]
             [bBool (car bRes)] 
             [bHeight (cdr bRes)])
            (cons (and (and aBool bBool) (equal? aHeight bHeight)) (+ aHeight (is-black rb))))
    ]
  )
)

(define/contract (consistent-black-height t)
  (-> tree? boolean?)
  (car (consistent-black-height_ t))
)

(define/contract (is-RBT t)
  (-> tree? maybe?)
  (just (and (is-BST t) (consistent-black-height t) (no-red-red t)))
)

(define (to-list t)
  (match t 
    [(E) '()]
    [(T c l k v r) (append (to-list l) (list (list k v)) (to-list r))]
    [_ '()]
  )
)

(define (assumes p1 p2)
  (match p1
    [(nothing) (nothing)]
    [(just #f) (nothing)]
    [(just #t) p2]
  )
)

#| ----------- |#

#| -- Validity Properties. |#

(define (prop_InsertValid t k v)
  (assumes (is-RBT t) (is-RBT (insert k v t)))
)

(define (prop_DeleteValid t k)
  (assumes (is-RBT t) (apply (lambda (x) (is-RBT x)) (delete k t)))
)


;(apply (lambda (x) (consistent-black-height x)) (delete 12 (T (B) (T (B) (T (R) (E) 4 9 (E)) 7 17 (E)) 12 23 (T (B) (T (R) (E) 24 0 (E)) 25 20 (E)))))
;(delete 12 (T (B) (T (B) (T (R) (E) 4 9 (E)) 7 17 (E)) 12 23 (T (B) (T (R) (E) 24 0 (E)) 25 20 (E))))
#| ----------- |#

#| -- Postcondition Properties. |#


(define (prop_InsertPost t k1 k2 v)
  (assumes (is-RBT t)
           (just (equal? (find k2 (insert k1 v t)) (if (equal? k1 k2) (just v) (find k2 t))))
  )
)

(define (prop_DeletePost t k1 k2)
  (assumes (is-RBT t)
           (just (equal? (apply (lambda (x) (find k2 x)) (delete k1 t)) (if (= k1 k2) (nothing) (find k2 t))))
  )           
)
#| ----------- |#

#| -- Model-based Properties. |#

(define (delete-key k l)
  (filter (lambda (kv) (not (= (first kv) k))) l) 
)

(define (l_insert k v l)
  (match l
    ['() (list (list k v))]
    [(cons (list k1 v1) xs) (cond
                              [(= k k1) (cons (list k v) xs)]
                              [(< k k1) (cons (list k v) l)]
                              [else (append (list (list k1 v1)) (l_insert k v xs))]
                            )
    ]
  )
)

(define (prop_InsertModel t k v)
  (assumes (is-RBT t)
           (just (equal? (to-list (insert k v t)) (l_insert k v (delete-key k (to-list t)))))
  )           
)

(define (prop_DeleteModel t k)
  (assumes (is-RBT t)
           (just (equal? (apply (lambda (x) (to-list x)) (delete k t)) (delete-key k (to-list t))))           
  )
)
#| ----------- |#

#| -- Metamorphic Properties. |#

(define (prop_InsertInsert t k1 k2 v1 v2)
  (assumes (is-RBT t)
           (just (equal? (to-list (insert k1 v1 (insert k2 v2 t))) 
                         (to-list (if (= k1 k2) (insert k1 v1 t) (insert k2 v2 (insert k1 v1 t))))))
  )           
)

(define (prop_InsertDelete t k1 k2 v)
  (assumes (is-RBT t)
           (just (equal? (apply (lambda (tr) (to-list (insert k1 v tr))) (delete k2 t))
                         (to-list (if (= k1 k2) (insert k1 v t) (apply (lambda (x) x) (delete k2 (insert k1 v t)))))))
  )           
)

(define (prop_DeleteInsert t k1 k2 v)
  (assumes (is-RBT t)
           (just (equal? (apply (lambda (x) (to-list x)) (delete k1 (insert k2 v t))) 
                         (to-list (if (= k1 k2) (apply (lambda (x) x) (delete k1 t)) (apply (lambda (x) (insert k2 v x)) (delete k1 t))))))
  )           
)


(define (prop_DeleteDelete t k1 k2)
  (assumes (is-RBT t)
           (just (equal? (to-list (apply (lambda (x) x) (apply (lambda (t2) (delete k1 t2)) (apply (lambda (t1) (return t1)) (delete k2 t))))) 
                         (to-list (apply (lambda (x) x) (apply (lambda (t2) (delete k2 t2)) (apply (lambda (t1) (return t1)) (delete k1 t)))))))
  )           
)

#| ----------- |#

(define (size-RBT t)
  (length (to-list t))
)