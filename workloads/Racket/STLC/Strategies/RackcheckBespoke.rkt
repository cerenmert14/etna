#lang racket

(require "../src/impl.rkt")
(require "../src/spec.rkt")
(require rackcheck)
(require rackunit)
(require data/maybe)
(require algebraic/control/applicative)

(provide (all-defined-out))

(define nat-lst? (list*of positive?)) 

(define (gen:bind-opt g f)
    (gen:bind g 
        (lambda (maybe-x) 
            (match maybe-x
                [nothing nothing]
                [(just x) (f x)]
            )
        ))
)

(define (gen:opt g)
    (gen:bind g 
        (lambda (x) (gen:one-of (list nothing (just x)))
    ))
)

(define gen:maybe-bool 
    (gen:opt gen:boolean)
)

(define/contract (gen-var ctx t p r)
(ctx? typ? positive? nat-lst? . -> . nat-lst?)
    (match ctx
        ['() r]
        [(cons t2 ctx2) (if (= t t2) 
                                (gen-var ctx2 t (+ p 1) (append p r))
                                (gen-var ctx2 t (+ p 1) r))]
    )
)

(define (gen:zero env tau)
    (match tau 
        [(TBool) (gen:bind gen:boolean (lambda (b) (just (Bool b))))]
        [(TFun T1 T2) (gen:bind-opt (gen:zero (cons T1 env) T2) 
            (lambda (e) (just (Abs T1 e))))]
    )
)

#|(define (gen:expr env tau sz)
    (match sz 
        [0 ()]
        [x ()]
    
    )
)#|