

(set-logic HORN)
(set-info :status sat)

(declare-fun Inv (Int) Bool)

;; fact
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
;; chc
(assert (forall ((x Int) (y Int))
                (=> (and (Inv x) (Inv y) (<= x 10) (= y (* x x)))
                   (Inv y))))
;; query
(assert (forall ((x Int)) (=> (and (Inv x) (> x 15)) false)))

(check-sat)
