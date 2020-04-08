(set-logic HORN)

(declare-fun false1 () Bool)
(declare-fun Inv (Int) Bool)

;; fact
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
;; chc
(assert (forall ((x Int) (y Int))
                (=> (and (Inv x) (<= x 10) (= y (+ x 1)))
                   (Inv y))))

(assert (forall ((x Int)) (=> (and (Inv x) (> x 15)) false1)))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false1)))

(assert (forall ((x Bool)) (=> false1 false)))

(check-sat)
(exit)
