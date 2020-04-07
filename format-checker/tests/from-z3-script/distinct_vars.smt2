
(set-logic HORN)
(declare-fun pred (Int Int) Bool)

(assert
  (forall ((n Int))
    (=> (and (>= n 0)) (pred n n))
  )
)

(assert
  (forall ((n Int) (m Int))
    (=> (and (pred n m)) false)
  )
)

(check-sat)