
(set-logic HORN)
(declare-fun pred (Int Int) Bool)

(assert
  (forall ((n Int) (m Int))
    (=> (and (>= n 0)) (pred n m))
  )
)

(assert
  (forall ((n Int) (m Int))
    (=> (and (pred n m) (<= n m)) false)
  )
)

(assert
  (forall ((n Int) (m Int))
    (=> (and (pred n m) (> n m)) false)
  )
)

(check-sat)