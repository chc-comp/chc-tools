

(set-logic HORN)
(declare-fun pred (Int Int) Bool)

(assert
  (forall ((n Int) (m Int))
    (=> (>= n 0) (pred n m))
  )
)

(assert
  (forall ((n Int) (m Int))
    (=> (pred n m) false)
  )
)

(check-sat)