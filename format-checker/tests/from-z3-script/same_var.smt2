(set-logic HORN)

(declare-fun unknown
  ( Int Int ) Bool
)

(assert
  (forall ( (|$V-reftype:10| Int) (|$alpha-1:x| Int) (|$knormal:1| Int) (|$knormal:2| Int) (|$knormal:3| Int) (|$knormal:5| Int) )
    (=>
      ( and (= |$knormal:2| (+ |$alpha-1:x| 11)) (= (not (= 0 |$knormal:1|)) (> |$alpha-1:x| 100)) (= |$V-reftype:10| |$knormal:5|) (not (not (= 0 |$knormal:1|))) (unknown |$knormal:5| |$knormal:3|) (unknown |$knormal:3| |$knormal:2|) true )
      (unknown |$V-reftype:10| |$alpha-1:x|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:8| Int) (|$V-reftype:9| Int) (|$alpha-1:x| Int) (|$knormal:1| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:1|)) (> |$alpha-1:x| 100)) (= |$V-reftype:8| (- |$alpha-1:x| 10)) (not (= 0 |$knormal:1|)) (= |$V-reftype:8| |$V-reftype:9|) )
      (unknown |$V-reftype:8| |$V-reftype:9|)
    )
  )
)
(assert
  (not (exists ( (|$alpha-2:n| Int) (|$knormal:6| Int) (|$knormal:7| Int) (|$knormal:8| Int) (|$knormal:9| Int) )
    ( and (= (not (= 0 |$knormal:9|)) (= |$knormal:7| 91)) (= (not (= 0 |$knormal:6|)) (<= |$alpha-2:n| 101)) (not (not (= 0 |$knormal:9|))) (not (= 0 |$knormal:6|)) (unknown |$knormal:7| |$knormal:8|) )
    )
  )
)
(assert
  (forall ( (|$alpha-2:n| Int) (|$knormal:6| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:6|)) (<= |$alpha-2:n| 101)) (not (= 0 |$knormal:6|)) )
      false
    )
  )
)
(check-sat)


