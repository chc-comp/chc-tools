(set-logic HORN)

(declare-fun |wdt_start| ( Bool Bool Bool Int Int Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |main@entry| ( Int Int (Array Int Int) Int Int Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) ) Bool)
(declare-fun |wdt_keepalive@_1| ( Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int Int ) Bool)
(declare-fun |wdt_stop@superio_enter.exit.thread1.split| ( Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int Int ) Bool)
(declare-fun |wdt_stop| ( Bool Bool Bool Int Int Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |wdt_keepalive| ( Bool Bool Bool Int Int Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |wdt_start@superio_enter.exit.thread1.split| ( Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int Int ) Bool)
(declare-fun |main@orig.main.exit.split| ( ) Bool)
(declare-fun |wdt_keepalive@superio_enter.exit.thread1| ( Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int Int ) Bool)
(declare-fun |main@NodeBlock4.i| ( Int Int (Array Int Int) (Array Int Int) Int Int Int (Array Int Int) (Array Int Int) Int Int Int (Array Int Int) Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |wdt_start@_1| ( Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int ) Bool)
(declare-fun |wdt_stop@_1| ( Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and


        (|main@NodeBlock4.i| Z37 I19 J19 K19 L19 M19 N19 O19 P19 Q19 R19
  S19 T19 U19 V19 W19 G19 Q38 R38 S38 T38 U38 V38)

        (= V18 ((as const (Array Int Int)) 0))

      )
      (|main@NodeBlock4.i|
  Z37
  A38
  B38
  C38
  D38
  E38
  F38
  G38
  H38
  I38
  J38
  K38
  L38
  M38
  N38
  O38
  P38
  Q38
  R38
  S38
  T38
  U38
  V38)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@orig.main.exit.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
