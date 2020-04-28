(set-logic HORN)

(declare-fun |ULTIMATE.start_L6| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |ULTIMATE.start_ULTIMATE.startEXIT| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |ULTIMATE.start_ULTIMATE.startFINAL| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |ULTIMATE.start_L4| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |ULTIMATE.start_L-1| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |ULTIMATE.start_L27| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |ULTIMATE.start_ULTIMATE.startENTRY| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |ULTIMATE.start_L23| ( Int (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Bool ) Bool)

(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R (Array Int Int)) (S Int) (T Int) ) 
    (=>
      (and
        (ULTIMATE.start_ULTIMATE.startENTRY A R C D E S G H I T K L M N O P Q)
        (or Q (and (= J 0) (= F 0) (= B (store R 0 0))))
      )
      (ULTIMATE.start_L-1 A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R (Array Int Int)) (S (Array Int (Array Int Int))) (T (Array Int Int)) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (ULTIMATE.start_L-1 A R C S E F G T I J K U V N W X Q)
        (let ((a!1 (= D (store S L (store (select S L) M 0)))))
(let ((a!2 (and (not (<= A L))
                (= P (select (select D L) M))
                (not (= L 0))
                (= 0 M)
                (= (select R L) 0)
                (= (store T L 4) H)
                (= (store R L 1) B)
                a!1)))
  (or Q a!2)))
      )
      (ULTIMATE.start_L27 A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) ) 
    (=>
      (and
        (ULTIMATE.start_L27 A B C D E F G H I J K L M N O P Q)
        (or Q (= P 0))
      )
      (ULTIMATE.start_L4 A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) ) 
    (=>
      (and
        (ULTIMATE.start_L27 A B C D E F G H I J K L M N O P Q)
        (or Q (not (= P 0)))
      )
      (ULTIMATE.start_L6 A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R (Array Int Int)) (S Int) (T Int) (U Int) ) 
    (=>
      (and
        (ULTIMATE.start_L4 A R C D E F G H I J K S T N O U Q)
        (or Q (= (store R S 0) B))
      )
      (ULTIMATE.start_L23 A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) ) 
    (=>
      (and
        (ULTIMATE.start_L6 A B C D E F G H I J K L M N O P R)
        (= Q true)
      )
      (ULTIMATE.start_ULTIMATE.startEXIT A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) ) 
    (=>
      (and
        (ULTIMATE.start_L6 A B C D E F G H I J K L M N O P Q)
        (= Q true)
      )
      (ULTIMATE.start_L4 A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Int) ) 
    (=>
      (and
        (ULTIMATE.start_L23 A B C D E F G H I J K L M R O P Q)
        (or Q (= N O))
      )
      (ULTIMATE.start_ULTIMATE.startFINAL A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) ) 
    (=>
      (and
        (ULTIMATE.start_ULTIMATE.startFINAL A B C D E F G H I J K L M N O P Q)
        true
      )
      (ULTIMATE.start_ULTIMATE.startEXIT A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) ) 
    (=>
      (and
        (and (= I H) (= B C) (= K J) (= F G) (not Q) (= D E))
      )
      (ULTIMATE.start_ULTIMATE.startENTRY A B C D E F G H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int (Array Int Int))) (E (Array Int (Array Int Int))) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) ) 
    (=>
      (and
        (ULTIMATE.start_ULTIMATE.startEXIT A B C D E F G H I J K L M N O P Q)
        (= Q true)
      )
      false
    )
  )
)

(check-sat)
(exit)
