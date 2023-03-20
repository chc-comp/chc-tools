(set-logic HORN)

(declare-datatypes ((E_0 0)) (((x_0 (proj_0 E_0)(proj_1 E_0))(x_1 (proj_2 E_0)(proj_3 E_0))(EX_0 )(EY_0 ))))
(declare-datatypes ((list_0 0)) (((nil_0 )(cons_0 (head_0 list_0)(tail_0 list_0)))))
(declare-datatypes ((Tok_0 0)) (((C_0 )(D_0 )(X_0 )(Y_0 )(Plus_0 )(Mul_0 ))))

(declare-fun |diseqE_0| ( E_0 E_0 ) Bool)
(declare-fun |x_5| ( list_0 list_0 list_0 ) Bool)
(declare-fun |assoc_0| ( E_0 E_0 ) Bool)
(declare-fun |lin_0| ( list_0 E_0 ) Bool)
(declare-fun |linTerm_0| ( list_0 E_0 ) Bool)

(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (and (= A (x_1 E F)) (= B (x_0 C D)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_0 B C)) (= v_3 EX_0))
      )
      (diseqE_0 A v_3)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_0 B C)) (= v_3 EY_0))
      )
      (diseqE_0 A v_3)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (and (= A (x_0 E F)) (= B (x_1 C D)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_0 B C)) (= v_3 EX_0))
      )
      (diseqE_0 v_3 A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_0 B C)) (= v_3 EY_0))
      )
      (diseqE_0 v_3 A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_1 B C)) (= v_3 EX_0))
      )
      (diseqE_0 A v_3)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_1 B C)) (= v_3 EY_0))
      )
      (diseqE_0 A v_3)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_1 B C)) (= v_3 EX_0))
      )
      (diseqE_0 v_3 A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (x_1 B C)) (= v_3 EY_0))
      )
      (diseqE_0 v_3 A)
    )
  )
)
(assert
  (forall ( (v_0 E_0) (v_1 E_0) ) 
    (=>
      (and
        (and true (= v_0 EX_0) (= v_1 EY_0))
      )
      (diseqE_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 E_0) (v_1 E_0) ) 
    (=>
      (and
        (and true (= v_0 EY_0) (= v_1 EX_0))
      )
      (diseqE_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (diseqE_0 C E)
        (and (= A (x_0 E F)) (= B (x_0 C D)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (diseqE_0 D F)
        (and (= A (x_0 E F)) (= B (x_0 C D)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (diseqE_0 C E)
        (and (= A (x_1 E F)) (= B (x_1 C D)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (diseqE_0 D F)
        (and (= A (x_1 E F)) (= B (x_1 C D)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (assoc_0 E B)
        (assoc_0 F C)
        (and (= D (x_1 E F)) (= A (x_1 B C)))
      )
      (assoc_0 D A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) (G E_0) (H E_0) ) 
    (=>
      (and
        (assoc_0 H A)
        (and (= B (x_0 C D)) (= C (x_0 E F)) (= G H) (= A (x_0 E (x_0 F D))))
      )
      (assoc_0 G B)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (assoc_0 E B)
        (assoc_0 F C)
        (and (= A (x_0 B C)) (= D (x_0 E F)) (= B EX_0))
      )
      (assoc_0 D A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (assoc_0 E B)
        (assoc_0 F C)
        (and (= A (x_0 B C)) (= D (x_0 E F)) (= B EY_0))
      )
      (assoc_0 D A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) (G E_0) (H E_0) ) 
    (=>
      (and
        (assoc_0 G B)
        (assoc_0 H C)
        (and (= B (x_1 D E)) (= F (x_0 G H)) (= A (x_0 B C)))
      )
      (assoc_0 F A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) ) 
    (=>
      (and
        (and (= A EX_0) (= B A))
      )
      (assoc_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) ) 
    (=>
      (and
        (and (= A EY_0) (= B A))
      )
      (assoc_0 B A)
    )
  )
)
(assert
  (forall ( (A list_0) (B list_0) (C Tok_0) (D list_0) (E list_0) (F list_0) ) 
    (=>
      (and
        (x_5 F D B)
        (and (= A (cons_0 C D)) (= E (cons_0 C F)))
      )
      (x_5 E A B)
    )
  )
)
(assert
  (forall ( (A list_0) (B list_0) (C list_0) ) 
    (=>
      (and
        (and (= A nil_0) (= C B))
      )
      (x_5 C A B)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E list_0) (F list_0) (G list_0) (H list_0) (v_8 list_0) (v_9 list_0) ) 
    (=>
      (and
        (lin_0 F A)
        (x_5 G F v_8)
        (x_5 H v_9 G)
        (and (= v_8 (cons_0 D_0 nil_0))
     (= v_9 (cons_0 C_0 nil_0))
     (= B (x_1 C D))
     (= E H)
     (= A (x_0 C D)))
      )
      (linTerm_0 E B)
    )
  )
)
(assert
  (forall ( (A E_0) (B list_0) (C list_0) ) 
    (=>
      (and
        (lin_0 C A)
        (and (= B C) (= A EX_0))
      )
      (linTerm_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B list_0) (C list_0) ) 
    (=>
      (and
        (lin_0 C A)
        (and (= B C) (= A EY_0))
      )
      (linTerm_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D list_0) (E list_0) ) 
    (=>
      (and
        (lin_0 E A)
        (and (= D E) (= A (x_0 B C)))
      )
      (linTerm_0 D A)
    )
  )
)
(assert
  (forall ( (A E_0) (B list_0) ) 
    (=>
      (and
        (and (= B (cons_0 Y_0 nil_0)) (= A EY_0))
      )
      (lin_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B list_0) ) 
    (=>
      (and
        (and (= B (cons_0 X_0 nil_0)) (= A EX_0))
      )
      (lin_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D list_0) (E list_0) (F list_0) (G list_0) (H list_0) (v_8 list_0) ) 
    (=>
      (and
        (lin_0 E B)
        (lin_0 F C)
        (x_5 G v_8 F)
        (x_5 H E G)
        (and (= v_8 (cons_0 Mul_0 nil_0)) (= D H) (= A (x_1 B C)))
      )
      (lin_0 D A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D list_0) (E list_0) (F list_0) (G list_0) (H list_0) (v_8 list_0) ) 
    (=>
      (and
        (linTerm_0 E B)
        (linTerm_0 F C)
        (x_5 G v_8 F)
        (x_5 H E G)
        (and (= v_8 (cons_0 Plus_0 nil_0)) (= D H) (= A (x_0 B C)))
      )
      (lin_0 D A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E list_0) (F list_0) ) 
    (=>
      (and
        (assoc_0 D B)
        (lin_0 F B)
        (lin_0 E A)
        (diseqE_0 C D)
        (assoc_0 C A)
        (= E F)
      )
      false
    )
  )
)

(check-sat)
(exit)
