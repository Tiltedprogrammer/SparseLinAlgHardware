grinMain =
  m <- main $
  (CSucc m_deref) <- fetch m
  (CSucc m_deref_1) <- fetch m_deref
  m_deref_2 <- fetch m_deref_1
  pure m_deref_2

main =
  i <- do
    i_1 <- store (CZero)
    store (CSucc i_1)
  j <- do
    j' <- store (CZero)
    store (CSucc j')
  var_d <- do
    var_e <- do
      store (P3plus)
    var_f <- do
      pure j
    var_n <- do
      pure var_e
    var_o <- do
      pure var_f
    store (Fap var_n var_o)
  var_g <- do
    pure i
  var_p <- do
    pure var_d
  var_q <- do
    pure var_g
  main_cont <- store (P1idCont)
  var_q' <- store (Fap var_p var_q)
  ap $ var_q' main_cont

plusCont_2 c_bind_m_1 k_plus_cont_2 =
  
  res1 <- store (CSucc c_bind_m_1)
  apply $ k_plus_cont_2 res1

plusCont_1 y z k_plus_cont =
  z_deref <- fetch z
  case z_deref of
    (CZero) ->
      evalC $ y k_plus_cont
    (CSucc n) ->
          var_a <- do
            store (P3plus)
          var_b <- store (Fap var_a n)
          cont_42 <- store (P2plusCont_2)  
          cont_42' <- store (P1apCont k_plus_cont cont_42)
          apCont $ cont_42' var_b y

plus x y k_plus =
  scrut <- do
    pure x
  scrut_h <- do
    pure scrut
  cont_43 <- store (P2plusCont_1 y)  
  cont_43' <- store (P1apCont k_plus cont_43)
  evalC $ scrut_h cont_43'
  

apply f'' a'' =

  f' <- fetch f''

  case f' of
    (P2ap) ->
      res_2 <- store (P1ap a'')
      pure res_2
    (P1ap pat_ac) ->
      ap $ pat_ac a''
    (P3apCont) ->
      res_3 <- store (P2apCont a'')
      pure res_3
    (P2apCont a''') ->
      res_4 <- store (P1apCont a''' a'')
      pure res_4
    (P1apCont a_1''' a_2''') ->
      apCont $ a_1''' a_2''' a''
    (P3plus) ->
      res_5 <- store (P2plus a'')  
      pure res_5
    (P2plus pat_af_1) ->
      res_10 <- store (P1plus pat_af_1 a'')  
      pure res_10
    (P1plus pat_af' pat_af) ->
      plus $ pat_af' pat_af a''
    (P3plusCont_1) ->
      res_6 <- store (P2plusCont_1 a'') 
      pure res_6
    (P2plusCont_1 pat_af_2) ->
      res_11 <- store (P1plusCont_1 pat_af_2 a'')
      pure res_11  
    (P1plusCont_1 pat_af_3 i_1) ->
      plusCont_1 $ pat_af_3 i_1 a''
    (P2plusCont_2) ->
      res_12 <- store (P1plusCont_2 a'')
      pure res_12
    (P1plusCont_2 pat_af_4) ->
      plusCont_2 $ pat_af_4 a''
    (P1idCont) ->
      pure a''
    (CSucc c_bind_m_r_2) ->
      pure f''
    (CZero) ->
      pure f''
    (P2evalC) ->
      res_7 <- store (P1evalC a'')
      pure res_7
    (P1evalC arg') ->
      evalC $ arg' a''
    (P3evalC2) ->
      res_8 <- store (P2evalC2 a'')
      pure res_8
    (P2evalC2 arg_1') ->
      res_9 <- store (P1evalC2 arg_1' a'')
      pure res_9
    (P1evalC2 arg_2' arg_2'') ->
      evalC2 $ arg_2' arg_2'' a''

applyC f'' a'' k_deref =
    
  f_1' <- fetch f''

  case f_1' of
    (P2ap) ->
      arg <- store (P1ap a'')
      apply $ k_deref arg
    (P1ap pat_ac_1) ->
      apCont $ pat_ac_1 a'' k_deref
    (P3plus) ->
      arg_8 <- store (P2plus a'')
      apply $ k_deref arg_8  
    (P2plus pat_af_1) ->
      plus $ pat_af_1 a'' k_deref
    (P3plusCont_1) ->
      arg_9 <- store (P2plusCont_1 a'')
      apply $ k_deref arg_9
    (P2plusCont_1 pat_af_2) ->
      plusCont_1 $ pat_af_2 a'' k_deref 
    (P2plusCont_2) ->
      plusCont_2 $ a'' k_deref
    (CSucc c_bind_m_r) ->
      apply $ k_deref f''
    (CZero) ->
      apply $ k_deref f''
    (P2evalC) ->
      arg_1 <- store (P1evalC a'')
      apply $ k_deref arg_1
    (P1evalC arg_4') ->
      evalC2 $ arg_4' k_deref a''
    (P3evalC2) ->
      arg_2 <- store (P2evalC2 a'')
      apply $ k_deref arg_2
    (P2evalC2 arg_5') ->
      arg_3 <- store (P1evalC2 arg_5' a'')
      apply $ k_deref arg_3
    (P1evalC2 arg1_3 arg2) ->
      cont_1 <- store (P1apCont k_deref a'')
      evalC2 $ arg1_3 arg2 cont_1
    (P3apCont) ->
      arg_4 <- store (P2appCont a'')
      apply $ k_deref arg_4
    (P2apCont arg1_4) ->
      arg_5 <- store (P1apCont arg1_4 a'')
      apply $ k_deref arg_5
    (P1idCont) ->
      apply $ k_deref a''



idCont p = pure p

eval q k_ref =
  v <- fetch q
  k <- fetch k_ref
  case v of
    (Fap pat_t pat) -> 
      apCont $ k_ref pat_t pat
    (P2ap) ->
      apply $ k_ref q 
    (P1ap pat_v) ->
      apply $ k_ref q 
    (Fmain) ->
      main $
    (P3apCont) ->
      apply $ k_ref q
    (P2apCont arg1_1) ->
      apply $ k_ref q
    (P1apCont arg1_2 arg2_1) ->
      apply $ k_ref q 
    (CSucc c_bind_m_r_s) ->
      apply $ k_ref q 
    (CZero) ->
      apply $ k_ref q 
    (P1idCont arg_7) ->
      apply $ k_ref q
    (P3plus) ->
      apply $ k_ref q
    (P2plus pat_af_1) ->
      apply $ k_ref q
    (P1plus pat_af' pat_af) ->
      apply $ k_ref q
    (P3plusCont_1) ->
      apply $ k_ref q
    (P2plusCont_1 pat_af_2) ->
      apply $ k_ref q 
    (P1plusCont_1 pat_af_3 i_1) ->
      apply $ k_ref q
    (P2plusCont_2) ->
      apply $ k_ref q
    (P1plusCont_2 pat_af_4) ->
      apply $ k_ref q

ap f a =
  cont_6 <- store (P1evalC a)
  eval $ f cont_6

apCont k_3 f_1 a_1 =
  cont_7 <- store (P1evalC2 a_1 k_3)
  eval $ f_1 cont_7

evalC a_2 x_2 =
    apply x_2 a_2

evalC2 a_3 k_4 x_3 =
    applyC x_3 a_3 k_4