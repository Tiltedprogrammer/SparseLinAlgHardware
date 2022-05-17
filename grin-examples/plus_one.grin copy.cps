grinMain =
  m <- main $
  result <- fetch m
  pure result

main =
  i <- do
    store (CZero)
  
  var_e <- store (P2plusOne)
  
  var_n <- store (Fap var_e i)
  
  main_cont <- store (P1idCont)
    
  ap $ var_n main_cont 


plusOneCont y k_2 = 
  res_1 <- store (CSucc y)
  apply $ k_2 res_1


plusOne x k_1 =
  scrut_x' <- do
    pure x
  cont <- store (P2plusOneCont)  
  cont' <- store (P1apCont k_1 cont)
  eval $ scrut_x' cont'


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
    (P2plusOne) ->
      res_5 <- store (P1plusOne a'')  
      pure res_5
    (P1plusOne pat_af) ->
      plusOne $ pat_af a''
    (P2plusOneCont) ->
      res_6 <- store (P1plusOneCont a'') 
      pure res_6
    (P1plusOneCont i_1) ->
      plusOneCont $ i_1 a''
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

--k,f here are also values

applyC f'' a'' k_deref =
    
  f_1' <- fetch f''

  case f_1' of
    (P2ap) ->
      arg <- store (P1ap a'')
      apply $ k_deref arg
    (P1ap pat_ac_1) ->
      apCont $ pat_ac_1 a'' k_deref
    (P2plusOne) ->
      plusOne $ a'' k_deref
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
    (P2plusOneCont) ->
      plusOneCont $ a'' k_deref
    (P1plusOneCont arg_6') ->
      cont_2 <- store (P1apCont k_deref a'')
      plusOneCont $ arg_6' cont_2
    (P1idCont) ->
      apply $ k_deref a''



idCont p = pure p

eval q k_ref =
  v <- fetch q
  k <- fetch k_ref
  case v of
    (Fap pat_t pat) -> 
      apCont $ k_ref pat_t pat
--    (Fapply pat_zz pat_zzz) ->
--      applyC pat_zz pat_zzz k_ref
--    (FapCont k1 f1 a1) ->
--      cont_3 <- store (P1apCont k_ref k1)
--     apCont $ cont_3 f1 a1
--    (FevalC a1_2 x1) ->
--      evalC $ a1_2 x1
--    (FevalC2 a1_3 k1_2 x1_2) ->
--      cont_4 <- store (P1apCont k_ref k1_2)
--      evalC2 $ a1_3 cont_4 x1_2
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
    (FplusOne pat_x pat_w) ->
      cont_5 <- store (P1apCont k_ref pat_w)
      plusOne $ pat_x cont_5
    (P2plusOne) ->
      apply $ k_ref q 
    (P1plusOne pat_aa) ->
      apply $ k_ref q
    (P2plusOneCont) ->
      apply $ k_ref q
    (P1plusOneCont) ->
      apply $ k_ref q
    (CSucc c_bind_m_r_s) ->
      apply $ k_ref q 
    (CZero) ->
      apply $ k_ref q 
    (P1idCont arg_7) ->
      apply $ k_ref q 

ap f a =
  cont_6 <- store (P1evalC a)
  eval $ f cont_6

apCont k_3 f_1 a_1 =
  cont_7 <- store (P1evalC2 a_1 k_3)
  eval $ f_1 cont_7

-- x is a value here, not a pointer, mb fetch is needed

evalC a_2 x_2 =
    apply x_2 a_2

evalC2 a_3 k_4 x_3 =
    applyC x_3 a_3 k_4