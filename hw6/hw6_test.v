Require Export String.
Open Scope string.

Ltac start m := idtac "----" m.
Ltac nl := idtac "".
Ltac exc x := idtac "Exercise:" x.
Ltac itm x := idtac "Sub-exercise:" x.
Ltac pt x := idtac "Possible points:" x.
Ltac ass := idtac "Assumptions:".

Parameter MISSING: Type.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => gfail 1 "Type missing for" A
    | ?T => unify T B
    end.

Require hw6.

Goal True.
  start "hw6".
  nl.

  exc "LCPairsBool.has_type".
  pt 2.
  check_type @hw6.LCPairsBool.has_type ((hw6.LCPairsBool.context -> StlcBoolProd.tm -> StlcBoolProd.ty -> Prop)).
  nl.

  exc "LCPairsBool.progress".
  pt 3.
  check_type @hw6.LCPairsBool.progress ((forall (t : StlcBoolProd.tm) (T : StlcBoolProd.ty),
                                            hw6.LCPairsBool.has_type Maps.empty t T ->
                                            StlcBoolProd.value t \/ (exists t' : StlcBoolProd.tm, StlcBoolProd.step t t'))).
  ass.
  Print Assumptions hw6.LCPairsBool.progress.
  nl.

  exc "LCPairsBool.preservation".
  pt 2.
  check_type @hw6.LCPairsBool.preservation ((forall (t t' : StlcBoolProd.tm) (T : StlcBoolProd.ty),
                                                hw6.LCPairsBool.has_type Maps.empty t T ->
                                                StlcBoolProd.step t t' -> hw6.LCPairsBool.has_type Maps.empty t' T)).
  ass.
  Print Assumptions hw6.LCPairsBool.preservation.
  nl.

  exc "LCPairsBool.soundness".
  pt 1.
  check_type @hw6.LCPairsBool.soundness ((forall (t t' : StlcBoolProd.tm) (T : StlcBoolProd.ty),
                                             hw6.LCPairsBool.has_type Maps.empty t T ->
                                             Smallstep.multi StlcBoolProd.step t t' -> ~ hw6.LCPairsBool.stuck t')).
  ass.
  Print Assumptions hw6.LCPairsBool.soundness.
  nl.

  exc "LCPairsBool.has_type_w_constraints".
  pt 2.
  check_type @hw6.LCPairsBool.has_type_w_constraints ((hw6.LCPairsBool.context ->
       StlcBoolProd.tm ->
       StlcBoolProd.ty -> list hw6.LCPairsBool.constraint -> Prop)).
  nl.

  exc "#LCPairsBool.product_inference_examples".
  pt 1.
  check_type @hw6.LCPairsBool.product_inference_example_1 ((hw6.LCPairsBool.has_type_w_constraints Maps.empty
         (StlcBoolProd.tm_abs StlcBoolProd.x
            (StlcBoolProd.Ty_Var StlcBoolProd.X)
            (StlcBoolProd.tm_fst (StlcBoolProd.tm_var StlcBoolProd.x)))
         (StlcBoolProd.Ty_Arrow (StlcBoolProd.Ty_Var StlcBoolProd.X)
            (StlcBoolProd.Ty_Var StlcBoolProd.U))
         ((StlcBoolProd.Ty_Var StlcBoolProd.X,
          StlcBoolProd.Ty_Prod (StlcBoolProd.Ty_Var StlcBoolProd.U)
            (StlcBoolProd.Ty_Var StlcBoolProd.V)) :: nil))).
  check_type @hw6.LCPairsBool.product_inference_example_2 ((hw6.LCPairsBool.has_type_w_constraints Maps.empty
         (StlcBoolProd.tm_abs StlcBoolProd.x
            (StlcBoolProd.Ty_Var StlcBoolProd.X)
            (StlcBoolProd.tm_snd (StlcBoolProd.tm_var StlcBoolProd.x)))
         (StlcBoolProd.Ty_Arrow (StlcBoolProd.Ty_Var StlcBoolProd.X)
            (StlcBoolProd.Ty_Var StlcBoolProd.V))
         ((StlcBoolProd.Ty_Var StlcBoolProd.X,
          StlcBoolProd.Ty_Prod (StlcBoolProd.Ty_Var StlcBoolProd.U)
            (StlcBoolProd.Ty_Var StlcBoolProd.V)) :: nil))).
  check_type @hw6.LCPairsBool.product_inference_example_3 ((hw6.LCPairsBool.has_type_w_constraints Maps.empty
         (StlcBoolProd.tm_abs StlcBoolProd.x
            (StlcBoolProd.Ty_Var StlcBoolProd.X)
            (StlcBoolProd.tm_abs StlcBoolProd.y
               (StlcBoolProd.Ty_Prod (StlcBoolProd.Ty_Var StlcBoolProd.Y)
                  (StlcBoolProd.Ty_Var StlcBoolProd.Y))
               (StlcBoolProd.tm_ite (StlcBoolProd.tm_var StlcBoolProd.x)
                  (StlcBoolProd.tm_fst (StlcBoolProd.tm_var StlcBoolProd.y))
                  StlcBoolProd.tm_false)))
         (StlcBoolProd.Ty_Arrow (StlcBoolProd.Ty_Var StlcBoolProd.X)
            (StlcBoolProd.Ty_Arrow
               (StlcBoolProd.Ty_Prod (StlcBoolProd.Ty_Var StlcBoolProd.Y)
                  (StlcBoolProd.Ty_Var StlcBoolProd.Y))
               (StlcBoolProd.Ty_Var StlcBoolProd.Y)))
         ((StlcBoolProd.Ty_Var StlcBoolProd.X, StlcBoolProd.Ty_Bool)
          :: (StlcBoolProd.Ty_Var StlcBoolProd.Y, StlcBoolProd.Ty_Bool)
             :: (StlcBoolProd.Ty_Prod (StlcBoolProd.Ty_Var StlcBoolProd.Y)
                   (StlcBoolProd.Ty_Var StlcBoolProd.Y),
                StlcBoolProd.Ty_Prod (StlcBoolProd.Ty_Var StlcBoolProd.Y)
                  (StlcBoolProd.Ty_Var StlcBoolProd.Y)) :: nil))).
  ass.
  Print Assumptions hw6.LCPairsBool.product_inference_example_1.
  Print Assumptions hw6.LCPairsBool.product_inference_example_2.
  Print Assumptions hw6.LCPairsBool.product_inference_example_3.
  nl.

Abort.
