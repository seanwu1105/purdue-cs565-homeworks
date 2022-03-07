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

Require Midterm.

Goal True.
  start "Midterm".
  nl.

  exc "rangeSearch".
  pt 2.
  check_type @Midterm.rangeSearch ((Midterm.NatTree -> nat -> nat -> list nat)).
  nl.

  exc "#rangeSearch_tests".
  pt 1.
  check_type @Midterm.rangeSearch_test_1 ((Permutation.Permutation (Midterm.rangeSearch Midterm.tree_1 4 8) (6 :: 6 :: nil))).
  check_type @Midterm.rangeSearch_test_2 ((Permutation.Permutation (Midterm.rangeSearch Midterm.tree_1 14 18) nil)).
  check_type @Midterm.rangeSearch_test_3 ((Permutation.Permutation (Midterm.rangeSearch Midterm.tree_1 2 10) (2 :: 6 :: 10 :: 6 :: nil))).
  check_type @Midterm.rangeSearch_test_4 ((Permutation.Permutation (Midterm.rangeSearch Midterm.tree_1 10 2) nil)).
  ass.
  Print Assumptions Midterm.rangeSearch_test_1.
  Print Assumptions Midterm.rangeSearch_test_2.
  Print Assumptions Midterm.rangeSearch_test_3.
  Print Assumptions Midterm.rangeSearch_test_4.
  nl.

  exc "P_And_Not_P".
  pt 2.
  check_type @Midterm.P_And_Not_P ((forall P : Prop, ~ (P /\ ~ P))).
  ass.
  Print Assumptions Midterm.P_And_Not_P.
  nl.

  exc "And_Distribute_Or".
  pt 2.
  check_type @Midterm.And_Distribute_Or ((forall P Q R : Prop, P /\ (Q \/ R) <-> P /\ Q \/ P /\ R)).
  ass.
  Print Assumptions Midterm.And_Distribute_Or.
  nl.

  exc "Subsequence".
  pt 4.
  check_type @Midterm.Subsequence ((forall X : Type, list X -> list X -> Prop)).
  nl.

  exc "#Subsequence_tests".
  pt 1.
  check_type @Midterm.Subsequence_test_1 ((Midterm.Subsequence ("e" :: "x" :: "m" :: nil) ("e" :: "x" :: "a" :: "m" :: nil))).
  check_type @Midterm.Subsequence_test_2 ((Midterm.Subsequence (2 :: 6 :: nil) (1 :: 2 :: 15 :: 6 :: 15 :: 34 :: nil))).
  check_type @Midterm.Subsequence_test_3 ((Midterm.Subsequence nil ("e" :: "x" :: "a" :: "m" :: nil))).
  check_type @Midterm.Subsequence_test_4 ((Midterm.Subsequence ("e" :: "x" :: "a" :: nil) ("e" :: "x" :: "a" :: "m" :: nil))).
  check_type @Midterm.Subsequence_test_5 ((Midterm.Subsequence ("e" :: "x" :: "a" :: "m" :: nil) ("e" :: "x" :: "a" :: "m" :: nil))).
  ass.
  Print Assumptions Midterm.Subsequence_test_1.
  Print Assumptions Midterm.Subsequence_test_2.
  Print Assumptions Midterm.Subsequence_test_3.
  Print Assumptions Midterm.Subsequence_test_4.
  Print Assumptions Midterm.Subsequence_test_5.
  nl.

  exc "Subsequence_refl".
  pt 2.
  check_type @Midterm.Subsequence_refl ((forall (X : Type) (l : list X), Midterm.Subsequence l l)).
  ass.
  Print Assumptions Midterm.Subsequence_refl.
  nl.

  exc "Subsequence_not_sym".
  pt 2.
  check_type @Midterm.Subsequence_not_sym ((exists l1 l2 : list nat, Midterm.Subsequence l1 l2 /\ ~ Midterm.Subsequence l2 l1)).
  ass.
  Print Assumptions Midterm.Subsequence_not_sym.
  nl.

  exc "Subsequence_trans".
  pt 4.
  check_type @Midterm.Subsequence_trans ((forall (X : Type) (l1 l2 l3 : list X),
       Midterm.Subsequence l1 l2 -> Midterm.Subsequence l2 l3 -> Midterm.Subsequence l1 l3)).
  ass.
  Print Assumptions Midterm.Subsequence_trans.
  nl.

  exc "b_opt".
  pt 3.
  check_type @Midterm.b_opt (((Imp.aexp -> Imp.aexp) -> Imp.bexp -> Imp.bexp)).
  nl.

  exc "b_opt_sound".
  pt 4.
  check_type @Midterm.b_opt_sound ((forall a_opt : Imp.aexp -> Imp.aexp,
       (forall (a : Imp.aexp) (st : Imp.state), Imp.aeval st (a_opt a) = Imp.aeval st a) ->
       forall (b : Imp.bexp) (st : Imp.state), Imp.beval st (Midterm.b_opt a_opt b) = Imp.beval st b)).
  ass.
  Print Assumptions Midterm.b_opt_sound.
  nl.

  exc "insert".
  pt 2.
  check_type @Midterm.insert ((forall X : Type, (X -> X -> bool) -> X -> list X -> list X)).
  nl.

  exc "insert_sort".
  pt 2.
  check_type @Midterm.insert_sort ((forall X : Type, (X -> X -> bool) -> list X -> list X)).
  nl.

  exc "#insert_sort_tests".
  pt 1.
  check_type @Midterm.insert_sort_test_1 ((Midterm.insert_sort PeanoNat.Nat.leb (1 :: 4 :: 6 :: 8 :: nil) = (1 :: 4 :: 6 :: 8 :: nil)%list)).
  check_type @Midterm.insert_sort_test_2 ((Midterm.insert_sort PeanoNat.Nat.leb (1 :: 8 :: 6 :: 4 :: nil) = (1 :: 4 :: 6 :: 8 :: nil)%list)).
  check_type @Midterm.insert_sort_test_3 ((Midterm.insert_sort PeanoNat.Nat.leb (8 :: 8 :: 3 :: 4 :: nil) = (3 :: 4 :: 8 :: 8 :: nil)%list)).
  ass.
  Print Assumptions Midterm.insert_sort_test_1.
  Print Assumptions Midterm.insert_sort_test_2.
  Print Assumptions Midterm.insert_sort_test_3.
  nl.

  exc "insert_correct".
  pt 5.
  check_type @Midterm.insert_correct ((forall (X : Type) (le : X -> X -> Prop) (leb : X -> X -> bool),
       (forall x x' : X, leb x x' = true <-> le x x') ->
       (forall x x' : X, leb x x' = false -> leb x' x = true) ->
       forall (x : X) (l : list X),
       Midterm.SortedList le l -> Midterm.SortedList le (Midterm.insert leb x l))).
  ass.
  Print Assumptions Midterm.insert_correct.
  nl.

  exc "insert_sort_correct".
  pt 2.
  check_type @Midterm.insert_sort_correct ((forall (X : Type) (le : X -> X -> Prop) (leb : X -> X -> bool),
       (forall x x' : X, leb x x' = true <-> le x x') ->
       (forall x x' : X, leb x x' = false -> leb x' x = true) ->
       forall l : list X, Midterm.SortedList le (Midterm.insert_sort leb l))).
  ass.
  Print Assumptions Midterm.insert_sort_correct.
  nl.

  exc "IMPRepeat.cReval".
  pt 4.
  check_type @Midterm.IMPRepeat.cReval ((Midterm.IMPRepeat.comR -> Imp.state -> Imp.state -> Prop)).
  nl.

  exc "IMPRepeat.no_repeat_test".
  pt 1.
  check_type @Midterm.IMPRepeat.no_repeat_test ((forall st : Imp.state,
       exists st' : Imp.state,
         Midterm.IMPRepeat.cReval Midterm.IMPRepeat.no_repeat_example st st' /\ st' Imp.X = 1)).
  ass.
  Print Assumptions Midterm.IMPRepeat.no_repeat_test.
  nl.

  exc "IMPRepeat.div_by_two_test".
  pt 1.
  check_type @Midterm.IMPRepeat.div_by_two_test ((forall st : Maps.total_map nat,
       exists st' : Imp.state,
         Midterm.IMPRepeat.cReval Midterm.IMPRepeat.div_by_two_example
           (Maps.t_update (Maps.t_update st Imp.X 0) Imp.Y 8) st' /\ st' Imp.Y = 0 /\ st' Imp.X = 4)).
  ass.
  Print Assumptions Midterm.IMPRepeat.div_by_two_test.
  nl.

  exc "IMPRepeat.comRTocom".
  pt 4.
  check_type @Midterm.IMPRepeat.comRTocom ((Midterm.IMPRepeat.comR -> Imp.com)).
  nl.

  exc "IMPRepeat.comRToCom_correct".
  pt 6.
  check_type @Midterm.IMPRepeat.comRToCom_correct ((forall (c : Midterm.IMPRepeat.comR) (st st' : Imp.state),
       Midterm.IMPRepeat.cReval c st st' -> Imp.ceval (Midterm.IMPRepeat.comRTocom c) st st')).
  ass.
  Print Assumptions Midterm.IMPRepeat.comRToCom_correct.
  nl.

  exc "LCPairsBool.tm".
  pt 2.
  check_type @Midterm.LCPairsBool.tm ((Set)).
  nl.

  exc "LCPairsBool.not2B".
  pt 1.
  check_type @Midterm.LCPairsBool.not2B ((Midterm.LCPairsBool.tm)).
  nl.

  exc "LCPairsBool.and2B".
  pt 1.
  check_type @Midterm.LCPairsBool.and2B ((Midterm.LCPairsBool.tm)).
  nl.

  exc "LCPairsBool.or2B".
  pt 1.
  check_type @Midterm.LCPairsBool.or2B ((Midterm.LCPairsBool.tm)).
  nl.

  exc "LCPairsBool.subst".
  pt 6.
  check_type @Midterm.LCPairsBool.subst ((string -> Midterm.LCPairsBool.tm -> Midterm.LCPairsBool.tm -> Midterm.LCPairsBool.tm)).
  nl.

  exc "LCPairsBool.step".
  pt 10.
  check_type @Midterm.LCPairsBool.step ((Midterm.LCPairsBool.tm -> Midterm.LCPairsBool.tm -> Prop)).
  nl.

  exc "#LCPairsBool.step_test_notB".
  pt 1.
  check_type @Midterm.LCPairsBool.notB_ex ((Smallstep.multi Midterm.LCPairsBool.step
         (Midterm.LCPairsBool.tm_app Midterm.LCPairsBool.notB Midterm.LCPairsBool.tm_true)
         Midterm.LCPairsBool.tm_false)).
  ass.
  Print Assumptions Midterm.LCPairsBool.notB_ex.
  nl.

  exc "#LCPairsBool.step_test_not2B".
  pt 1.
  ass.
  Print Assumptions Midterm.LCPairsBool.not2B_ex_1.
  Print Assumptions Midterm.LCPairsBool.not2B_ex_2.
  nl.

  exc "#LCPairsBool.step_test_and2b".
  pt 1.
  ass.
  Print Assumptions Midterm.LCPairsBool.and2b_ex_1.
  Print Assumptions Midterm.LCPairsBool.and2b_ex_2.
  Print Assumptions Midterm.LCPairsBool.not2b_ex_3.
  nl.

  exc "#LCPairsBool.step_test_or2b".
  pt 1.
  ass.
  Print Assumptions Midterm.LCPairsBool.or2b_ex_1.
  Print Assumptions Midterm.LCPairsBool.or2b_ex_2.
  Print Assumptions Midterm.LCPairsBool.or2b_ex_3.
  nl.

Abort.
