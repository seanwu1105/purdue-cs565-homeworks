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

Require hw4.

Goal True.
  start "hw4".
  nl.

  exc "DenotationalSemantics.if_false".
  pt 2.
  check_type @hw4.DenotationalSemantics.if_false ((forall (b : Imp.bexp) (c1 c2 : Imp.com),
       Denotational.bexp_eqv b Imp.BFalse -> Denotational.com_eqv (Imp.CIf b c1 c2) c2)).
  ass.
  Print Assumptions hw4.DenotationalSemantics.if_false.
  nl.

  exc "DenotationalSemantics.swap_if_branches".
  pt 2.
  check_type @hw4.DenotationalSemantics.swap_if_branches ((forall (b : Imp.bexp) (c1 c2 : Imp.com),
       Denotational.com_eqv (Imp.CIf b c1 c2) (Imp.CIf (Imp.BNot b) c2 c1))).
  ass.
  Print Assumptions hw4.DenotationalSemantics.swap_if_branches.
  nl.

  exc "DenotationalSemantics.seq_assoc".
  pt 2.
  check_type @hw4.DenotationalSemantics.seq_assoc ((forall c1 c2 c3 : Imp.com,
       Denotational.com_eqv (Imp.CSeq (Imp.CSeq c1 c2) c3) (Imp.CSeq c1 (Imp.CSeq c2 c3)))).
  ass.
  Print Assumptions hw4.DenotationalSemantics.seq_assoc.
  nl.

  exc "DenotationalSemantics.b_opt_sound".
  pt 2.
  check_type @hw4.DenotationalSemantics.b_opt_sound ((forall a_opt : Imp.aexp -> Imp.aexp,
       (forall a : Imp.aexp, Denotational.aexp_eqv a (a_opt a)) ->
       forall b : Imp.bexp, Denotational.bexp_eqv b (hw4.DenotationalSemantics.b_opt a_opt b))).
  ass.
  Print Assumptions hw4.DenotationalSemantics.b_opt_sound.
  nl.

  exc "hoare_asgn_example".
  pt 1.
  check_type @hw4.hoare_asgn_example ((Hoare.hoare_triple (Hoare.assert_of_Prop True)
         (Imp.CSeq (Imp.CAsgn Imp.X (Imp.ANum 1)) (Imp.CAsgn Imp.Y (Imp.ANum 2)))
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.X) st = Hoare.Aexp_of_nat 1 st /\
          Hoare.Aexp_of_aexp (Imp.AId Imp.Y) st = Hoare.Aexp_of_nat 2 st))).
  ass.
  Print Assumptions hw4.hoare_asgn_example.
  nl.

  exc "swap_program".
  pt 1.
  check_type @hw4.swap_program ((Imp.com)).

  exc "swap_exercise".
  pt 2.
  check_type @hw4.swap_exercise ((Hoare.hoare_triple
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.X) st <= Hoare.Aexp_of_aexp (Imp.AId Imp.Y) st)
         hw4.swap_program
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.Y) st <= Hoare.Aexp_of_aexp (Imp.AId Imp.X) st))).
  ass.
  Print Assumptions hw4.swap_exercise.
  nl.

  exc "parity_correct".
  pt 3.
  check_type @hw4.parity_correct ((forall m : nat,
       Hoare.hoare_triple
         (fun st : Imp.state => Hoare.Aexp_of_aexp (Imp.AId Imp.X) st = Hoare.Aexp_of_nat m st)
         (Imp.CWhile (Imp.BLe (Imp.ANum 2) (Imp.AId Imp.X))
            (Imp.CAsgn Imp.X (Imp.AMinus (Imp.AId Imp.X) (Imp.ANum 2))))
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.X) st = Hoare.Aexp_of_nat (hw4.parity m) st))).
  ass.
  Print Assumptions hw4.parity_correct.
  nl.

  exc "factorial_correct".
  pt 5.
  check_type @hw4.factorial_correct ((forall m : nat,
       Hoare.hoare_triple
         (fun st : Imp.state => Hoare.Aexp_of_aexp (Imp.AId Imp.X) st = Hoare.Aexp_of_nat m st)
         (Imp.CSeq (Imp.CAsgn Imp.Y (Imp.ANum 1))
            (Imp.CWhile (Imp.BNot (Imp.BEq (Imp.AId Imp.X) (Imp.ANum 0)))
               (Imp.CSeq (Imp.CAsgn Imp.Y (Imp.AMult (Imp.AId Imp.Y) (Imp.AId Imp.X)))
                  (Imp.CAsgn Imp.X (Imp.AMinus (Imp.AId Imp.X) (Imp.ANum 1))))))
         (fun st : Imp.state => st Imp.Y = hw4.real_fact m))).
  ass.
  Print Assumptions hw4.factorial_correct.
  nl.

Abort.
