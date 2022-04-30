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

Require Final.

Goal True.
  start "Final".
  nl.

  exc "DenotationalSemantics.NotAppearsIn".
  pt 5.
  check_type @Final.DenotationalSemantics.NotAppearsIn ((string -> Imp.aexp -> Prop)).
  nl.

  exc "DenotationalSemantics.Not_AppearsIn_impl_NotAppearsIn".
  pt 5.
  check_type @Final.DenotationalSemantics.Not_AppearsIn_impl_NotAppearsIn ((forall (x : string) (a : Imp.aexp),
       ~ Final.DenotationalSemantics.AppearsIn x a -> Final.DenotationalSemantics.NotAppearsIn x a)).
  ass.
  Print Assumptions Final.DenotationalSemantics.Not_AppearsIn_impl_NotAppearsIn.
  nl.

  exc "DenotationalSemantics.if_shift".
  pt 5.
  check_type @Final.DenotationalSemantics.if_shift ((forall (b : Imp.bexp) (c1 c2 c3 : Imp.com),
       Denotational.com_eqv (Imp.CSeq (Imp.CIf b c1 c2) c3)
         (Imp.CIf b (Imp.CSeq c1 c3) (Imp.CSeq c2 c3)))).
  ass.
  Print Assumptions Final.DenotationalSemantics.if_shift.
  nl.

  exc "DenotationalSemantics.three_seq_equiv".
  pt 10.
  check_type @Final.DenotationalSemantics.three_seq_equiv ((forall c1 c2 c3 c1' c2' c3' : Imp.com,
       Denotational.com_eqv (Imp.CSeq c1 c2) (Imp.CSeq c1' c2') ->
       Denotational.com_eqv (Imp.CSeq c2 c3) (Imp.CSeq c2 c3') ->
       Denotational.com_eqv (Imp.CSeq c1 (Imp.CSeq c2 c3)) (Imp.CSeq c1' (Imp.CSeq c2' c3')))).
  ass.
  Print Assumptions Final.DenotationalSemantics.three_seq_equiv.
  nl.

  exc "DenotationalSemantics.subst_eqv".
  pt 5.
  check_type @Final.DenotationalSemantics.subst_eqv ((forall (x y : string) (a1 a2 : Imp.aexp),
       Final.DenotationalSemantics.NotAppearsIn x a1 ->
       Denotational.com_eqv (Imp.CSeq (Imp.CAsgn x a1) (Imp.CAsgn y a2))
         (Imp.CSeq (Imp.CAsgn x a1) (Imp.CAsgn y (Final.DenotationalSemantics.subst_var x a1 a2))))).
  ass.
  Print Assumptions Final.DenotationalSemantics.subst_eqv.
  nl.

  exc "DenotationalSemantics.three_subst_eqv".
  pt 5.
  check_type @Final.DenotationalSemantics.three_subst_eqv ((forall (x y z : string) (a1 a2 a3 : Imp.aexp),
       Final.DenotationalSemantics.NotAppearsIn x a1 ->
       Final.DenotationalSemantics.NotAppearsIn y a2 ->
       Denotational.com_eqv (Imp.CSeq (Imp.CAsgn x a1) (Imp.CSeq (Imp.CAsgn y a2) (Imp.CAsgn z a3)))
         (Imp.CSeq (Imp.CAsgn x a1)
            (Imp.CSeq (Imp.CAsgn y (Final.DenotationalSemantics.subst_var x a1 a2))
               (Imp.CAsgn z (Final.DenotationalSemantics.subst_var y a2 a3)))))).
  ass.
  Print Assumptions Final.DenotationalSemantics.three_subst_eqv.
  nl.

  exc "AxiomaticSemantics.Hoare_Q1".
  pt 5.
  check_type @Final.AxiomaticSemantics.Hoare_Q1 ((forall m : nat,
       Hoare.hoare_triple
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.X) st <= Hoare.Aexp_of_aexp (Imp.AId Imp.Y) st)
         (Imp.CSeq (Imp.CAsgn Imp.Z (Imp.AMult (Imp.AId Imp.X) (Imp.ANum m)))
            (Imp.CAsgn Imp.W (Imp.AMult (Imp.AId Imp.Y) (Imp.ANum m))))
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.Z) st <= Hoare.Aexp_of_aexp (Imp.AId Imp.W) st))).
  ass.
  Print Assumptions Final.AxiomaticSemantics.Hoare_Q1.
  nl.

  exc "AxiomaticSemantics.Hoare_Q2".
  pt 5.
  check_type @Final.AxiomaticSemantics.Hoare_Q2 ((Hoare.hoare_triple (Hoare.assert_of_Prop True)
         (Imp.CSeq
            (Imp.CIf (Imp.BLe (Imp.AId Imp.Y) (Imp.ANum 10))
               (Imp.CAsgn Imp.Y (Imp.APlus (Imp.AId Imp.Y) (Imp.ANum 1))) (Imp.CAsgn Imp.Y (Imp.ANum 10)))
            (Imp.CAsgn Imp.X (Imp.AId Imp.Y)))
         (fun st : Imp.state => Hoare.Aexp_of_aexp (Imp.AId Imp.X) st <= Hoare.Aexp_of_nat 11 st))).
  ass.
  Print Assumptions Final.AxiomaticSemantics.Hoare_Q2.
  nl.

  exc "AxiomaticSemantics.Hoare_Q3".
  pt 10.
  check_type @Final.AxiomaticSemantics.Hoare_Q3 ((forall m n : nat,
       Hoare.hoare_triple
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.X) st = Hoare.Aexp_of_nat 0 st /\
          Hoare.Aexp_of_aexp (Imp.AId Imp.Y) st = Hoare.Aexp_of_nat 0 st)
         (Imp.CWhile (Imp.BNot (Imp.BEq (Imp.AId Imp.Y) (Imp.ANum n)))
            (Imp.CSeq (Imp.CAsgn Imp.X (Imp.APlus (Imp.AId Imp.X) (Imp.ANum m)))
               (Imp.CAsgn Imp.Y (Imp.APlus (Imp.AId Imp.Y) (Imp.ANum 1)))))
         (fun st : Imp.state =>
          Hoare.Aexp_of_aexp (Imp.AId Imp.X) st = Hoare.Aexp_of_nat m st * Hoare.Aexp_of_nat n st))).
  ass.
  Print Assumptions Final.AxiomaticSemantics.Hoare_Q3.
  nl.

  exc "TypeErasure.erase".
  pt 5.
  check_type @Final.TypeErasure.erase ((Stlc.STLC.tm -> UntypedLC.Utm)).
  nl.

  exc "TypeErasure.erase_value".
  pt 2.
  check_type @Final.TypeErasure.erase_value ((forall v : Stlc.STLC.tm, Stlc.STLC.value v -> UntypedLC.Uvalue (Final.TypeErasure.erase v))).
  ass.
  Print Assumptions Final.TypeErasure.erase_value.
  nl.

  exc "TypeErasure.erase_subst".
  pt 3.
  check_type @Final.TypeErasure.erase_subst ((forall (x : string) (v t : Stlc.STLC.tm),
       UntypedLC.Usubst x (Final.TypeErasure.erase v) (Final.TypeErasure.erase t) =
       Final.TypeErasure.erase (Stlc.STLC.subst x v t))).
  ass.
  Print Assumptions Final.TypeErasure.erase_subst.
  nl.

  exc "TypeErasure.erase_preserves_semantics".
  pt 15.
  ass.
  Print Assumptions Final.TypeErasure.erase_preserves_semantics.
  nl.

  exc "STLC_Extensions.subst".
  pt 5.
  check_type @Final.STLC_Extensions.subst ((string -> Final.STLC_Extensions.tm -> Final.STLC_Extensions.tm -> Final.STLC_Extensions.tm)).
  nl.

  exc "STLC_Extensions.value".
  pt 2.
  check_type @Final.STLC_Extensions.value ((Final.STLC_Extensions.tm -> Prop)).
  nl.

  exc "STLC_Extensions.step".
  pt 3.
  check_type @Final.STLC_Extensions.step ((Final.STLC_Extensions.tm -> Final.STLC_Extensions.tm -> Prop)).
  nl.

  exc "STLC_Extensions.has_type".
  pt 2.
  check_type @Final.STLC_Extensions.has_type ((Final.STLC_Extensions.context -> Final.STLC_Extensions.tm -> Final.STLC_Extensions.ty -> Prop)).
  nl.

  exc "STLC_Extensions.canonical_forms_option".
  pt 3.
  check_type @Final.STLC_Extensions.canonical_forms_option ((forall (t : Final.STLC_Extensions.tm) (T : Final.STLC_Extensions.ty),
       Final.STLC_Extensions.has_type Maps.empty t (Final.STLC_Extensions.Ty_Option T) ->
       Final.STLC_Extensions.value t ->
       t = Final.STLC_Extensions.tm_none T \/
       (exists v : Final.STLC_Extensions.tm,
          Final.STLC_Extensions.value v /\ t = Final.STLC_Extensions.tm_some v))).
  ass.
  Print Assumptions Final.STLC_Extensions.canonical_forms_option.
  nl.

  exc "STLC_Extensions.progress".
  pt 10.
  check_type @Final.STLC_Extensions.progress ((forall (t : Final.STLC_Extensions.tm) (T : Final.STLC_Extensions.ty),
       Final.STLC_Extensions.has_type Maps.empty t T ->
       Final.STLC_Extensions.value t \/
       (exists t' : Final.STLC_Extensions.tm, Final.STLC_Extensions.step t t'))).
  ass.
  Print Assumptions Final.STLC_Extensions.progress.
  nl.

  exc "STLC_Extensions.substitution_preserves_typing".
  pt 10.
  check_type @Final.STLC_Extensions.substitution_preserves_typing ((forall (Gamma : Maps.partial_map Final.STLC_Extensions.ty) (x : string)
         (U : Final.STLC_Extensions.ty) (t v : Final.STLC_Extensions.tm) (T : Final.STLC_Extensions.ty),
       Final.STLC_Extensions.has_type (Maps.update Gamma x U) t T ->
       Final.STLC_Extensions.has_type Maps.empty v U ->
       Final.STLC_Extensions.has_type Gamma (Final.STLC_Extensions.subst x v t) T)).
  ass.
  Print Assumptions Final.STLC_Extensions.substitution_preserves_typing.
  nl.

  exc "STLC_Extensions.preservation".
  pt 5.
  check_type @Final.STLC_Extensions.preservation ((forall (t t' : Final.STLC_Extensions.tm) (T : Final.STLC_Extensions.ty),
       Final.STLC_Extensions.has_type Maps.empty t T ->
       Final.STLC_Extensions.step t t' -> Final.STLC_Extensions.has_type Maps.empty t' T)).
  ass.
  Print Assumptions Final.STLC_Extensions.preservation.
  nl.

  exc "STLC_Extensions.soundness".
  pt 5.
  check_type @Final.STLC_Extensions.soundness ((forall (t t' : Final.STLC_Extensions.tm) (T : Final.STLC_Extensions.ty),
       Final.STLC_Extensions.has_type Maps.empty t T ->
       Smallstep.multi Final.STLC_Extensions.step t t' -> ~ Final.STLC_Extensions.stuck t')).
  ass.
  Print Assumptions Final.STLC_Extensions.soundness.
  nl.

Abort.
