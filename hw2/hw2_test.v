(** Do not submit this file. *)

Set Warnings "-notation-overridden,-parsing".
Require Import hw2.

Parameter MISSING: Type.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => gfail 1 "Type missing:" A
    | ?T => first [unify T B | gfail 1 "Type wrong - should be (" B ")"]
    end.

Tactic Notation "exc" string(x) := idtac "*>" x.
Tactic Notation "itm" string(x) := idtac "#>" x.
Ltac ass := idtac "Assumptions:".
Ltac nl := idtac "".
Ltac pt x := idtac "Possible point:" x.

Goal True.
  exc "SearchTree".
  pt 1.
  nl.

  exc "EnumerateRecords".
  pt 1.
  nl.

  exc "FindKey".
  pt 1.
  nl.

  exc "AddElement".
  pt 1.
  nl.

  exc "sanity_check".
  pt 1.
  check_type @Find_21_OK ((FindStudent' 21 exampleDB' = FindStudent 21 exampleDB)).
  ass.
  Print Assumptions Find_21_OK.
  check_type @Find_22_OK ((FindStudent' 22 exampleDB' = FindStudent 22 exampleDB)).
  ass.
  Print Assumptions Find_22_OK.
  check_type @Find_23_OK ((FindStudent' 23 exampleDB' = FindStudent 23 exampleDB)).
  ass.
  Print Assumptions Find_23_OK.
  check_type @Find_24_OK ((FindStudent' 24 exampleDB' = FindStudent 24 exampleDB)).
  ass.
  Print Assumptions Find_24_OK.
  nl.

  exc "apply_Q".
  pt 1.
  check_type @apply_Q (((forall n, evenb n = true -> oddb (S n) = true) ->
                        evenb 4 = true ->
                        oddb 3 = true)).
  Print Assumptions apply_Q.
  nl.

  exc "injection_Q".
  pt 1.
  check_type @injection_Q ((forall (X : Type) (x y z w : X) (l j : list X),
                               x :: y :: l = w :: z :: j ->
                               x :: l = z :: [ ] ->
                               x = y)).
  Print Assumptions injection_Q.
  nl.

  exc "discriminate_Q".
  pt 1.
  check_type @discriminate_Q ((forall (X : Type) (x y z : X) (l j : list X),
                                  x :: y :: l = [] ->
                                  x = z)).
  Print Assumptions discriminate_Q.
  nl.

Abort.

Module NatGymnasium_test.
  Import NatGymnasium.

Goal True.
  exc "plus_n_Sm".
  pt 1.
  check_type @plus_n_Sm ((forall n m : nat,
                             S (plus n m) = plus n (S m))).
  ass.
  Print Assumptions plus_n_Sm.
  nl.

  exc "plus_assoc".
  pt 1.
  check_type @plus_assoc ((forall n m p : nat,
                              plus n (plus m p) = plus (plus n m) p)).
  ass.
  Print Assumptions plus_assoc.
  nl.

  exc "plus_comm".
  pt 1.
  check_type @plus_comm ((forall n m : nat,
                             plus n m = plus m n)).
  ass.
  Print Assumptions plus_comm.
  nl.

  exc "double_plus".
  pt 1.
  check_type @double_plus ((forall n, double n = plus n n)).
  ass.
  Print Assumptions double_plus.
  nl.

Abort.

End NatGymnasium_test.

Module ListGynamsium_test.
  Import ListGynamsium.

Goal True.

  exc "app_length".
  pt 1.
  check_type @app_length ((forall A : Type, forall l1 l2 : list A,
                                length (app l1 l2) = (length l1) + (length l2))).
  ass.
  Print Assumptions app_length.
  nl.

Abort.

End ListGynamsium_test.

Goal True.

  exc "and_assoc".
  pt 1.
  check_type @and_assoc ((forall P Q R : Prop,
                             P /\ (Q /\ R) -> (P /\ Q) /\ R)).
  ass.
  Print Assumptions and_assoc.
  nl.

  exc "or_commut".
  pt 1.
  check_type @or_commut ((forall P Q : Prop,
                             P \/ Q  -> Q \/ P)).
  ass.
  Print Assumptions or_commut.
  nl.

  exc "contrapositive".
  pt 1.
  check_type @contrapositive ((forall (P Q : Prop),
                                  (P -> Q) -> (~Q -> ~P))).
  ass.
  Print Assumptions contrapositive.
  nl.

  exc "ev_double".
  pt 1.
  check_type @ev_double ((forall n,
                             ev (n + n))).
  ass.
  Print Assumptions ev_double.
  nl.

  exc "ev_sum".
  pt 1.
  check_type @ev_sum ((forall n m, ev n -> ev m -> ev (n + m))).
  ass.
  Print Assumptions ev_sum.
  nl.

  exc "WF_studentsTree".
  pt 3.
  nl.

  exc "exampleDBOK".
  pt 1.
  check_type @exampleDBOK ((WF_StudentsTree exampleDB)).
  ass.
  Print Assumptions exampleDBOK.
  nl.

Abort.
