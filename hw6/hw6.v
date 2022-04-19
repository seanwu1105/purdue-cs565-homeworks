(****** Homework 6 for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 04/29/2022 by 6:00PM !!! **)
(* ================================================================= *)
(** ** Instructions for Homework 6 *)

(** Follow the following instructions for Homework 6.
      - Before working on this file, open '_CoqProject' file in the same
        directory and replace the line '-R ../plf PLF' with '-R
        /path/to/your/programming/language/foundations/directory PLF', similar
        to how you did it in previous homework.
      - Alternatively, you may symlink (or move / copy) the plf directory to the
        parent directory of the homework directory. For example, if your
        homework folder is at '/path/to/hw6', you may symlink plf to
        '/path/to/plf'. This way you don't have to change '_CoqProject'.
      - Compile your [Smallstep.v] first according to 'Software Foundations', or
        just run `make` in PLF to compile everything.
      - You are allowed to use axioms from [Maps.v]. Therefore, if you see
        axioms with prefix [Maps.] in the output of [hw4_test.v], it is fine.
      - You shouldn't need axioms from other chapters. If you really want to use
        an exercise from other chapters, please copy it to [hw6.v] and prove it.
      - If you define additional definitions or lemmas, make sure they are
        defined in [hw6.v]. Remember you only hand in [hw6.v].
 *)

(** ** Homework Submission Guidelines *)

(** In order for the grading scripts to work correctly (and
    give you that you get full credit for your work!), please be
    careful to follow these rules:
      - Do not alter the names, types and definitions of the exercises,
        unless instructed to do so.
      - If the instructions ask you to state a theorem of a given name,
        or replace part of a definition with a given one, make sure you
        use the exact same name or definition.
      - Do not delete exercises.  If you skip an exercise (e.g.,
        because it is marked "optional," or because you can't solve it),
        it is OK to leave a partial proof in your [.v] file; in
        this case, please make sure it ends with [Admitted] (not, for
        example [Abort]).
      - It is fine to use additional definitions (of helper functions,
        useful lemmas, etc.) in your solutions.  Put these between the
        exercise header and the theorem you are asked to prove.
      - Before submitting, make sure that running 'make' command produces
        no error. If for some compatibility reason 'make' always fails in
        your environment, inform the TA ASAP.
      - Only hand in [hw<n>.v]. Please do not submit auxiliary files,
        such as [Makefile] or [hw<n>_test.v].

    Each homework (like [hw6.v]) is accompanied by a _test script_
    ([hw6_test.v]). You may want to use them to double-check that your
    file is well-formed before handing it in by running the 'make'
    command.

    For full credit, make sure you check the following:
      - The "Assumptions" section for each exercise outputted by
        'make' (or the test script) contains only "Closed under the
        global context", but not "Axioms: ...". If some axioms are
        allowed as per instructions, make sure only those allowed
        axioms are printed out.
      - Before proving a theorem, make sure that the relevant
        definitions are correct first. If your definitions are wrong,
        you will not get full credit for the proof. For example, if
        the definition of [getFlag] is wrong, then every proof
        exercise involving [getFlag] (e.g., [evalAddFlagID]) will be
        impacted.
      - Be aware that even if 'make' prints no error or axioms, you
        may still lose points, because some exercises are manually
        graded.

    We are using Brightspace for submission. If you submit multiple
    versions of the assignment, you may notice that they are given
    different names.  This is fine: The most recent submission is the
    one that will be graded. *)

Set Warnings "-notation-overridden,-parsing,-require-in-module".
From Coq Require Export
     String
     List
     Nat (* For natural number comparision operators. *)
     Arith.PeanoNat. (* For some additional lemmas about natural numbers. *)
Import List.ListNotations.
Import PeanoNat.Nat.
From Coq Require Import Lia.

(***************************************************************************
  Part 1: Type Safety [8 points]
 ***************************************************************************)

From PLF Require Import Smallstep.
From PLF Require Import Maps.
From Top Require Import StlcBoolProd.
Module LCPairsBool.

  (* In this section, you will be adding a type system to the language
     of lambda calculus + Booleans + Pairs from the midterm, and
     proving that it is sound.

     The Coq formalization of the calculus' syntax and
     small-step-semantics can be found in [StlcBoolProd.v] *)

  (* In BNF Notation, the syntax for the types of this language is:
     T := T -> T | bool | T * T

     and the syntax for the language itself is:

       t ::=
       | x                    (variable)
       | \x : T,t                 (abstraction)
       | t t                  (application)
       | true                 (constant true)
       | false                (constant false)
       | if t then t else t   (conditional)

       | (t,t)                (pair [tm_pair])
       | t.fst                (first projection [tm_fst])
       | t.snd                (second projection [tm_snd])

       (The only difference from the untyped version is the typing
       annotation on lambda abstractions. *)

  (* Here are lambda expressions for logical negation and swapping the
   elements of a pair *)
  Definition notB : tm := <{\x : Bool, if x then false else true}>.
  Definition swap : tm := <{\x : Bool * Bool, <snd x, fst x> }>.

  (* And here are expressions that calculate the bitwise and, bitwise or,
   and bitwise negation of a pair of booleans (i.e. a 2-bit vector).  *)

  Definition andB : tm := <{\x : Bool, \y : Bool, if x then y else false}>.
  Definition and2B : tm := <{\x : Bool * Bool, \y : Bool * Bool, <andB (fst x) (fst y), andB (snd x) (snd y)>}>.

  Definition orB : tm := <{\x : Bool, \y : Bool, if x then true else y}>.
  Definition or2B : tm := <{\x : Bool * Bool, \y : Bool * Bool, <orB (fst x) (fst y), orB (snd x) (snd y)>}>.

  Definition not2B : tm := <{\x : Bool,  <notB (fst x), notB (snd x)>}>.

  Definition context := partial_map ty.

  Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

  (* Here are the typing rules for this calculus:

Gamma x = T1
------------------------------------------------ (T_Var)
Gamma ⊢ x ∈ T1

x ⊢> T2 ; Gamma ⊢ t1 ∈ T1
Gamma ⊢ \x:T2,t1 ∈ T2->T1
------------------------------------------------ (T_Abs)
Gamma ⊢ t1 ∈ T2->T1

Gamma ⊢ t2 ∈ T2
------------------------------------------------ (T_App)
Gamma ⊢ t1 t2 ∈ T1

------------------------------------------------ (T_True)
Gamma ⊢ true ∈ Bool

------------------------------------------------ (T_False)
Gamma ⊢ false ∈ Bool

Gamma ⊢ t1 ∈ Bool    Gamma ⊢ t2 ∈ T1    Gamma ⊢ t3 ∈ T1
-------------------------------------------------------- (T_If)
Gamma ⊢ if t1 then t2 else t3 ∈ T1


Gamma ⊢ t1 ∈ T1            Gamma ⊢ t2 ∈ T2
------------------------------------------------ (T_Pair)
Gamma ⊢ (t1,t2) ∈ T1*T2

Gamma ⊢ t0 ∈ T1*T2
------------------------------------------------ (T_Fst)
Gamma ⊢ fst t0 ∈ T1

Gamma ⊢ t0 ∈ T1*T2
------------------------------------------------ (T_Snd)
Gamma ⊢ snd t0 ∈ T2
   *)

  (** Exercise: 2 point (has_type) *)
  Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
    Gamma x = Some T1 ->
    Gamma |- x \in T1
  | T_Abs : forall Gamma x t1 T1 T2,
    (x |-> T2 ; Gamma) |- t1 \in T1 ->
    Gamma |- \x : T2, t1 \in (T2 -> T1)
  | T_App : forall Gamma t1 t2 T1 T2,
    Gamma |- t1 \in (T2 -> T1) ->
    Gamma |- t2 \in T2 ->
    Gamma |- t1 t2 \in T1
  | T_True : forall Gamma,
    Gamma |- true \in Bool
  | T_False : forall Gamma,
    Gamma |- false \in Bool
  | T_If : forall Gamma t1 t2 t3 T1,
    Gamma |- t1 \in Bool ->
    Gamma |- t2 \in T1 ->
    Gamma |- t3 \in T1 ->
    Gamma |- if t1 then t2 else t3 \in T1
  | T_Pair : forall Gamma t1 t2 T1 T2,
    Gamma |- t1 \in T1 ->
    Gamma |- t2 \in T2 ->
    Gamma |- <t1, t2> \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
    Gamma |- t0 \in (T1 * T2) ->
    Gamma |- fst t0 \in T1
  | T_Snd : forall Gamma t0 T1 T2,
    Gamma |- t0 \in (T1 * T2) ->
    Gamma |- snd t0 \in T2

  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

  #[local] Hint Constructors has_type : core.
  #[local] Hint Constructors value : core.

  (** Exercise: 3 point (progress) *)
  (*Complete the proof of [progress] for this calculus. *)
  Theorem progress : forall t T,
      empty |- t \in T ->
      value t \/ exists t', t --> t'.
  Proof.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst; eauto.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be
       [T_Var], since it can never be the case that
       [empty |- x \in T] (since the context is empty). *)
    discriminate H.
  - (* T_App *)
    (* If the last rule applied was T_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty |- t1 \in T1 -> T2]
         [empty |- t2 \in T1]
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    destruct IHHt1; subst; eauto.
    + (* t1 is a value *)
      destruct IHHt2; subst; eauto.
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = \x0 : T0, t11], since abstractions are the
           only values that can have an arrow type.  But
           [(\x0 : T0, t11) t2 --> [x:=t2]t11] by [ST_AppAbs]. *)
        destruct H; try solve_by_invert. eapply ex_intro. apply ST_AppAbs. eauto.
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'],
           then [t1 t2 --> t1 t2'] by [ST_App2]. *)
        destruct H0 as [t2' Hstp]; eauto.
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [ST_App1]. *)
      destruct H as [t1' Hstp]; eauto.
  - (* T_If *)
    destruct IHHt1; eauto.
    + destruct t1; try solve_by_invert; eauto.
    + destruct H. eauto.
  - (* T_Pair *)
    destruct IHHt1; eauto.
    + destruct IHHt2; eauto. destruct H0. eauto.
    + destruct H. eauto.
  - (* T_Fst *)
    destruct IHHt; eauto.
    + destruct H; try solve_by_invert. eauto.
    + destruct H. eauto.
  - (* T_Snd *)
    destruct IHHt; eauto.
    + destruct H; try solve_by_invert. eauto.
    + destruct H. eauto. 
  Qed.

  (* ###################################################################### *)
  (** *** Substitution *)

  Lemma weakening : forall Gamma Gamma' t T,
      inclusion Gamma Gamma' ->
      Gamma  |- t \in T  ->
      Gamma' |- t \in T.
  Proof.
    intros Gamma Gamma' t T H Ht.
    generalize dependent Gamma'.
    induction Ht; eauto 7 using inclusion_update.
  Qed.

  Lemma weakening_empty : forall Gamma t T,
      empty |- t \in T  ->
                     Gamma |- t \in T.
  Proof.
    intros Gamma t T.
    eapply weakening.
    discriminate.
  Qed.

  Lemma substitution_preserves_typing : forall Gamma x U t v T,
      (x |-> U ; Gamma) |- t \in T ->
                                 empty |- v \in U   ->
                                                Gamma |- [x:=v]t \in T.
  Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term [t].  Most cases follow
     directly from the IH, with the exception of [var]
     and [abs]. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty.
      rewrite eqb_refl; eauto.
    + (* x<>y *)
      generalize n; intro; apply eqb_neq in n; rewrite n.
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
  Qed.

  (* ###################################################################### *)
  (** *** Preservation *)

  (** Exercise: 2 points (preservation) *)
  (* Complete the proof of [preservation] for the calculus: *)
  Theorem preservation : forall t t' T,
      empty |- t \in T  ->
                     t --> t'  ->
                     empty |- t' \in T.
  Proof.
    intros t t' T HT. generalize dependent t'.
    remember empty as Gamma.
  (* Proof: By induction on the given typing derivation.
     Hint: Many cases are contradictory ([T_Var], [T_Abs]).
     The most interesting cases are [T_App], [T_Fst], and [T_Snd] *)
    induction HT; intros; subst; try solve [inversion H; subst; eauto];
    inversion H; subst; eauto.
    - apply substitution_preserves_typing with (U:=T2);
       inversion HT1; eauto.
    - inversion HT. eauto.
    - inversion HT. eauto.
  Qed.

  Definition stuck (t:tm) : Prop :=
    (normal_form step) t /\ ~ value t.

  (** Exercise: 1 point (soundness) *)
  (* Combine the proofs of [progress] and [preservation] to complete the
   proof of type soundness: *)
  Corollary soundness :
    forall t t' T,
      (empty |- t \in T) ->
      t -->* t' ->
      ~(stuck t').
  Proof.
    unfold stuck, normal_form, not.
    intros.
    destruct H1.
    induction H0.
    - apply progress in H. destruct H; eauto.
    - apply IHmulti; try eauto.
    -- eapply preservation; eauto.
  Qed.

  (***************************************************************************
  Part 2: Type Inference [5 points]
   ***************************************************************************)

  (* In this section, you'll be formalizing a constraint-based type
   system for the lambda calculus + Booleans + Pairs*)

  (* A constraint is a pair of types: *)
  Definition constraint := prod ty ty.

  Declare Scope stlc_scope.
  Notation "x == y" := (x, y) (at level 39): stlc_scope .

  Open Scope stlc_scope.

  Reserved Notation "Gamma '||-' t '\in' T '|' Cs"
           (at level 40, t custom stlc, T custom stlc_ty at level 0).

  (** Exercise: 4 points (has_type_w_constraints) *)
  (** The following inductive proposition defines a constraint-based
    type system for the lambda calculus with booleans.  For
    simplicitly, its rules omit the various conditions dealing with
    variable freshness we discussed in class, but it's morally correct
    for pedagogical purposes :).

    Using the lecture notes and the typing rules for the other terms
    below as inspiration, define the three constraint-based typing
    rules needed for pairs (TC_Pair, TC_Fst, and TC_Snd).

   Remember that your rules should be designed such that: a) they can
   derive a type and set of constraints for *any* expression b) any
   solution to generated constraints should also be a solution for the
   generated type.

   As a sanity check, you should be able to use your rules to prove
   the three product_inference_example_XX examples at this end of this
   homework. *)

  Inductive has_type_w_constraints
    : context -> tm -> ty -> list constraint -> Prop :=
  | TC_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma ||- x \in T | [ ]
  | TC_Abs : forall Gamma x T1 T2 t1 C,
      (x |-> T1 ; Gamma) ||- t1 \in T2 | C ->
      Gamma ||- \x: T1, t1 \in (T1 -> T2) | C
  | TC_App : forall Gamma T1 T2 t1 t2 C1 C2 C3 X,
      (Gamma ||- t1 \in T1 | C1) ->
      (Gamma ||- t2 \in T2 | C2) ->
      C3 = (T1 == (Ty_Arrow T2 X) :: C1 ++ C2) ->
      Gamma ||- (t1 t2) \in X | C3

  | TC_True : forall Gamma,
      Gamma ||- true \in Bool | [ ]
  | TC_False : forall Gamma,
      Gamma ||- false \in Bool | [ ]
  | TC_If : forall Gamma t1 t2 t3 Tc Tt Te Cc Ct Ce C,
      (Gamma ||- t1 \in Tc | Cc) ->
      (Gamma ||- t2 \in Tt | Ct) ->
      (Gamma ||- t3 \in Te | Ce) ->
      C = (Tc == Ty_Bool) :: (Tt == Te) :: Cc ++ Ct ++ Ce ->
      Gamma ||- if t1 then t2 else t3 \in Tt | C

  | TC_Pair : forall Gamma t1 t2 T1 T2 Tp C1 C2 C3,
      Gamma ||- t1 \in T1 | C1 ->
      Gamma ||- t2 \in T2 | C2 ->
      C3 = (Tp == Ty_Prod T1 T2) :: C1 ++ C2 ->
      Gamma ||- <t1, t2> \in Tp | C3
  | TC_Fst : forall Gamma t0 T1 T2 Tp Cp C,
      Gamma ||- t0 \in Tp | Cp ->
      C = (Tp == Ty_Prod T1 T2) :: Cp ->
      Gamma ||- fst t0 \in T1 | C
  | TC_Snd : forall Gamma t0 T1 T2 Tp Cp C,
      Gamma ||- t0 \in Tp | Cp ->
      C = (Tp == Ty_Prod T1 T2) :: Cp ->
      Gamma ||- snd t0 \in T2 | C

  where "Gamma '||-' t '\in' T '|' Cs" := (has_type_w_constraints Gamma t T Cs).

  (** An unifier (substitution) is a parital_map. Recall that principal unifier
      is the most general one. *)
  Definition unifier := partial_map ty.

  (** Here is an example taken from the slides. *)
  (* The constraint is {V == W -> U, X == Z -> V, Y == Z -> W} *)
  Example type_inference_example_sample :
    empty ||- \x: X, \y : Y, \z : Z, (x z) (y z) \in X -> Y -> Z -> U | [Ty_Var V == Ty_Arrow W U; Ty_Var X == Ty_Arrow Z V; Ty_Var Y == Ty_Arrow Z W].
  Proof.
    intros; repeat econstructor.
  Qed.
  (* We can write down the principal unifier for this example: (X |-> Z -> W -> U; Y |-> Z -> W).
     Because there may be no solution to the constraints, the type is [option unifier]. *)
  Definition unification_sample : option unifier :=
    Some (X |-> Ty_Arrow Z (Ty_Arrow W U); Y |-> Ty_Arrow Z W).

  (* Exercise: 1 point (product_inference_examples) *)
  Example product_inference_example_1 :
    empty ||- \x: X, fst x \in X -> U | [Ty_Var X == Ty_Prod U V].
  Proof.
  intros; repeat econstructor.
  Qed.

  Example product_inference_example_2 :
    empty ||- \x: X, snd x \in X -> V | [Ty_Var X == Ty_Prod U V].
  Proof.
    intros; repeat econstructor.
  Qed.

  Example product_inference_example_3 :
    empty ||- \x: X, \y : Y * Y, if x then fst y else false \in X -> Y * Y -> Y | [Ty_Var X == Ty_Bool; Ty_Var Y == Ty_Bool; Ty_Prod Y Y == Ty_Prod Y Y ].
  Proof.
    intros; repeat econstructor.
  Qed.


  (** The next five examples give the terms that generated the sets of
      constraints used in question 3 of the Pen+Paper portion of the
      homework. *)

  (* { } (the empty set of constraints) *)
  Example type_inference_example_1 :
    empty ||- \x: X, x \in X -> X | [ ].
  Proof.
    intros; repeat econstructor.
  Qed.

  (* {Y = V -> U, Y = X -> V}  *)
  Example type_inference_example_2 :
    empty ||- \x: X, \y : Y, y (y x) \in X -> Y -> U | [Ty_Var Y == Ty_Arrow V U; Ty_Var Y == Ty_Arrow X V].
  Proof.
    intros; repeat econstructor.
  Qed.

  (* {X = Bool, Y = X -> X}*)
  Example type_inference_example_3 :
    empty ||- \x: X, \y : Y, if x then y else (\z : X, z) \in X -> Y -> Y | [Ty_Var X == Ty_Bool; Ty_Var Y == Ty_Arrow X X].
  Proof.
    intros; repeat econstructor.
  Qed.

  (* {Bool -> Bool = X -> Y}*)
  Example type_inference_example_4 :
    (x |-> Ty_Arrow X Y; empty) ||- if x true then false else true \in Bool | [Ty_Bool == Ty_Bool; Ty_Bool == Ty_Bool; Ty_Arrow X Y == Ty_Arrow Ty_Bool Ty_Bool].
  Proof.
    intros; repeat econstructor.
  Qed.

  (*{ (Bool -> Y) -> Bool = Bool -> U} *)
  Example type_inference_example_5 :
    (x |-> Ty_Arrow (Ty_Arrow Ty_Bool Y) Ty_Bool ; empty) ||- x true \in U | [Ty_Arrow (Ty_Arrow Ty_Bool Y) Ty_Bool == Ty_Arrow Ty_Bool U].
  Proof.
    intros; repeat econstructor.
  Qed.

End LCPairsBool.
