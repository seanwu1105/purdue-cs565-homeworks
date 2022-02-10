(* Lab 4: Working with Inductive Evidence + Encoding Semantics in Coq *)

(* Tactics covered:
  - inversion
  - subst
  - assumption
  - lia
 *)

(* In order to step through this file, you'll need to update your path
   so that Coq knows where to look for the libraries from Logical
   Foundations.

   If you're using emacs / proof general, the easiest way to do this
   is to create a file named _CoqProject which includes the line:
   "-Q *PATH_TO_LF* LF", replacing the line *PATH_TO_LF* with the path to
   your local copy of Logical Foundations. This should work for other IDEs
   as well, but I can't promise that. Post problems / solutions this problem
   on piazza.
*)

From LF Require Export IndProp
     Maps
     Imp.
From Coq Require Import Init.Datatypes
     List
     Lia.
Open Scope string.

(** * Using Evidence in Proofs *)

(* Recall the definition of eveness from IndProp.v *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** Defining [ev] using [Inductive] tells Coq not only that the
    constructors [ev_0] and [ev_SS] are valid ways to build evidence
    that some number is [ev], but also that these two constructors are
    the _only_ ways to build evidence that numbers are [ev]. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros s E.
  (* In much the same way that we know n in the context is
     either a zero or the successor of another number, we know that
     the evidence of evenness given the assumption [E] could have been
     built in exactly two ways: either
      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

  (* This suggestions that we should be able to some sort of case
     analysis on how [E] was built. *)
  destruct E as [ | n' E']. (* destructed into two constructors: ev_0, ev_SS *)
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(* This works for *any* inductively defined proposition: *)
Inductive MyFavorites : string -> Prop :=
| IHeartDog : MyFavorites "Dachushunds"
| IHeart565 : MyFavorites "CS 565 Students"
| IHeartCoffee : MyFavorites "Coffee".

Lemma NoHeartBrocoli : forall s, MyFavorites s -> s <> "broccoli".
Proof.
  intros s1 [ | | ].
  - intro. discriminate.
  - intro. discriminate.
  - intro. discriminate.
Qed.

(* In fact, this is what is going on under the hood with all of our
   propositional connectives! *)
Print and. (* Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B *)

Lemma ElimAndR : forall (A B : Prop), (A /\ B) -> A.
Proof.
  intros A B [HA HB].
  exact HA.
Qed.

Print or.
(*  or_introl : A -> A \/ B | or_intror : B -> A \/ B *)

Lemma ElimOr : forall (A B C : Prop),
    (A \/ B) -> (A -> C) -> (B -> C) -> C.
Proof.
  intros A B C [HA | HB] ? ?.
  - apply H. exact HA.
  - apply H0. exact HB.
Qed.

(* [destruct] isn't always helpful, as this example shows: *)
Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  (* Similarly to before, we now that
     - [E] is [ev_0] (and [S (S n)] is [O]), or
     - [E] is [ev_SS n' E'] (and [S (S n)] is [S (S n')], where [E'] is
     evidence for [ev n']). *)
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
    (* The issue here is that destruct has somehow lost the connection
       between (S (S n)) from [E] and the number in the conclusion of
       [ev_0]. *)
Abort.

(* This missing connection between the arguments of the constructors
   and [2 + n] is precisely what we proved in our earlier inversion
   lemma [ev_inversion]. The proof is straightforward equipped with that fact (as our
   use of corollary indicates ;) ). *)
Corollary evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm as Heq.
   rewrite Heq. apply Hev.
Qed.

(** Coq provides a handy tactic called [inversion], which does the
    work of our inversion lemma and more besides. *)
Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H.
  inversion H.
  apply H1.
Qed.

(** The tactic [inversion] actually works on any [H : P] where
    [P] is an inductively defined proposition:

      - For each constructor of [P], make a subgoal and replace [H] by
        how exactly this constructor could have been used to prove [P].
      - Generate auxiliary equalities between the parameters of P and those
        used in the conclusion of the constructors (as with [ev_SS] above).
      - Discard contradictory subgoals (such as [ev_0] above). *)

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1. Proof. intros H. inversion H. Qed.

(* Just like [destruct], [inversion] works for any evidence of an
inductive proposition: *)
Lemma NoHeartBrocoli' : forall s, ~MyFavorites ("b" ++ s).
Proof.
  intros s H.
  inversion H.
Qed.

Definition ev' (n : nat) := exists m, n = double m.

(* Let's try to show that our new notion of evenness implies the one
   based on [double] above. *)
Lemma ev_even_firsttry : forall n,
  ev n -> ev' n.
Proof.
  (* WORK IN CLASS USING INVERSION *)
 Admitted.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If getting stuck here looks familiar, it is no coincidence: We've
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! *)

(** We could try inducting on n. *)
Lemma ev_even' : forall n,
  ev n -> ev' n.
Proof.
  induction n.
  - intro. exists 0. reflexivity.
  - intro.
    unfold even in IHn.
    inversion H. subst.
    (* Things have gotten quite messy: our IH is not sufficiently
       general, and generalizing it complicates the proof. Perhaps
       there's something else we can use [induction] on ? *)
Abort.


(* .... Pause for insightful input from the audience ...*)

















(* .... Continue pausing for insightful input from the audience ...*)



(** Let's try our current lemma again: *)
Lemma ev_even : forall n,
  ev n -> ev' n.
Proof.
  intros n E.
  induction E as [ |n' E' IH].
  - exists 0. reflexivity.
  - unfold even in IH.
    destruct IH as [m m_eq].
    unfold even.
    exists (S m).
    simpl.
    rewrite <- m_eq.
    reflexivity.
Qed.

(* For comparision, here's the more complicated proof by induction on
   [n]. *)
Lemma ev_even_complicated' : forall n,
    (ev n -> ev' n) /\ (ev (S n) -> ev' (S n)).
Proof.
  intro.
  induction n.
  - split.
    + exists 0. reflexivity.
    + intro; inversion H.
  - split.
    + intro. destruct IHn.
      apply H1. assumption.
    + intro. destruct IHn.
      inversion H. subst.
      apply H0 in H3.
      destruct H3 as [m m_eq].
      exists (S m).
      simpl.
      rewrite <- m_eq.
      reflexivity.
Qed.

(** As we will see shortly, induction on evidence is a recurring
    technique across many areas, and in particular when formalizing
    the semantics of programming languages, where many properties of
    interest (e.g. semantics, typing rules) are defined inductively. *)

Module IndEvidencePlayground.

  Import ListNotations.
  (** Before we get there, let's consider how we can use evidence of the
    fact that one number is less than or equal to another. *)

  Inductive le : nat -> nat -> Prop :=
  | le_n : forall (n : nat), le n n
  | le_S : forall (n m : nat),  le n m -> le n (S m).

  (** Note that we could have also written the above proposition in a
     style that is much closer to 'normal' induction datatypes: *)

   (* Inductive le : nat -> nat -> Prop :=
     | le_n (n : nat)                : le n n
     | le_S (n m : nat) (H : le n m) : le n (S m). *)

  (* These two definition are equivalent (and desugar into the exact
     same thing "under the hood"). *)

  Notation "m <= n" := (le m n).

  (** A quick sanity checks using inversion: *)

  Theorem test_le3 :
    (2 <= 1) -> 2 + 2 = 5.
  Proof.
  (* WORK IN CLASS *) Admitted.

  Lemma le_trans : forall (m n o : nat),
      le m n -> le n o -> le m o.
  Proof.
    intros m n o le_m_n le_n_o.
    generalize dependent m.
    induction le_n_o.
    - intros m le_m_n.
      (* We could solve this goal with [apply le_m_n], but let's learn a
       new tactic instead: *)
      assumption.
    (* [assumption]: Try to find a hypothesis [H] in the context that
     exactly matches the goal; if one is found, behave like [apply
     H]. *)
    - intros m' le_m'_n.
      (* This goal matches one of the constructors of le, so we could
       use [apply le_S] to make progress, but let's use the
       [constructor] tactic from the last lecture instead. *)
      constructor.
      (* - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to current goal.  If one is found, behave
       like [apply c]. *)
      apply IHle_n_o.
      assumption.
  Qed.

  (* For our last example of inducting on evidence, consider the
     following definition of list permutation as inductive proposition: *)
  Inductive Permutation {A : Type} : list A -> list A -> Prop :=
  | perm_nil: Permutation [] []
  | perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
  | perm_swap x y l : Permutation (y::x::l) (x::y::l)
  | perm_trans l l' l'' :
      Permutation l l' -> Permutation l' l'' -> Permutation l l''.

  (* Trying to prove that permutation is symmetric by [induction l] is
     complicated. [induction] on evidence is much nicer! *)
  Lemma Permutation_sym : forall (A : Type) (l l' : list A),
      Permutation l l' -> Permutation l' l.
  Proof.
    intros A l l' E.
    induction E.
  (* WORK IN CLASS *) Admitted.

End IndEvidencePlayground.

Module AutomationPlayground.
  (* To see how we embed the big-step semantics of a programming
   language in Coq, let's revisit our simple aritmetic expression
   language from the second lab. *)
  Inductive aexp : Type :=
  | ANum (a : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult  (a1 a2 : aexp).

  (* Here is our evaluation function for arithmetic expressions: *)
  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  (* Since many of our proofs about the semantics of arithmetic
     expressions use numbers in some way, we begin by introducing a
     new tactic for dealing with goals involving natural numbers. *)

  (* ================================================================= *)
  (** ** The [lia] Tactic *)

  (** The [lia] tactic implements a decision procedure for a subset of
      first-order logic called _Presburger arithmetic_.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and ordering ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or fail, meaning
    that the goal is actually false.  (If the goal is _not_ of this
    form, [lia] will also fail.) *)

  (* Note that we have to import the Lia module to make this tactic
     available (we did so at the beginning of this file). *)

  Example silly_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. lia.
  Qed.

  Example add_comm_lia : forall m n,
      m + n = n + m.
  Proof.
    intros. lia.
  Qed.

  Example add_assoc_lia : forall m n p,
      m + (n + p) = m + n + p.
  Proof.
    intros. lia.
  Qed.

  Reserved Notation "e '==>' n" (at level 90, left associativity).

  (* Last Thursday, we encoded the big-step operational semantics of
     our expression language as the inductive proposition defined by
     the following rules: *)

  (*
============================ (E_ANum
         ANum n ==> n


  e1 ==> n1     e2 ==> n2
============================ 	(E_APlus)
   APlus e1 e2 ==> n1+n2

   e1 ==> n1 	   e2 ==> n2
============================ (E_AMinus)
   AMinus e1 e2 ==> n1-n2

e1 ==> n1 	e2 ==> n2
============================  (E_AMult)
   AMult e1 e2 ==> n1 * n2 	 *)

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

  (* ================================================================= *)
  (** ** Equivalence of the Definitions *)

  (** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)

  Theorem aevalR_if_aeval : forall a n,
      aeval a = n -> (a ==> n).
  Proof.
    intro a.
    (* For this proof, we need to induct on the structure of the
    expression [a]: *)
    induction a.
    - (* ANum *)
      simpl. intros.
      (* Now, we could rewrite the goal using our assumption [H], but
         this is as good a time as any to introduce the new [subst]
         tactic. This tactic has two variants that help to automates
         the humdrummery of doing lots of manual rewrites:

      - subst x: For a variable x, find an assumption x = e or e = x
         in the context, replace x with e throughout the context and
         current goal, and clear the assumption.

      - subst: Substitute away all assumptions of the form x = e or e
         = x (where x is a variable). *)
      subst a.
      apply E_ANum.
    - (* APlus *)
      simpl. intros. subst n.
      apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
    - (* AMinus *)
      simpl. intros. subst.
      apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
    - (* AMult *)
      simpl. intros. subst.
      apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
  Qed.

  Theorem aeval_if_aevalR : forall a n,
      (a ==> n) -> aeval a = n.
  Proof.
    intros a n H.
    (* For this direction of the proof, we could again induct over a:*)
    induction a.
    (* This would require us to use inversion and subst to make
    progress. This works, but the proof gets a little messy. *)
    inversion H. subst.
    (* Instead, observe that we have an inductively defined
       proposition as an assumption; this contains considerably
       more information than [a] alone. So, let's induct on that! *)
    Undo 3.
    induction H.
    (* WORK IN CLASS: *)
  Admitted.

End AutomationPlayground.

Module SemanticsPlayground.
  (* Here is an inductive proposition encoding the big-step semantics
     of the simple imperative language from last Thursday: *)

  Reserved Notation
           "st '=[' c ']=>' st'"
           (at level 40, c custom com at level 99,
            st constr, st' constr at next level).

  Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

  (* Note how these nicely correspond to the inference rules we saw
  last week:

=====================  	(E_Skip)
  st =[ skip ]=> st

aeval st a = n
===================== (E_Asgn)
st =[ x := a ]=> (x !-> n ; st)

st =[ c1 ]=> st'
st' =[ c2 ]=> st''
===================== 	(E_Seq)
st =[ c1;c2 ]=> st''

beval st b = true
st =[ c1 ]=> st'
===================== 	(E_IfTrue)
st =[ if b then c1 else c2 end ]=> st'

beval st b = false
st =[ c2 ]=> st'
===================== 	(E_IfFalse)
st =[ if b then c1 else c2 end ]=> st'

beval st b = false
===================== 	(E_WhileFalse)
st =[ while b do c end ]=> st

beval st b = true
st =[ c ]=> st'
st' =[ while b do c end ]=> st''
===================== 	 	(E_WhileTrue)
st =[ while b do c end ]=> st'' 	 *)

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

  Definition Z := "Z".

  Example ceval_example1:
    empty_st =[
      X := 2;
      if X <= 1
       then Y := 3
       else Z := 4
     end
    ]=> (Z !-> 4 ; X !-> 2).
  Proof.
  Admitted.

  (* A more interesting fact is that a while loop whose condition is
     always true never terminates (Imp doesn't have any breaks, after
     all): *)

  Definition loop : com :=
    <{while true do
      skip
      end }>.

  (* Due to the vagaries of Coq Notations, we had to use the <{ and }>
     brackets above to help Coq correctly parse our custom IMP syntax. *)
  Theorem loop_never_stops : forall st st',
      ~(st =[ loop ]=> st').
  Proof.
    intros st st' contra. unfold loop in contra.
    (* WORK IN CLASS *)
  Admitted.

  (* The following proposition encodes the fact that a program doesn't
   have any loops in it. *)

Inductive no_whilesR: com -> Prop :=
| NoWhilesSkip : no_whilesR <{skip}>
| NoWhilesAssgn : forall x a, no_whilesR <{x := a}>
| NoWhilesSeq : forall c1 c2,
    no_whilesR c1 -> no_whilesR c2 -> no_whilesR <{c1 ; c2}>
| NoWhilesIf : forall b ct ce,
    no_whilesR ct -> no_whilesR ce -> no_whilesR <{if b then ct else ce end}>.

(* An imp program without any loops in it will always terminate: *)
Lemma no_whiles_terminating :
  forall c, no_whilesR c ->
            forall st, exists st', st =[c]=> st'.
Proof.
  intros c E.
  induction E; intros.
  - intros. exists st. constructor.
  - intros. exists ((x !-> aeval st a ; st)). constructor.
    reflexivity.
  - specialize (IHE1 st). destruct IHE1 as [st' IHE1].
    specialize (IHE2 st'). destruct IHE2 as [st'' IHE2].
    exists st''. apply E_Seq with (st' := st'); assumption.
  - destruct (beval st b) eqn: b_eq.
    + specialize (IHE1 st). destruct IHE1 as [st' IHE1].
      exists st'; constructor; assumption.
    + specialize (IHE2 st). destruct IHE2 as [st' IHE2].
      exists st'; apply E_IfFalse; assumption.
Qed.

End SemanticsPlayground.
