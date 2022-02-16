(* Lab 4: Working with Inductive Evidence + Encoding Semantics in Coq *)

(* Tactics covered:
  - inversion
  - subst
  - constructor
  - assumption
  - omega

- tacticals:
  + sequencing (;)
  + repeat
  + try
  + first *)

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
     List.
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
  intros n E.
  (* In much the same way that we know n in the context is
     either a zero or the successor of another number, we know that
     the evidence of evenness given the assumption [E] could have been
     built in exactly two ways: either
      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

  (* This suggestions that we should be able to some sort of case
     analysis on how [E] was built. *)
  destruct E as [ | n' E'].
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
  intros s [ | | ].
  - rewrite <- String.eqb_eq. simpl. discriminate.
  - rewrite <- String.eqb_eq. simpl. discriminate.
  - rewrite <- String.eqb_eq. simpl. discriminate.
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
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
    (* The issue here is that destruct has somehow lost the connection
       between the number used in [E] and the number used in the
       conclusion of [ev_0]. *)
Abort.

(* This missing connection between the arguments of the constructors
   and [2 + n] is precisely what we proved in our earlier inversion
   lemma. The proof is straightforward equipped with that fact (as our
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
  intros n E.
  inversion E as [| n' E' EQ].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The tactic [inversion] actually works on any [H : P] where
    [P] is defined by [Inductive]:

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

(* Let's try to show that our new notion of evenness implies the one
   based on [double]. *)

Lemma ev_even_firsttry : forall n,
  ev n -> even n.
Proof.
  intros n ev. unfold even.
  inversion ev.
  - exists 0. reflexivity.
  - exists (S n0). simpl.
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to
    use case analysis to prove results that required induction.  And
    once again the solution is... induction! *)

(** We could try inducting on n. *)
Lemma ev_even' : forall n,
  ev n -> even n.
Proof.
  induction n.
  - intro. exists 0. reflexivity.
  - intro.
    inversion H. subst.
    (* Things have gotten quite messy: our IH is not sufficiently
       general, and generalizing it complicates the proof. Perhaps
       there's something else we can use [induction] on ? *)
Abort.


(* .... Pause for insightful input from the audience ...*)

















(* .... Continue pausing for insightful input from the audience ...*)



(** Let's try our current lemma again: *)
Lemma ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(* For comparision, here's the more complicated proof by induction on
   [n]. *)
Lemma ev_even_complicated' : forall n,
    (ev n -> even n) /\ (ev (S n) -> even (S n)).
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

(** As we will see shortly, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

Module IndEvidencePlayground.

  Import ListNotations.
  (** Before we get there, let's consider how we can use evidence of the
    fact that one number is less than or equal to another. *)

  Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

  Notation "m <= n" := (le m n).

  (** Some sanity checks... *)

  Theorem test_le1 :
    3 <= 3.
  Proof.
  (* WORK IN CLASS *) Admitted.

  Theorem test_le2 :
    3 <= 6.
  Proof.
  (* WORK IN CLASS *) Admitted.

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
       use [apply le_S] to make progress, but let's expand our tactic
       toolbox instead. *)
      constructor.
      (* - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to current goal.  If one is found, behave
       like [apply c]. *)
      Fail assumption.
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
    intros A l l' Perml. induction Perml.
    - constructor.
    - constructor. assumption.
    - constructor.
    - Fail constructor.
      (* [constructor] won't work here, because [apply perm_trans]
         doesn't work: *)
      apply (perm_trans l'' l').
      assumption.
      assumption.
  Qed.

End IndEvidencePlayground.

Module AutomationPlayground.
  (* Before looking at how to represent the syntax and semantics of Imp
   in Coq, we're first going to see how to automate proof scripts a
   bit more. We'll use the proof of soundness of the aritmetic
   expression optimizer from the second lab. *)
  Inductive aexp : Type :=
  | ANum (a : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult  (a1 a2 : aexp).

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Fixpoint aexp_opt_zero (a : aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) e2 => aexp_opt_zero e2
    | APlus e1 e2 => APlus (aexp_opt_zero e1) (aexp_opt_zero e2)
    | AMinus e1 e2 => AMinus (aexp_opt_zero e1) (aexp_opt_zero e2)
    | AMult e1 e2 => AMult (aexp_opt_zero e1) (aexp_opt_zero e2)
    end.

  Compute (aexp_opt_zero (AMinus (APlus (ANum 0) (ANum 4)) (ANum 3))).
  (* Before optimization: (0 + 4) - 3*)
  (* After optimization: 4 - 3 *)

  Theorem aexp_opt_zero_sound
    : forall a, aeval (aexp_opt_zero a) = aeval a.
  Proof.
    induction a.
    - reflexivity.
    - simpl.
      destruct a1.
      + destruct a.
        * simpl. rewrite -> IHa2. reflexivity.
        * simpl. rewrite -> IHa2. reflexivity.
      + rewrite <- IHa1. rewrite <- IHa2.
        reflexivity.
      + rewrite <- IHa1. rewrite <- IHa2. reflexivity.
      + rewrite <- IHa1. rewrite <- IHa2. reflexivity.
    - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
    - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Qed.

  (* ================================================================= *)
  (** Tacticals *)

  (** _Tacticals_ are tactics that take other tactics as arguments --
      "higher-order tactics," if you will.  *)

(* ----------------------------------------------------------------- *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (rather than failing). *)

  Theorem silly1 : forall ae, aeval ae = aeval ae.
  Proof. try reflexivity. (* This just does [reflexivity]. *) Qed.

  Theorem silly2 : forall (P : Prop), P -> P.
  Proof.
    intros P HP.
    try reflexivity. (* Just [reflexivity] would have failed. *)
    apply HP. (* We can still finish the proof in some other way. *)
  Qed.

  (* ----------------------------------------------------------------- *)
  (** *** The [;] Tactical (Simple Form) *)

  (** In its most common form, the [;] tactical takes two tactics as
    arguments.  The compound tactic [T;T'] first performs [T] and then
    performs [T'] on _each subgoal_ generated by [T]. *)

  (** For example: *)
  Lemma foo : forall n, Nat.leb 0 n = true.
  Proof.
    intros.
    destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
  Qed.

  (** We can simplify this proof using the [;] tactical: *)

  Lemma foo' : forall n, Nat.leb 0 n = true.
  Proof.
    intros.
    (* [destruct] the current goal *)
    destruct n;
      (* then [simpl] each resulting subgoal *)
      simpl;
      (* and do [reflexivity] on each resulting subgoal *)
      reflexivity.
  Qed.

  (** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)
  Theorem optimize_0plus_sound'
    : forall a, aeval (aexp_opt_zero a) = aeval a.
  Proof.
    intros a; induction a;
      (* Most cases follow directly by the IH... *)
      try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    - reflexivity.
    - simpl.
      destruct a1;
        try (rewrite <- IHa1; rewrite <- IHa2; reflexivity).
      + destruct a;
          simpl; rewrite -> IHa2; reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
(** *** The [repeat] Tactical *)

  Import ListNotations.
(** The [repeat] tactical takes another tactic and keeps applying this
    tactic until it fails. Here is an example showing that [10] is in
    a long list using repeat. *)

  Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.
  (* When writing example facts using our inductive propositions,
     [repeat constructor] can be quite helpful! *)

  Theorem test_le2' :
    3 <= 6.
  Proof.
    repeat constructor.
  Qed.

  (* While evaluation in Coq's term language, Gallina, is guaranteed to
     terminate, tactic evaluation is not! This does not affect Coq's
     logical consistency, however, since the job of repeat and other
     tactics is to guide Coq in constructing proofs; if the construction
     process diverges (i.e., it does not terminate), this simply means
     that we have failed to construct a proof, not that we have
     constructed a wrong one. *)

  (* ================================================================= *)
  (** ** Defining New Tactic Notations *)

  (** Coq also provides several ways of "programming" tactic scripts:
      - [Tactic Notation]: syntax extension for tactics (good for
      simple macros)
      - [Ltac]: scripting language for tactics (good for more
      sophisticated proof engineering)
      - OCaml tactic scripting API (for wizards)

      An example [Tactic Notation]: *)

  Tactic Notation "simpl_and_try" tactic(c) :=
    simpl;
    try c.

  (* ================================================================= *)
  (** ** The [omega] Tactic *)

  (** The [omega] tactic implements a decision procedure for a subset of
      first-order logic called _Presburger arithmetic_.  It is based on
      the Omega algorithm invented by William Pugh [Pugh 1991].

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and ordering ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or fail, meaning
    that the goal is actually false.  (If the goal is _not_ of this
    form, [omega] will also fail.) *)

  Example silly_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. Omega.omega.
  Qed.

  Reserved Notation "e '==>' n" (at level 90, left associativity).

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

  Theorem aeval_iff_aevalR : forall a n,
      (a ==> n) <-> aeval a = n.
  Proof.
    split.
    - (* -> *)
      intros H.
      induction H; simpl.
      + (* E_ANum *)
        reflexivity.
      + (* E_APlus *)
        rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
      + (* E_AMinus *)
        rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
      + (* E_AMult *)
        rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    - (* <- *)
      generalize dependent n.
      induction a;
        simpl; intros; subst.
      + (* ANum *)
        apply E_ANum.
      + (* APlus *)
        apply E_APlus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      + (* AMinus *)
        apply E_AMinus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      + (* AMult *)
        apply E_AMult.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
  Qed.

  (* Using a little bit of automation, we can shrink this proof
     considerably. *)
  Theorem aeval_iff_aevalR' : forall a n,
      (a ==> n) <-> aeval a = n.
  Proof.
    split.
    - (* -> *)
      intros H; induction H; simpl;
        first [rewrite IHaevalR1; rewrite IHaevalR2; reflexivity
              | reflexivity].
    - generalize dependent n.
      induction a;
        simpl; intros; subst; constructor;
          try first [ apply IHa1; reflexivity
                    | apply IHa2; reflexivity].
  Qed.
  (* WORK IN CLASS Admitted. *)

End AutomationPlayground.

Module SemanticsPlayground.

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
    (* We must supply the intermediate state *)
    apply E_Seq with (X !-> 2).
    - (* assignment command *)
      apply E_Ass. reflexivity.
    - (* if command *)
      apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.
  Qed.

  (* A more interesting fact is that a while loop whose condition is
     always true never terminates (Imp doesn't have any breaks, after
     all): *)
  Definition loop : com :=
    <{while true do
      skip
    end }>.
  Theorem loop_never_stops : forall st st',
      ~(st =[ loop ]=> st').
  Proof.
    intros st st' contra. unfold loop in contra.
    remember (<{while true do skip end}>) as loopdef eqn:Heqloopdef.
    induction contra; try discriminate.
    - injection Heqloopdef as beq ceq; subst.
      discriminate.
    - apply IHcontra2; assumption.
  Qed.

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
  intros c H; induction H; intros.
  - exists st. constructor.
  - exists (x !-> aeval st a; st); constructor; reflexivity.
  - specialize (IHno_whilesR1 st). destruct IHno_whilesR1 as [st' IHno_whilesR1].
    specialize (IHno_whilesR2 st'). destruct IHno_whilesR2 as [st'' IHno_whilesR2].
    exists st''. apply E_Seq with (st' := st'); assumption.
  - destruct (beval st b) eqn: b_eq.
    + specialize (IHno_whilesR1 st). destruct IHno_whilesR1 as [st' IHno_whilesR1].
      exists st'; constructor; assumption.
    + specialize (IHno_whilesR2 st). destruct IHno_whilesR2 as [st' IHno_whilesR2].
      exists st'; apply E_IfFalse; assumption.
Qed.

End SemanticsPlayground.
