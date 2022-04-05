(* Lab 8: More Proof Automation /and/ Metatheory of Hoare Logic. *)

(* Tactics covered:
   - auto
 *)

(** Our job for this lab:
   - Explore the magical world of proof automation in more depth

   - (If there's time [but there probably won't be]), look at proof of soundness and relative completeness for Hoare logic
 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Import Hoare.
From DS Require Import Fixpoints.

(** Up to now, we've used the more manual part of Coq's tactic
    facilities.  In this Lab, we'll learn more about some of Coq's
    powerful automation features: proof search via the [auto] tactic,
    automated forward reasoning via the [Ltac] hypothesis matching
    machinery, and several additional tacticals (higher-order
    tactics).  Using these features together with Ltac's scripting
    facilities will enable us to make our proofs startlingly short!
    Used properly, they can also make proofs more maintainable and
    robust to changes in underlying definitions.  A deeper treatment
    of [auto] and [eauto] can be found in the [UseAuto] chapter in
    _Programming Language Foundations_.

    Our motivating example will be this proof, repeated with just a
    few small changes from the [Imp] chapter.  We will simplify this
    proof in several stages. *)

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1.
  - (* E_Skip *) intros st2 E2. inversion E2. subst. reflexivity.
  - (* E_Ass *) intros st2 E2. inversion E2. subst. reflexivity.
  - (* E_Seq *)
    intros st2 E2. inversion E2. subst.
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - intros st2 E2. inversion E2. subst.
    + (* b evaluates to true *)
      apply IHE1. assumption.
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse *)
      intros st2 E2. inversion E2. subst.
      + (* b evaluates to true (contradiction) *)
        rewrite H in H5. discriminate.
      + (* b evaluates to false *)
        apply IHE1. assumption.
  (* E_WhileFalse *)
  - intros st2 E2. inversion E2. subst.
    + (* b evaluates to false *)
      reflexivity.
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - intros st2 E2. inversion E2. subst.
    + (* b evaluates to false (contradiction) *)
      rewrite H in H4. discriminate.
    + (* b evaluates to true *)
      rewrite (IHE1_1 st'0 H3) in *.
      apply IHE1_2. assumption.
Qed.

(* ################################################################# *)
(** * The [auto] Tactic *)

(** Thus far, our proof scripts mostly apply relevant hypotheses or
    lemmas by name, and one at a time. *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

(** In the fourth lab, we saw how to use the ';' tactical to chain
    together multiple tactics: *)
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
    intros; destruct n; (simpl; reflexivity).
  Qed.

  Example auto_example_1' : forall (P Q R: Prop),
      (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    (* WORK IN CLASS *)
  Admitted.

  (** The [auto] tactic frees us from this drudgery by _searching_ for a
      sequence of applications that will prove the goal: *)
  Example auto_example_1'' : forall (P Q R: Prop),
      (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    auto.
  Qed.

(** The [auto] tactic solves goals that are solvable by any combination of
     - [intros] and
     - [apply] (of hypotheses from the local context,
                and additional facts (hints) specified by the user.).

   This is a kind of enchanced variant of [assumption],
   which can chain together sequences of apply to solve the current goal *)

(** Using [auto] is always "safe" in the sense that it will never fail
    and will never change the proof state: either it completely solves
    the current goal, or it does nothing. *)

  Example auto_example_1''' : forall (P Q R: Prop),
      (P -> Q) -> (Q -> R) -> P -> R /\ 5 <= 15.
  Proof.
    intros P Q R H1 H2 H3.
    (* WORK IN CLASS *)
  Admitted.

(** Here is a larger example showing [auto]'s power: *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** Proof search could, in principle, take an arbitrarily long time,
    so there are limits to how far [auto] will search by default. *)
Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, [auto] does nothing *)
  auto.
  (* [auto] takes an optional argument specifying how deep to search (default is 5) *)
  auto 6.
Qed.

(** We can extend the hint database just for the purposes of one
    application of [auto] by writing "[auto using ...]". *)
Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto.
  intros; apply le_antisym. auto.
  Undo 1.
  auto using le_antisym.
Qed.

(** In any given development there will probably be
    some specific constructors and lemmas that are used very often in
    proofs.  We can add these to the global hint database via the command

    Hint Resolve T : core.

    at the top level, where [T] is a top-level theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication).

    When searching for potential proofs of the current goal,
    [auto] considers the hypotheses in the current context together
    with a _hint database_ of other lemmas and constructors. *)

Theorem ceval_ex: forall c1 c2 st st1 st2,
    st =[ c1 ]=> st1  ->
    st1 =[ c2 ]=> st2 ->
    st =[ c1; c2  ]=> st2.
Proof.
  (* WORK IN CLASS *)
Admitted.

(* Some common lemmas about equality and logical operators are
    installed in this hint database by default.*)
Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto.
Qed.

(** If we want to see which facts [auto] is using, we can use
    [info_auto] instead. *)
Example auto_example_4' : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  info_auto.
Qed.

(* If [auto] tried to [apply] every available fact, it would be very
   slow indeed, so it uses several heuristics to decide what to use.
   We can also see which lemmas / constructors [auto] will try to
   apply to the current goal using the [Print Hint] command.  *)
Example auto_example_5: 2 = 2.
Proof.
  Print Hint.
  info_auto.
Qed.

(**  It is also sometimes necessary to add

      Hint Unfold d : core.

    where [d] is a defined symbol, so that [auto] knows to expand uses
    of [d], thus enabling further possibilities for applying lemmas that
    it knows about. *)

(** It is also possible to define specialized hint databases that can
    be activated only when needed.  See the Coq reference manual for
    details. *)

Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
  (* WORK IN CLASS *)
Abort.

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  Print Hint.
  info_auto. (* try also: info_auto. *)
Qed.

(* As a shorthand, we can write

      Hint Constructors c : core.

    to tell Coq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c]. *)
#[local] Hint Constructors ceval : core.
Theorem ceval_ex_2: forall st ,
    st =[ X := 4; Y := 5  ]=> (Y !-> 5; X !-> 4; st).
Proof.
  intros.
  assert (st =[ X := 4 ]=> (X !-> 4; st)) by (econstructor; reflexivity).
  assert ((X !-> 4; st) =[ Y := 5 ]=> (Y !-> 5; X !-> 4; st)) by (econstructor; reflexivity).
  eauto.
Qed.

Theorem ceval_ex_2': forall st ,
    st =[ X := 4; Y := 5  ]=> (Y !-> 5; X !-> 4; st).
Proof.
  debug auto.
  (* WORK IN CLASS *)
Admitted.

(** Let's take a first pass over [ceval_deterministic] to simplify the
    proof script. *)

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  (* Our first optimization is to observe that we did inversion on the
     second hypothesis in every subgoal, so let's use ";" here. *)
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *; auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *; auto.
Qed.

(* ################################################################# *)
(** * Searching For Hypotheses *)

(** The proof has become simpler, but there is still an annoying
    amount of repetition. Let's start by tackling the contradiction
    cases. Each of them occurs in a situation where we have both

      H1: beval st b = false

    and

      H2: beval st b = true

    as hypotheses.  The contradiction is evident, but demonstrating it
    is a little complicated: we have to locate the two hypotheses [H1]
    and [H2] and do a [rewrite] following by a [discriminate].  We'd
    like to automate this process.

    (In fact, Coq has a built-in tactic [congruence] that will do the
    job in this case.  But we'll ignore the existence of this tactic
    for now, in order to demonstrate how to build forward search
    tactics by hand.)

    As a first step, we can abstract out the piece of script in
    question by writing a little function in Ltac. *)

Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Theorem ceval_deterministic'': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rwd H H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rwd H H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rwd H H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rwd H H4.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto.
Qed.

(** That was a bit better, but we really want Coq to discover the
    relevant hypotheses for us.  We can do this by using the [match
    goal] facility of Ltac. *)

Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2
  end.

(** This [match goal] looks for two distinct hypotheses that
    have the form of equalities, with the same arbitrary expression
    [E] on the left and with conflicting boolean values on the right.
    If such hypotheses are found, it binds [H1] and [H2] to their
    names and applies the [rwd] tactic to [H1] and [H2].

    Adding this tactic to the ones that we invoke in each case of the
    induction handles all of the contradictory cases. *)

Theorem ceval_deterministic''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; try find_rwd; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_WhileTrue *)
    + (* b evaluates to true *)
      rewrite (IHE1_1 st'0 H3) in *.
      auto.
Qed.

(** Let's see about the remaining cases. Each of them involves
    applying rewrting an hypothesis after feeding it with the required
    condition. We can automate the task of finding the relevant
    hypotheses to rewrite with. *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

(** The pattern [forall x, ?P x -> ?L = ?R] matches any hypothesis of
    the form "for all [x], _some property of [x]_ implies _some
    equality_."  The property of [x] is bound to the pattern variable
    [P], and the left- and right-hand sides of the equality are bound
    to [L] and [R].  The name of this hypothesis is bound to [H1].
    Then the pattern [?P ?X] matches any hypothesis that provides
    evidence that [P] holds for some concrete [X].  If both patterns
    succeed, we apply the [rewrite] tactic (instantiating the
    quantified [x] with [X] and providing [H2] as the required
    evidence for [P X]) in all hypotheses and the goal. *)

Theorem ceval_deterministic''''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; try find_rwd;
    try find_eqn; eauto.
Qed.

(* That was fun, but as [ceval_ex_2'] illustrated, [auto] is not a
   magical bullet. Let's revisit an example from a couple of labs
   ago to see how we can use some additional tacticals to help
   automate proofs like [ceval_ex_2']. *)

(* To recap everything we've seen today:
   - [auto] : try to solve goals via a combination of [intros] and [apply],
     leaving the goal unchanged if any subgoals remain).
   - [auto using X, Y, Z] : consider lemmas X, Y, and Z when using [auto].
   - [Hint Resolve X] : Add X to a database of lemmas that [auto] should consider
   - [Hint Unfold X] : Tell [auto] to try to [unfold X] when looking at what hints to use
   - [Hint Constructors T] : add all the constructors of to the hint database

   - [Ltac foo H := ... ]: define a new tactic
   - [match goal with ... ] : 'pattern match' on the goal to discover the
   - tac; [tac1 | .... | tacn] : specify a tactic for each individual subgoal.
   - first [tac1 | .... | tacn] : apply tactics in order until the first one succeeds. Fail if none do.
   - solve [ tac ] : use tac to solve a goal, failing otherwise.

*)


(* ################################################################# *)
(** * Partial Hoare Logic *)



Section Hoare.

  (* We first develop a proof theory for building up evidence of Hoare
     triples as an inductive proposition. Following a standard
     convention from proof theory, we denote the claims we can build
     evidence for using these rules as |- {{P}} c {{Q}}. *)
  Reserved Notation " |- {{ P }}  c  {{ Q }}"
           (at level 40, c at next level).

  Inductive hoare_proof : Assertion -> com -> Assertion -> Prop :=
  | H_Skip : forall P,
      |- {{ P }} <{skip}> {{P}}
  | H_Asgn : forall Q V a,
      |- {{Q[V |-> a]}} <{V := a}> {{Q}}
  | H_Seq  : forall P c Q d R,
      |- {{P}} c {{Q}} ->
       |- {{Q}} d {{R}} ->
       |- {{P}} <{c;d}> {{R}}
  | H_If : forall P Q b c1 c2,
       |- {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
       |- {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
       |- {{P}} <{if b then c1 else c2 end}> {{Q}}
  | H_While : forall P b c,
       |- {{fun st => P st /\ bassn b st}} c {{P}} ->
       |- {{P}} <{while b do c end}> {{fun st => P st /\ ~ (bassn b st)}}
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
       |- {{P'}} c {{Q'}} ->
          P ->> P' ->
          Q' ->> Q ->
       |- {{P}} c {{Q}}

where " |- {{ P }}  c  {{ Q }}" := (hoare_proof  P c Q) : hoare_spec_scope.

  (* The triples that can be proven using these rules do not
     necessarily align with /semantically/ valid hoare triples. The
     proofs of soundness and completeness establish they are the same.
     Again following proof theory conventions, we denote semantically
     valid hoare triples as |= {{P}} c {{Q}}. *)

  Notation " '|=' {{ P }}  c  {{ Q }}" :=
    (hoare_triple  P c Q) (at level 40, c at next level)
    : hoare_spec_scope.

  (* We begin by proving that our logic is sound, i.e. it can only be
     used to prove only semantically valid Hoare triples. *)

  (* The case for the [H_While] rule is the most interesting, so we
     define a seperate lemma for it: *)
  Lemma hoare_while : forall P b c,
       |= {{fun st => P st /\ bassn b st}} c {{P}} ->
       |= {{P}} <{while b do c end}> {{fun st => P st /\ ~ (bassn b st)}}.
  Proof.
    unfold hoare_triple.
    intros ? ? ? ? ? ? HE ?. remember <{while b do c end}> eqn:Heq.
    induction HE; try inversion Heq; subst.
    - eauto.
    - eauto.
  Qed.

  Theorem hoare_proof_sound : forall P c Q,
      |- {{P}} c {{Q}} ->
      |= {{P}} c {{Q}}.
  Proof.
    intros ? ? ? pf.
    (* The proof of soundness is by induction on the proof tree of the
       claim |- {{P}} c {{Q}}. *)
    induction pf; intros st st' HE HP; eauto using hoare_while;
      try (inversion HE; subst; eauto);
      eapply hoare_while; eauto.
  Qed.

  (* The weakest (liberal) precondition for an assertion [Q] and
     command [c] is the set of initial states from which [c] always
     either fails to terminate, or ends in a final state satisfying
     [Q].

     We define a proposition, [wlp], to capture when an assertion is a
     weakest precondition: *)
  Definition wlp
             (c : com)
             (Q : Assertion)
             (P : Assertion)
    : Prop := forall (P' : Assertion),
      |= {{P'}} c {{Q}}
      -> (P' ->> P).

  (* The weakest liberal precondition for the loop [while b c] and
     postcondition [Q] needs to be entailed by a precondition that either:
     a) causes the loop to immediately terminate in a state satisfying Q
     b) causes the loop to terminate in a state satisfying Q after one iteration
     c) causes the loop to terminate in a state satisfying Q after two iterations
     ...
     infinity) causes the loop to run forever. *)

  (* [wlp_one_iter Q c b WLP G] calculates the precondition that either:

     a) makes the guard [b] false and entails [Q] OR

     b) makes the guard [b] true and is the weakest precondition for
        command [c] and postcondition [G]. *)

  Definition wlp_one_iter
             (Q : Assertion)
             (c : com)
             (b : bexp)
             (WLP : com -> Assertion -> Assertion)
             (G : Assertion)
    : Assertion :=
    (   (~ b /\ Q)
        \/ (b /\ WLP c G))%assertion.

  (* The weakest liberal precondition for the loop [while b c] is the
     greatest fixed point of [wlp_one_iter]. *)
  Definition wlp_while
  (Q : Assertion)
  (c : com)
  (b : bexp)
  (WLP : com -> Assertion -> Assertion)
    : Assertion :=
    @GFP state (wlp_one_iter Q c b WLP).

  Fixpoint wlp_gen
           (c : com)
           (Q : Assertion) {struct c} : Assertion :=
    match c with
    | <{skip}> => Q
    | <{ x := a}> => Q [x |-> a]
    | <{ c1; c2 }> => wlp_gen c1 (wlp_gen c2 Q)
    | <{ if b then c1 else c2 end }> =>
      ((b -> wlp_gen c1 Q) /\ (~ b -> wlp_gen c2 Q))%assertion
    | <{while b do c end }> =>
      wlp_while Q c b wlp_gen
    end.

  Lemma wlp_ex_1 : wlp_gen <{skip}> (X = 5) = (X = 5)%assertion.
  Proof. reflexivity. Qed.

  Lemma wlp_ex_2 : wlp_gen <{X := Y + Z}> (X = 5) = (Y + Z = 5)%assertion.
  Proof. reflexivity. Qed.

  Lemma wlp_ex_3 : wlp_gen <{X := Y}> (X = Y) = (Y = Y)%assertion.
  Proof. reflexivity. Qed.

  Lemma wlp_ex_5 : wlp_gen <{X := 5}> (X = 0) = (5 = 0)%assertion.
  Proof. reflexivity. Qed.

  (* In order to reason about the greatest fixpoint of [wlp_one_iter],
     we need to prove that [wlp_gen] is monotone. *)
  Lemma wlp_gen_is_monotone
    : forall (c : com),
      Monotone (wlp_gen c).
  Proof.
    unfold Monotone.
    induction c; simpl; intros; eauto.
    - (* x := a*)
      unfold assn_sub, Subset; eauto.
    - (* if b then c1 else c2 end *)
      unfold assn_sub, Subset in *; intros; eauto.
      In_inversion.
      In_intro; split; intros; eauto.
      eapply IHc1; eauto.
      Hint Unfold In : core.
      eauto.
      eapply IHc2; eauto.
    - (* while b do c end *)
      unfold wlp_while, wlp_one_iter, GFP, FConsistent, Subset in *; intros.
      In_inversion.
      In_intro.
      exists x0.
      split; eauto; intros.
      eapply H0 in H2.
      In_inversion.
      + In_intro; left; split; eauto.
        eapply H; eauto.
      + In_intro; right; split; eauto.
  Qed.

  (* Here's an example of adding the constructors of a datatype to the
     hint database. *)
  Hint Constructors ceval : core.

  Definition wlp_gen' (c : com) (Q : Assertion) : Assertion :=
    fun _ => True.

  Lemma wlp_gen'_is_wlp
    : forall c Q,
      wlp c Q (wlp_gen' c Q).
  Proof.
    simpl.
    unfold wlp, wlp_gen'; simpl.
    eauto.
  Qed.

  (* The assertion produced by [wlp_gen] is always a weakest liberal
     precondition: *)
  Lemma wlp_gen_is_wlp
    : forall c Q,
      wlp c Q (wlp_gen c Q).
  Proof.
    unfold wlp, hoare_triple, "->>".
    intros; assert (forall st', st =[c]=> st' -> Q st') by eauto.
    generalize Q st H1; clear.
    induction c; simpl; intros; eauto.
    - (* if b then c1 else c2 *)
      split; eauto; intros.
      (* Could have used [intuition] instead *)
      eapply IHc2.
      intros; eapply H1; eapply E_IfFalse; eauto.
      eauto using not_true_is_false.
    - unfold wlp_while.
      (* The principle of coinduction allows us to prove that a particular state [st]
         is included in the greatest fixed point.

        To do so, we need to identify an F-Consistent set that includes [st].
        In this case, it will the set of states where:

        a) cause [while b do c end] to loop forever
        b) cause [while b do c end] to terminate in a final state where Q holds

 *)
      eapply CoInd with
          (Ind := fun st =>
                    (forall st' : state, st =[ while b do c end ]=> st' -> Q st')
                    /\ forall (Q : Assertion) (st : state), (forall st' : state, st =[ c ]=> st' -> Q st') ->
                                                            wlp_gen c Q st); eauto.
      unfold FConsistent, Subset, In; simpl; intros.
      destruct H.
      specialize (H1 x).
      destruct (beval x b) eqn: ?.
      + unfold wlp_one_iter; right; eauto 6.
      + unfold wlp_one_iter; left; eauto.
  Qed.

  (* If the guard is true, unrolling one iteration of the loop
     produces an equivalent weakest preondition: *)
  Lemma wlp_unroll_true :
    forall Q c b,
      (wlp_while Q c b wlp_gen /\ b)%assertion ->> wlp_gen <{c; while b do c end}> Q.
  Proof.
    unfold "->>"; simpl; intros; intuition.
    eapply GFP_is_FConsistent in H0; unfold wlp_one_iter, In in *; intuition.
    unfold Monotone, Subset, In; intros; intuition.
    right.
    intuition.
    eapply wlp_gen_is_monotone; eassumption.
  Qed.

  (* If the guard is false, the weakest precondition of the loop is
     the postcondition *)
  Lemma wlp_unroll_false :
    forall Q c b,
      (wlp_while Q c b wlp_gen /\ ~ b)%assertion ->> Q.
  Proof.
    unfold "->>"; simpl; intros; intuition.
    eapply GFP_is_FConsistent in H0; unfold wlp_one_iter, In in *; intuition.
    unfold Monotone, Subset, In; intros. intuition.
    right.
    intuition.
    eapply wlp_gen_is_monotone; eassumption.
  Qed.

  Hint Constructors hoare_proof : core.
  Hint Unfold assert_implies : core.

  (* For all postconditions [Q] and programs [c], we can build a proof
     of  |- {wp_gen c Q} c {Q}. *)
  Theorem wlp_is_derivable  : forall c Q,
       |- {{wlp_gen c Q}} c {{Q}}.
  Proof.
    (* The proof is by induction on c. Most of the cases follow
       immediately from the definition of wlp, which closely follows
       the definition of the proof rules. *)
    induction c; simpl; intros; eauto.
    - (* if *)
      eapply H_If.
      + eapply H_Consequence; eauto.
        unfold "->>"; intuition eauto.
      + eapply H_Consequence; eauto.
        unfold "->>"; intuition eauto.
    -  eapply H_Consequence with (P' := wlp_while Q c b wlp_gen)
                                (Q' := (wlp_while Q c b wlp_gen /\ ~ b)%assertion); auto.
      + eapply H_While.
        eapply H_Consequence with (Q' := wlp_while Q c b wlp_gen); eauto.
        apply wlp_unroll_true.
      + apply wlp_unroll_false.
  Qed.

  (* Let c be a command and let P and Q be assertions such that the
     partial correctness specification {P} c {Q} is valid. *)
  Theorem hoare_proof_complete :
    forall P c Q,
      |= {{P}} c {{Q}} ->
      |- {{P}} c {{Q}}.
  Proof.
    intros.
    (*By [wlp_is_derivable] we have: |- {wp_gen c Q}} c {Q} is provable. *)
    assert (|- {{wlp_gen c Q}} c {{Q}}) by (eauto using wlp_is_derivable).
    (*By [wlp_gen_is_wlp] and the fact that {P} c {Q} is a valid
      triple, then P implies [wp_gen c Q]. *)
    assert (P ->> wlp_gen c Q) by (eapply wlp_gen_is_wlp; eauto).
    (* By combining the rule of consequence with these two facts, the
       proof is immediate! *)
    eapply H_Consequence; eauto.
  Qed.

Ltac verify_assn :=
  repeat split;
  simpl; unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq; [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try lia.

Ltac verify_ht :=
  match goal with
    | |- {{?P}} ?p {{?Q}} =>
    eapply hoare_proof_sound;
    eapply H_Consequence with (Q' := Q);
    [ eapply wlp_is_derivable
      | verify_assn
      | eauto]
  end.

  Definition Hoare_Triple_1 : Prop := {{True}} <{X := 5}> {{X = 5}}.
  Definition Hoare_Triple_2 : Prop := {{X = 2}} <{X := X + 1}> {{X = 3}}.
  Definition Hoare_Triple_3 : Prop := {{True}} <{X := 5; Y := 0}> {{X = 5}}.
  Definition Hoare_Triple_4 : Prop := {{X = 2 /\ X = 3}} <{X := 5}> {{X = 0}}.
  Definition Hoare_Triple_5 : Prop :=
    {{X = 0}}
    <{while X = 0 do X := X + 1 end}>
    {{X = 1}}.

  Lemma Hoare_Triple_ex_1' : Hoare_Triple_1.
  Proof.
    unfold Hoare_Triple_1.
    verify_ht.
  Qed.

  (* And here: *)
  Lemma Hoare_Triple_ex_2' : Hoare_Triple_2.
  Proof.
    unfold Hoare_Triple_2.
    verify_ht.
  Qed.

  (* Here is the if example from class: *)
  Lemma Guarded_update_ex :
  {{True}}
  <{if (X = 0)
    then Y := 2
    else Y := X + 1; Y := Y + 1
    end}>
  {{X <= Y}}.
  Proof.
    verify_ht.
  Qed.

  Definition reduce_to_zero' : com :=
    <{ while ~(X = 0) do
               X := X - 1
               end }>.

  (* Actually proving the wlp for programs with loops amounts to
     figuring out the right invariant! *)
  Theorem reduce_to_zero_correct' :
    {{True}}
      reduce_to_zero'
      {{X = 0}}.
  Proof.
    verify_ht.
    unfold wlp_while.
    eapply CoInd with (Ind := fun _ => True); eauto.
    unfold FConsistent; intros ? ?.
    In_intro.
    unfold wlp_one_iter; intuition.
    simpl.
    destruct ((x X =? 0)) eqn: ?; simpl; intuition.
    left; verify_assn.
  Qed.

End Hoare.
