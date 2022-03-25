(****** Homework 4 for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 04/01/2020 by 6:00PM !!! **)
(* ================================================================= *)
(** ** Instructions for Homework 4 *)

(** Follow the following instructions for Homework 4.
      - The denotational semantics section of this homework requires
        some definitions from [Denotational.v] and [Fixpoints.v], which
        are included with the homework. Before you start working on the
        homework, make sure you build those files by running 'make' in
        this directory.
      - Some IDEs have trouble with the unicode notations in [Fixpoints.v]
        and [Denotational.v]. If you encounter a weird lexer error, please
        download the DenotationalSemantics_no_notations archive from
        Brightspace and replace the copies of these two files in the
        DenotationalSemantics subdirectory with their unicode-free counterparts.
        Note that the only differences between the two files are the notations
        used for set membership (∈) and subset (⊆), and that the choice of
        notations shouldn't affect your solution.

      - Before working on this file, open '_CoqProject' file in the same
        directory and replace the line '-R ../plf PLF' with '-R
        /path/to/your/programming/language/foundations/directory PLF', similar
        to how you did it in previous homework.
      - Alternatively, you may symlink (or move / copy) the plf directory to the
        parent directory of the homework directory. For example, if your
        homework folder is at '/path/to/hw4', you may symlink plf to
        '/path/to/plf'. This way you don't have to change '_CoqProject'.
      - Compile your [Hoare2.v] first according to 'Software Foundations', or
        just run `make` in PLF to compile everything.
      - You are allowed to use axioms from [Maps.v]. Therefore, if you see
        axioms with prefix [Maps.] in the output of [hw4_test.v], it is fine.
      - You shouldn't need axioms from other chapters. If you really want to use
        an exercise from other chapters, please copy it to [hw4.v] and prove it.
      - If you define additional definitions or lemmas, make sure they are
        defined in [hw4.v]. Remember you only hand in [hw4.v].
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

    Each homework (like [hw4.v]) is accompanied by a _test script_
    ([hw4_test.v]). You may want to use them to double-check that your
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
From Coq Require Import Lia.
From PLF Require Export Hoare2.
From PLF Require Export Hoare.
From PLF Require Export Maps.

Module DenotationalSemantics.
(* ================================================================= *)
(* Denotational Semantics        [8 points]                          *)
(* One of the places that denotational semantics tend to shine is when
   proving that two programs are equivalent or that a compiler
   optimization is correct. In this part of the homework you will use
   the denotational semantics for Imp defined in [Denotational.v] to
   prove these sorts of equivalence facts.

   Hint #1: The [In_intro] and [In_inversion] tactics could prove
   useful here. Both tactics will solve the goal if possible; if they
   can't, [In_intro] will transform a goal of the form 'x ∈ S' into an
   equivalent but more readable version, while [In_inversion]
   will simplify /assumptions/ of the form 'x ∈ S'.

   Hint #2: [Denotational.v] has several examples of similar proofs
   [seq_skip_opt, bexp_eqv_example, ...] .  *)

From DS Require Import Fixpoints.
From DS Require Import Denotational.

(** Exercise: 2 points (if_false) *)
(* Use the denotational semantics of commands to show that if the
    condition of an if expression is equivalent to false, the entire
    expression is semantically equivalent to the else branch: *)
Theorem if_false : forall b c1 c2,
    b ==B <{false}> ->
    <{ if b then c1 else c2 end }> ==C c2.
Proof.
  split; intros (?, ?) ?.
  - simpl in H0. In_inversion.
  -- destruct H. simpl in H. apply H in H0. In_inversion.
  -- assumption.
  - simpl. In_intro. right. split.
  -- destruct H. apply H1. simpl. In_intro.
  -- assumption. 
Qed.

(** Exercise: 2 points (swap_if_branches) *)
(* Show that swapping the branches of an [if] and negating its guard
    produces an equivalent expression: *)
Theorem swap_if_branches : forall b c1 c2,
    <{ if b then c1 else c2 end }> ==C <{ if ~ b then c2 else c1 end }>.
Proof.
  split; intros (?, ?) ?; simpl in H; In_inversion; simpl in *; In_intro.
  - right. simpl. split; assumption.
  - left. simpl. split; assumption.
  - right. split; assumption.
  - left. split; assumption.     
Qed.


(** Exercise: 2 points (seq_assoc) *)
(* Prove that a sequence of commands can be reassociated without
   changing its semantics: *)
Theorem seq_assoc :
  forall c1 c2 c3,
    <{(c1; c2); c3}> ==C <{c1; (c2; c3)}>.
Proof.
  split; intros (?, ?) ?; simpl in *; In_inversion; In_intro; exists x0; split.
  - assumption.
  - exists x. split; assumption.
  - exists x. split; assumption.
  - assumption.
Qed.

(* Here is the higher-order boolean expression optimizer from the
   midterm.  It takes an arithmetic expression optimizer [a_opt] and
   applies it to /all/ arithemetic subterms of a boolean
   expression. *)

Fixpoint b_opt (a_opt : aexp -> aexp) (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{a1 = a2}> => <{a_opt a1 = a_opt a2}>
  | <{a1 <= a2}> => <{a_opt a1 <= a_opt a2}>
  | <{~ b}> => <{~ (b_opt a_opt b)}>
  | <{b1 && b2}> => <{b_opt a_opt b1 && b_opt a_opt b2}>
  end.

(** Exercise: 2 points (b_opt_sound) *)

(* Show that when given a correct arithmetic expression optimizer,
   [b_opt] is semantics preserving with respect to the denotational
   semantics of boolean expressions.

   You may find the congruence lemmas for boolean expressions
   [beq_eqv_cong, ble_eqv_cong] from Denotational.v particularly
   helpful here.  *)
Lemma b_opt_sound
  : forall a_opt,
    (forall (a : aexp), a ==A a_opt a) ->
    forall (b : bexp), b ==B b_opt a_opt b.
Proof.
  intros.
  split; induction b; intros (?, ?) ?.
  - assumption.
  - assumption.
  - apply (beq_eqv_cong a1) with (x:=a2) (y:=a_opt a1) in H; apply H.
    assumption.
  - apply (ble_eqv_cong a1) with (x:=a2) (y:=a_opt a1) in H; apply H.
    assumption.
  - apply IHb. assumption.
  - simpl in *. In_inversion. subst. exists x. exists x0. split.
  -- apply IHb1 in H0. assumption.
  -- split.
  --- apply IHb2 in H1. assumption.
  --- reflexivity.
  - assumption.
  - assumption.
  - apply (beq_eqv_cong a1) with (x:=a2) (y:=a_opt a1) in H; apply H.
    assumption.
  - apply (ble_eqv_cong a1) with (x:=a2) (y:=a_opt a1) in H; apply H.
    assumption.
  - apply IHb. assumption.
  - simpl in *. In_inversion. subst. exists x. exists x0. split.
  -- apply IHb1 in H0. assumption.
  -- split.
  --- apply IHb2 in H1. assumption.
  --- reflexivity.
Qed.

End DenotationalSemantics.

(* ================================================================= *)
(* Axiomatic Semantics        [12 points]                            *)

(** Exercise: 1 point (hoare_asgn_example)  *)
(** Translate this "decorated program" into a formal proof
    in Coq.

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X := 1;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y := 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example :
  {{ True }}
  <{X := 1; Y := 2}>
  {{ X = 1 /\ Y = 2 }}.
Proof.
  apply hoare_seq with (Q := (X = 1)%assertion).
  (* The annotation [%assertion] is needed here to help Coq parse correctly. *)
  - eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- assn_auto.
  - eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- assn_auto.
Qed.

(** Exercise: 3 points (swap_exercise)  *)
(** Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:

      {{X <= Y}} c {{Y <= X}}
*)

Definition swap_program : com :=
  <{Z := X; X := Y; Y := Z}>.

Theorem swap_exercise :
  {{X <= Y}}
  swap_program
  {{Y <= X}}.
  Proof.
  - eapply hoare_seq.
  -- eapply hoare_seq.
  --- apply hoare_asgn.
  --- apply hoare_asgn.
  -- eapply hoare_consequence_pre.
  --- apply hoare_asgn.
  --- assn_auto.
Qed.

(* ================================================================= *)
(** ** Exercise: Parity *)

(** Here is a cute little program for computing the parity of the
    value initially stored in [X].

         {{ X = m }}
       WHILE 2 <= X DO
         X ::= X - 2
       END
         {{ X = parity m }}

    The mathematical [parity] function used in the specification is
    defined in Coq as follows: *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

(** The postcondition does not hold at the beginning of the loop,
    since [m = parity m] does not hold for an arbitrary [m], so we
    cannot use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  On each iteration it
    decrements [X] by [2], which preserves the parity of [X].  So the
    parity of [X] does not change, i.e., it is invariant.  The initial
    value of [X] is [m], so the parity of [X] is always equal to the
    parity of [m]. Using [parity X = parity m] as an invariant we
    obtain the following decorated program:

        {{ X = m }} ->>                              (a - OK)
        {{ parity X = parity m }}
      WHILE 2 <= X DO
          {{ parity X = parity m /\ 2 <= X }}  ->>    (c - OK)
          {{ parity (X-2) = parity m }}
        X ::= X - 2
          {{ parity X = parity m }}
      END
        {{ parity X = parity m /\ X < 2 }}  ->>       (b - OK)
        {{ X = parity m }}


    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)


(** Exercise: 3 points (parity_correct) *)
(** Translate this proof to Coq. Refer to the reduce-to-zero example
    from Hoare2.v for ideas.  Remember that you may have to use [ap] when
    including a Coq function in an assertion.

    You may find the following two lemmas useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- Minus.minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    exfalso. apply H. lia.
Qed.

From Coq Require Import Arith.Compare_dec.

Theorem parity_correct :
  forall (m : nat),
  {{ X = m }}
  while 2 <= X do
    X := X - 2
  end
  {{X = parity m}}.
Proof.
  intros.
  eapply hoare_consequence with (P' := (ap parity X = parity m)%assertion).
  - apply hoare_while.
    eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- verify_assn.
     rewrite <- H.
     apply parity_ge_2.
     apply leb_complete. assumption.
  - verify_assn.
  - verify_assn.
    rewrite <- H.
    symmetry.
    apply parity_lt_2.
    unfold not.
    intros.
    apply leb_correct in H1.
    simpl in H1.
    rewrite H0 in H1.
    discriminate H1.
Qed.

(* ================================================================= *)
(** ** Exercise: Factorial *)

(** Recall that [n!] denotes the factorial of [n] (i.e., [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:

    {{ X = m }}
  Y := 1 ;
  while X <> 0
  do
     Y := Y * X ;
     X := X - 1
  end
    {{ Y = m! }}


    Complete the proof in [factorial_correct] showing that this is a correct
    implementation of the factorial function.  Filling in the blanks in
    the following decorated program may help you complete this proof.

    {{ X = m }} ->>
    {{ 1 * X! = m! }}
  Y := 1;
    {{ Y * X! = m! }}
  while X <> 0
  do   {{ Y * X! = m! /\ X <> 0 }} ->>
       {{ (Y * X) * (X - 1)! = m! }}
     Y := Y * X;
       {{ Y * (X - 1)! = m! }}
     X := X - 1
       {{ Y * X! = m! }}
  end
    {{ Y * X! = m! /\ X = 0 }} ->>
    {{ Y = m! }}
*)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Lemma real_fact_neq_0 :
  forall n,
    n <> 0
    -> real_fact n = n * real_fact (n - 1).
Proof.
  induction n; simpl; intros; try congruence.
  rewrite <- Minus.minus_n_O.
  reflexivity.
Qed.

(** Exercise: 5 points (factorial_correct)  *)
Theorem factorial_correct : forall (m : nat),
    {{ X = m }}
      <{Y := 1;
  while ~ (X = 0) do
    Y := Y * X;
    X := X - 1
  end }>
    {{ fun st => st Y = real_fact m }}.
Proof.
  intros.
  eapply hoare_seq with (Q := (Y * (ap real_fact X) = real_fact m)%assertion).
  - eapply hoare_consequence_post.
  -- apply hoare_while.
     eapply hoare_consequence_pre.
  --- eapply hoare_seq.
  ---- apply hoare_asgn.
  ---- apply hoare_asgn.
  --- verify_assn.
      apply real_fact_neq_0 in H0.
      lia.
  -- verify_assn.
     simpl in H.
     lia.
  - eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- verify_assn.
Qed.
