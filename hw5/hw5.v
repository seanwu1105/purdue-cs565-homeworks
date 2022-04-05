(****** Homework 5 for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 04/15/2022 by 6:00PM !!! **)
(* ================================================================= *)
(** ** Instructions for Homework 5 *)

(** Follow the following instructions for Homework 5.
      - Before working on this file, open '_CoqProject' file in the same
        directory and replace the line '-R ../plf PLF' with '-R
        /path/to/your/programming/language/foundations/directory PLF', similar
        to how you did it in previous homework.
      - Alternatively, you may symlink (or move / copy) the plf directory to the
        parent directory of the homework directory. For example, if your
        homework folder is at '/path/to/hw5', you may symlink plf to
        '/path/to/plf'. This way you don't have to change '_CoqProject'.
      - Compile your [Smallstep.v] first according to 'Software Foundations', or
        just run `make` in PLF to compile everything.
      - You are allowed to use axioms from [Maps.v]. Therefore, if you see
        axioms with prefix [Maps.] in the output of [hw5_test.v], it is fine.
      - You shouldn't need axioms from other chapters. If you really want to use
        an exercise from other chapters, please copy it to [hw5.v] and prove it.
      - If you define additional definitions or lemmas, make sure they are
        defined in [hw5.v]. Remember you only hand in [hw5.v].
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

    Each homework (like [hw5.v]) is accompanied by a _test script_
    ([hw5_test.v]). You may want to use them to double-check that your
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
    versions of this assignment, you may notice that they are given
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
From Top Require Import ISA.

(***************************************************************************
  Part 1: Program Logics     [17 points]
 ***************************************************************************)

(* In the first part of this assignment, you'll be developing a Hoare
   Logic for our simple ISA from the first homework.

   The syntax and semantics of our ISA can be found in ISA.v; they
   are almost identical to the definitions from the first homework. *)

Module ISASemantics.

  (* To reason about the correctness of programs in our simple ISA
     language, we will use the recipe from the lectures:

     Step 1: Define a language of claims
     Step 2: Define a set of rules (axioms) to build proofs of claims
     Step 3: Verify specific programs *)

  (* Step 1A: Define a language of assertions (claims on program
     states).

    Following Hoare.v, our assertion language will simply use Prop to
    make claims on program states: *)

  Definition Assertion := MachineState -> Prop.
  (* Here is how we can claim that the value in ax is less than the
     value of bx in the current state *)
  Definition assert_ex_1 : Assertion := fun st => getReg ax st < getReg cx st.
  (* Here is how we can claim that the conditional flag is set to true: *)
  Definition assert_ex_2 : Assertion := fun st => getFlag st = true.
  (* And here are a couple examples of these assertions in action. *)
  Example assert_ex_1_ex : assert_ex_1 (MState 0 3 4 true).
  Proof. unfold assert_ex_1; simpl. lia. Qed.
  Example assert_ex_2_ex : assert_ex_2 (MState 0 3 4 true).
  Proof. unfold assert_ex_2; reflexivity. Qed.

  (** Exercise: 1 point (assert_ex_3) *)
  (* Write an assertion that claims that the conditional flag records
     whether dx is less than cx. *)
  Definition assert_ex_3 : Assertion := fun st => getReg dx st <? getReg cx st = getFlag st.
  Example assert_ex_3_ex : assert_ex_3 (MState 0 3 4 false).
  Proof.
    unfold assert_ex_3. 
    auto.
  Qed.

  (* Step 1B: Define a language of claims about programs (Basic Blocks
     in this setting): *)
  Definition BB_triple (P : Assertion) (p : BasicBlock) (Q : Assertion) : Prop :=
    forall st,
      P st ->
      forall st',
        BasicBlock_evalR st p st' ->
        Q st'.

  Notation "{{ P }}  p  {{ Q }}" :=
    (BB_triple P p Q)
      (at level 90, p at level 99).

  (* These are technically claims about partial correctness, but since
     our basic blocks don't loops or recursion, they always terminate. *)

  (* We could formalize the various claims about programs from the
     first lecture, and then prove they are valid using the semantics
     of basic blocks directly: *)
  Theorem evalAddFlagID :
    forall (src : Operand) (dest : Register) (f : bool),
      {{fun st => getFlag st = f}} [add src dest] {{fun st => getFlag st = f}}.
  Proof.
    unfold BB_triple; intros.
    inversion H0; inversion H4; inversion H6; subst.
    - destruct st; destruct r1; destruct dest; simpl; reflexivity.
    - destruct st; destruct dest; simpl; reflexivity.
  Qed.

  Theorem evalCsetOK :
    forall (src : Operand) (dest : Register)
           (P : Assertion),
      {{fun st => P st /\ getFlag st = false}} [cset src dest] {{P}}.
  Proof.
    unfold BB_triple; intros.
    inversion H0; inversion H4; inversion H6; subst; intuition eauto.
    - destruct st; destruct r1; destruct dest; simpl; intuition; congruence.
    - destruct st; destruct dest; simpl; intuition; congruence.
  Qed.

  Definition asmSwapAC : BasicBlock :=
  [cmp (imm 0) (imm 0);
   cset (reg cx) dx;
   cset (reg ax) cx;
   cset (reg dx) ax].

  Theorem asmSwapACOK :
    forall m n,
      {{fun st => getReg ax st = m /\ getReg cx st = n}}
        asmSwapAC
        {{fun st => getReg ax st = n /\ getReg cx st = m}}.
  Proof.
    unfold BB_triple; intros.
    repeat match goal with
             H : BasicBlock_evalR _ _ _ |- _ => inversion H; subst; clear H
           | H : Instr_evalR _ _ _ |- _ => inversion H; subst; clear H
           end; destruct st; simpl in *; intuition eauto; try discriminate.
  Qed.

  Definition asmTriple : BasicBlock :=
    [cmp (imm 0) (imm 0);
    cset (reg ax) cx;
    add (reg cx) ax;
    add (reg cx) ax].

  Theorem asmTripleAxOK :
    forall m,
      {{fun st => getReg ax st = m}} asmTriple {{fun st => getReg ax st = 3 * m}}.
  Proof.
    unfold BB_triple; intros.
    repeat match goal with
             H : BasicBlock_evalR _ _ _ |- _ => inversion H; subst; clear H
           | H : Instr_evalR _ _ _ |- _ => inversion H; subst; clear H
           end; destruct st; simpl in *; intuition eauto; try discriminate.
  Qed.

  (* But that's no fun! Instead, let's proceed to Step 2 of our recipe. *)

  Reserved Notation " |- {{ P }}  p  {{ Q }}"
           (at level 40, p at next level).

  Reserved Notation " |-I {{ P }}  p  {{ Q }}"
           (at level 40, p at next level).

  (* Here are a subset of the inference rules for instructions:

     ------------------------------------------------------------------ [H_AddReg]
      |-I {{[r2 := r1 + r2]Q }} (add (reg r1) r2) {{Q}}

     ------------------------------------------------------------------ [H_AddImm]
      |-I {{[r2 := n + r2]Q}} (add (imm n) r2) {{Q}}

    ----------------------------------------------------------------------- [HCmpRegReg]
      |-I {{[flag := r1 =? r2]Q}} (cmp (reg r1) (reg r2)) {{Q}}

    ----------------------------------------------------------------------- [HCSetImm]
    |-I {{(flag -> [r2 := n]Q) /\ (~ flag -> Q )}} (cset (imm n) r2) {{Q}} *)

  (* Here are the rules for individual instructions. Note that most
     are very similar to [H_Asgn], the rule for assignment in our
     hoare logic for Imp. *)

  Inductive Instr_proof : Assertion -> Instr -> Assertion -> Prop :=
  | H_AddReg : forall (r1 r2 : Register) (Q : Assertion),
      |-I {{fun st => Q (setReg r2 (getReg r1 st + getReg r2 st) st) }}
           (add (reg r1) r2) {{Q}}
  | H_AddImm : forall (n : nat) (r2 : Register) (Q : Assertion),
      |-I {{fun st => Q (setReg r2 (n + getReg r2 st) st)}}
           (add (imm n) r2)
           {{Q}}

  | H_IncReg : forall (r : Register) (Q : Assertion),
      |-I {{fun st => Q (setReg r (1 + getReg r st) st)}} (inc r) {{Q}}

  | H_CmpRegReg : forall (r1 r2 : Register) (Q : Assertion),
      |-I {{fun st => Q (setFlag (eqb (getReg r1 st) (getReg r2 st)) st)}}
          (cmp (reg r1) (reg r2))  {{Q}}
  | H_CmpRegImm : forall (r1 : Register) (n : nat) (Q: Assertion),
      |-I {{fun st => Q (setFlag (eqb (getReg r1 st) n) st)}}
           (cmp (reg r1) (imm n)) {{Q}}
  | H_CmpImmReg : forall (n : nat) (r2 : Register) (Q: Assertion),
      |-I {{fun st => Q (setFlag (eqb n (getReg r2 st)) st)}}
          (cmp (imm n) (reg r2)) {{Q}}
  | H_CmpImmImm : forall (n m: nat) (Q: Assertion),
      |-I {{fun st => Q (setFlag (eqb n m) st)}}
          (cmp (imm n) (imm m)) {{Q}}

  | H_CSetReg : forall (r1 r2 : Register) (Q: Assertion),
      |-I {{fun st => (getFlag st = true -> Q ((setReg r2 (getReg r1 st) st)))
                      /\ (getFlag st = false -> Q st)}}
          (cset (reg r1) r2) {{Q}}

  | H_CSetImm : forall (n : nat) (r2 : Register) (Q: Assertion),
      |-I {{fun st => (getFlag st = true -> Q ((setReg r2 n st)))
                      /\ (getFlag st = false -> Q st)}}
          (cset (imm n) r2) {{Q}}

  where " |-I {{ P }}  i  {{ Q }}" := (Instr_proof P i Q).

  Definition assert_implies (P Q : Assertion) : Prop :=
    forall st, P st -> Q st.

  Notation "P ->> Q" := (assert_implies P Q) (at level 80).

  (* The inference rules for basic blocks roughly correspond to [H_Skip], [H_Seq],
     and [H_Consequence]:

     |-I {{P}} i {{R}}         |- {{R}} p {{Q}}
     ------------------------------------------------------------------ [H_Seq]
      |- {{P}} i; p {{Q}}

     ------------------------------------------------------------------ [H_End]
      |- {{P}} [ ] {{P}}

      |- {{P'}} p {{Q'}}   P ->> P'       Q' ->> Q
     ------------------------------------------------------------------ [H_Consequence]
     |- {{P}} p {{Q}}
*)

  (** Exercise: 1 point (BB_proof) *)
  (* Formalize these rules as an inductive proposition *)
  Inductive BB_proof : Assertion -> BasicBlock -> Assertion -> Prop :=
  | H_End : forall (P : Assertion),
      |- {{P}} [ ] {{P}}
  | H_Seq : forall (P Q R : Assertion) (i : Instr) (p : BasicBlock),
      |-I {{P}} i {{R}} -> |- {{R}} p {{Q}} -> |- {{P}} i :: p {{Q}}
  | H_Consequence : forall (P P' Q Q' : Assertion) (p : BasicBlock),
      |- {{P'}} p {{Q'}} -> P ->> P' -> Q' ->> Q -> |- {{P}} p {{Q}}
  where " |- {{ P }}  p  {{ Q }}" := (BB_proof P p Q).

  (* Exercise: 3 points (BB_proof_sound)*)
  (* Prove that this logic is sound, i.e. it can only be
     used to prove only semantically valid triples. *)
  Lemma BB_proof_sound :
    forall (P : Assertion) (p : BasicBlock) (Q : Assertion),
      |- {{P}} p {{Q}} ->
      {{P}} p {{Q}}.
  Proof.
    intros.
    induction H; unfold BB_triple; intros.
    - inversion H0. subst. assumption.
    - inversion H2. apply (IHBB_proof ms').
    -- induction H; inversion H6; subst; try (apply H1); assumption.
    -- assumption.
    - apply H1. apply (IHBB_proof st).
    -- apply H0. assumption.
    -- assumption. 
  Qed.

  (* To prove completeness, we first define a function for computing the weakest preconditions
     of instructions: *)
  Definition wlp_Instr_gen (i : Instr) (Q: Assertion) : Assertion :=
    match i with
    | add (reg r1) r2 => fun st => Q (setReg r2 (getReg r1 st + getReg r2 st) st)
    | add (imm n) r2 => fun st => Q (setReg r2 (n + getReg r2 st) st)
    | inc r => fun st => Q (setReg r (1 + getReg r st) st)

    | cmp (reg r1) (reg r2) =>
      fun st => Q (setFlag (eqb (getReg r1 st) (getReg r2 st)) st)
    | cmp (reg r1) (imm n) =>
      fun st => Q (setFlag (eqb (getReg r1 st) n) st)
    | cmp (imm n) (reg r2) =>
      fun st => Q (setFlag (eqb n (getReg r2 st)) st)
    | cmp (imm n) (imm m) => fun st => Q (setFlag (eqb n m) st)

    | cset (reg r1) r2 => fun st => (getFlag st = true -> Q ((setReg r2 (getReg r1 st) st)))
                                    /\ (getFlag st = false -> Q st)
    | cset (imm n) r2 => fun st => (getFlag st = true -> Q ((setReg r2 n st)))
                                   /\ (getFlag st = false -> Q st)
    end.

  Definition wlp_Instr (i : Instr)
             (Q : Assertion)
             (P : Assertion)
    : Prop := forall (P' : Assertion),
      (forall st, P' st -> forall st', Instr_evalR st i st' -> Q st')
      -> (P' ->> P).

  (* Following the script from [HoarePartial.v] We can show that [wlp_Instr_gen]
     does, in fact, generate the weakest precondition: *)
  Lemma wlp_Instr_gen_is_wlp_Instr
    : forall i Q,
      wlp_Instr i Q (wlp_Instr_gen i Q).
  Proof.
    unfold wlp_Instr, "->>"; destruct i; simpl; intros; specialize (H st H0).
    - destruct src; destruct dest; destruct st; simpl; eapply H; econstructor.
    - destruct dest; destruct st; simpl; eapply H; econstructor.
    - destruct src; destruct dest; destruct st; simpl; eapply H; econstructor.
    - destruct src; destruct dest; destruct st; intuition; intros;
        eapply H; econstructor; eauto.
  Qed.

  Theorem wlp_Instr_is_derivable  : forall i Q,
       |-I {{wlp_Instr_gen i Q}} i {{Q}}.
  Proof.
    induction i; simpl; intros.
    - destruct src; simpl; econstructor.
    - econstructor.
    - destruct src; destruct dest; econstructor.
    - destruct src; econstructor; eauto.
  Qed.

  (* Exercise: 3 points (wlp_gen) *)
  (* Definite a function that calculates the weakest precondition for
     a basic block:

     Hint: Basic Blocks are very similar to sequences of Imp commands
     follow by skip. *)
  Fixpoint wlp_gen (p : BasicBlock) (Q : Assertion) {struct p} : Assertion := 
    match p with
    | [ ] => Q
    | i :: p' => wlp_Instr_gen i (wlp_gen p' Q)
    end.

  Definition wlp
             (p : BasicBlock)
             (Q : Assertion)
             (P : Assertion)
    : Prop := forall (P' : Assertion),
      {{P'}} p {{Q}}
      -> (P' ->> P).

  (* Exercise: 3 points (wlp_gen_is_wlp):

     Show that [wlp_gen] computes an assertion which is weaker than
     every other valid assertion: *)
  Lemma wlp_gen_is_wlp
    : forall p Q,
      wlp p Q (wlp_gen p Q).
  Proof.
    unfold wlp, "->>". induction p.
    - intros. apply H in H0. specialize (H0 st). apply H0. apply E_Done.
    - intros. induction a.
    -- destruct src.
    --- eapply IHp.
  Admitted.

  (* Exercise: 3 points (wlp_gen_is_derivable) *)

  (* Show that our Hoare logic can always construct evidence of a
  claim built from [wlp_gen]: *)
  Theorem wlp_is_derivable  : forall p Q,
       |- {{wlp_gen p Q}} p {{Q}}.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (* Exercise: 2 points (BB_proof_complete) *)

  (* Now use these two facts to prove that our logic is complete: it
     can construct evidence of every valid claim.

    If you are unable to prove the previous two lemmas, you can admit
    them and use them here without penalty (on this question). *)
  Theorem BB_proof_complete :
    forall P p Q,
      {{P}} p {{Q}} ->
      |- {{P}} p {{Q}}.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  Ltac verify_assn :=
    unfold "->>"; simpl; intros;
    repeat match goal with
             st : MachineState |- _ => destruct st; simpl
           | r : Register |- _ => destruct r; simpl
           | |- context[match ?s with | _ => _ end]  =>
             destruct s
           end;
    simpl in *;
    intuition eauto;
    try congruence;
    try lia.

  Ltac verify_ht :=
    match goal with
    | |- {{?P}} ?p {{?Q}} =>
      eapply BB_proof_sound;
      (* UNCOMMENT THE FOLLOWING LINE ONCE YOU COMPLETE THE DEFINITION OF BB_proof. *)
      (* eapply H_Consequence with (Q' := Q);*)
      [ eapply wlp_is_derivable
      | verify_assn
      | verify_assn]
    end.

  (* Exercise: (1 point) (verify_ht_ex) *)
  (* As we saw in the lab on 10/29, we can also use these facts to
     automatically verify various claims. *)
  Theorem evalAddFlagID' :
    forall (src : Operand) (dest : Register) (f : bool),
      {{fun st => getFlag st = f}} [add src dest] {{fun st => getFlag st = f}}.
  Proof.
    (* UNCOMMENT THE FOLLOWING TWO LINES *)
    (* intros; verify_ht.
       Qed. *)
  Admitted.

  Theorem evalCsetOK' :
    forall (src : Operand) (dest : Register)
           (P : Assertion),
      {{fun st => P st /\ getFlag st = false}} [cset src dest] {{P}}.
  Proof.
    (* UNCOMMENT THE FOLLOWING TWO LINES *)
    (* intros; verify_ht.
       Qed. *)
  Admitted.

  Theorem asmSwapACOK' :
    forall m n,
      {{fun st => getReg ax st = m /\ getReg cx st = n}}
        asmSwapAC
        {{fun st => getReg ax st = n /\ getReg cx st = m}}.
  Proof.
    (* UNCOMMENT THE FOLLOWING TWO LINES *)
    (* intros; verify_ht.
       Qed. *)
  Admitted.

  Theorem asmTripleAxOK' :
    forall m,
      {{fun st => getReg ax st = m}} asmTriple {{fun st => getReg ax st = 3 * m}}.
  Proof.
    (* UNCOMMENT THE FOLLOWING TWO LINES *)
  (* intros; verify_ht.
     Qed. *)
  Admitted.

End ISASemantics.
