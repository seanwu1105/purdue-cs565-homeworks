(****** Homework 3 for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 2/25/2022 by 6:00PM !!! **)
(* ================================================================= *)
(** ** Instructions for Homework 3 *)

(** Follow the following instructions for homework 3.
      - Before working on this homework, please open '_CoqProject' file
        in the same directory and replace the line '-R lf LF' with
        '-R /path/to/your/logical_foundations/directory LF'. For example,
        if your [Logic.v] resides in '/home/myname/lf', then replace that
        line with '-R /home/myname/lf LF'. If your path contains whitespaces,
        double-quote it, e.g., '-R "/home/first last/lf" lf'.
      - Alternatively, you may symlink (or move / copy) the lf directory
        to the parent directory of the homework directory. For example,
        if your homework folder is at '/path/to/hw3', you may symlink lf
        to '/path/to/lf'. This way you don't have to change '_CoqProject'.
      - Compile your [Imp.v] first according to 'Software Foundations'.
      - You are allowed to use all theorems and exercises in
        'Software Foundations' up to chapter [Imp.v] (regardless of whether
        they are proved or not). But do not use the exercises of the
        same statement. For example, you are not allowed to use the exercise
        [and_assoc] in [Logic.v] to prove the exercise [and_assoc].
      - To make the last point more clear, if you see axioms in the output of
        [hw3_test.v], as long as those axioms are exercises in
        [Software Foundations] up to [Imp.v], they are allowed.
      - If you define additional definitions or lemmas, make sure they are
        defined in [hw3.v]. Remember you only hand in [hw3.v] and [hw3.pdf].
      - This assignment also includes a set of pen and paper exercises;
        you should submit a completed [hw3.pdf] on Brightspace. We have included
        the LaTex sources for this document so that you can typeset this pdf;
        it's also fine to submit a scan of handwritten solutions.
      - There is no extra credit for solving the optional exercises at the
        end of this homework. Try solve them if you want some challenges.
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

    Each homework (like [hw3.v]) is accompanied by a _test script_
    ([hw3_test.v]). You may want to use them to double-check that your
    file is well-formed before handing it in by running the 'make' command.

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
        graded. *)

 (* Note that you should submit *both* a completed version of this
    file [hw3.v] and your solutions to the pen and paper exercises as
    a pdf [hw3.pdf].

    We are using Brightspace for submission. If you submit multiple
    versions of the assignment, you may notice that they are given
    different names.  This is fine: The most recent submission is the
    one that will be graded. *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Imp.
From LF Require Import Maps.
From Coq Require Export Nat (* For natural number comparision operators. *)
     List.
Import List.ListNotations.

(* ================================================================= *)
(* Induction on Evidence *)
(* In the fourth lab session, we saw how to use [induction] on
   evidence to prove a goal. The tactic applies the same reasoning as
   with inductively defined data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question. *)

(* Recall the definition of even from IndProp. *)
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)
Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the original
    one.  Hint: In the proof of the "only if" case, it may be helpful
    to use the [apply ... with (... := ...) tactic to explicitly
    supply the arguments to one of the constructor of ev'.

    Hint: It may be helpful to use your proof of ev_sum from the last
    homework, feel free to copy it here.  *)

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [|n' Hn IH].
  - (* ev_0 *) simpl. apply Hm.
  - (* ev_SS *) simpl. apply ev_SS. apply IH.
Qed.

(** Exercise: 1 point (ev'_ev) *)
Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros.
  unfold iff.
  split.
  - intros. induction H.
  -- constructor.
  -- repeat constructor.
  -- apply ev_sum; assumption.
  - intros. induction H.
  -- constructor.
  -- apply (ev'_sum 2 n).
  --- constructor.
  --- assumption.
Qed.

(** Exercise: 1 point (ev_ev__ev) *)
(* Prove that whenever the sum of two numbers is even, if the first
   operand is even, so is the second.
   Hint: There are two pieces of evidence you could attempt to induct upon
    here. If one doesn't work, try the other. *)
Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros.
  induction H0.
  - assumption.
  - apply IHev. inversion H. assumption.
Qed.

(* A palindrome is a word or sequence that reads the same backward as
   forward, e.g. [1;3;4;4;3;1] or [1;2;2;1]. Here's a set of inference
   rules formalizing when a list of numbers is a palindrome :*)

(* ================
   IsPalindrome [ ]

          IsPalindrome l
   =============================
   IsPalindrome ([n] ++ l ++ [n])
*)

(* Note that under this definition a list with an odd number of
   elements is not a palindrome, but that's okay.
   Here's the corresponding definition of palindromes in Coq:
*)
Open Scope list_scope.
Inductive IsPalindrome : list nat -> Prop :=
| PalindromeEmpty : IsPalindrome [ ]
| PalindromeDouble : forall (n : nat) (l : list nat),
    IsPalindrome l ->
    IsPalindrome ([n] ++ l ++ [n]).

(* We could also define palindromes in terms of list append and
   reverse: *)
Definition IsPalindrome' (l : list nat) : Prop :=
  exists l', l = l' ++ rev l'.

(** Exercise: 1 point (IsPalindrome_equiv) *)
(* Prove that the inductive definition of palindromes implies the
   definition one. *)
Lemma IsPalindrome_equiv : forall l,
    IsPalindrome l -> IsPalindrome' l.
Proof.
  intros.
  induction H; unfold IsPalindrome'.
  - exists [].
    reflexivity.
  - inversion IHIsPalindrome.
    rewrite H0.
    exists ([n] ++ x).
    rewrite <- app_assoc.
    reflexivity.
Qed.

(* ================================================================= *)
(* Big-Step Semantics *)
(* In the lecture on simple extensions to IMP, we discussed how to add
   nondeterministic choice to the language. For this part of the
   homework, you will model this extension in Coq. *)

(* Before completing the rest of the exercises in this file, it may be
   a good time to finish the exercises on the pen and paper portion of
   the assignment, which you can find in Pen+Paper/hw3.pdf. *)

Module ImpPlusFlip.
  Inductive com : Type :=
  | IfFlip (c : com) (* <--- Nondeterministic Execution. *)
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

  (* Notations for our language. See [Imp.v] for more usages of these notations. *)
  Notation "'flip' c 'end'" :=
    (IfFlip c) (in custom com at level 89, c at level 99) : com_scope.
  Notation "'skip'"  :=
    CSkip (in custom com at level 0) : com_scope.
  Notation "x := y"  :=
    (CAss x y)
      (in custom com at level 0, x constr at level 0,
          y at level 85, no associativity) : com_scope.
  Notation "x ; y" :=
    (CSeq x y)
      (in custom com at level 90, right associativity) : com_scope.
  Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
      (in custom com at level 89, x at level 99,
          y at level 99, z at level 99) : com_scope.
  Notation "'while' x 'do' y 'end'" :=
    (CWhile x y)
      (in custom com at level 89, x at level 99, y at level 99) : com_scope.

  (* The program from the 'Extending Imp' quiz can be embedded as a
     command: *)
  Example p1 : com :=
    <{ X := 2;
       Y := 6;
       flip (X := 4) end;
       if X = 2
         then flip (Y := X) end
         else Y := 3
       end }>.

  (** Exercise: 1 point (ImpPlusFlip ceval) *)
  (* Extend the semantics of Imp with the evaluation rules for
     nondeterministic choice from the lecture on 'Extending Imp': *)
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
  | E_FlipTrue : forall st st' c,
      st  =[ c ]=> st' ->
      st  =[ flip c end ]=> st'
  | E_FlipFalse : forall st c,
      st  =[ flip c end ]=> st
  where "st =[ c ]=> st'" := (ceval c st st').

  (** **** Exercise: 2 point (p1_NN, p1_Y, p1_NY) *)
  (* Show that your new rules permit [p1] to evaluate to each of the
     valid states from the quiz: *)
  Example p1_NN : forall sigma,
      sigma =[ p1 ]=> (Y !-> 6; X !-> 2; sigma).
  Proof.
    intros. unfold p1.
    apply E_Seq with (st':=(X !-> 2; sigma)).
    apply E_Ass. reflexivity.
    apply E_Seq with (st':=(Y !-> 6; X !-> 2; sigma)).
    apply E_Ass. reflexivity.
    apply E_Seq with (st':=(Y !-> 6; X !-> 2; sigma)).
    apply E_FlipFalse.
    apply E_IfTrue. reflexivity.
    apply E_FlipFalse.
  Qed.

  Example p1_Y : forall sigma,
      sigma =[ p1 ]=> (Y !-> 3; X !-> 4; Y !-> 6; X !-> 2; sigma).
  Proof.
    intros. unfold p1.
    apply E_Seq with (st':=(X !-> 2; sigma)).
    apply E_Ass. reflexivity.
    apply E_Seq with (st':=(Y !-> 6; X !-> 2; sigma)).
    apply E_Ass. reflexivity.
    apply E_Seq with (st':=(X !-> 4; Y !-> 6; X !-> 2; sigma)).
    apply E_FlipTrue.
    apply E_Ass. reflexivity.
    apply E_IfFalse. reflexivity.
    apply E_Ass. reflexivity.
  Qed.

  Example p1_NY : forall sigma,
      sigma =[ p1 ]=> (Y !-> 2; Y !-> 6; X !-> 2; sigma).
  Proof.
    intros. unfold p1.
    apply E_Seq with (st':=(X !-> 2; sigma)).
    apply E_Ass. reflexivity.
    apply E_Seq with (st':=(Y !-> 6; X !-> 2; sigma)).
    apply E_Ass. reflexivity.
    apply E_Seq with (st':=(Y !-> 6; X !-> 2; sigma)).
    apply E_FlipFalse.
    apply E_IfTrue. reflexivity.
    apply E_FlipTrue.
    apply E_Ass. reflexivity.
  Qed.

  (* OPTIONAL EXERCISE: *)
  (* Just for fun, try to show that the definition of ceval does not
     permit [p1] to evaluate to the invalid state from the 'Extending
     Imp' quiz: *)
  Example p1_Not : forall sigma,
      ~ (sigma =[ p1 ]=> (X !-> 4; Y !-> 6; X !-> 2; sigma)).
  Proof.
    (* FILL IN HERE, IF YOU WANT *)
  Admitted.

  (* This is a helper lemma for the next exercise: *)
  Lemma empty_neq_update
    : forall X v,
      v <> 0 ->
      (X !-> v; empty_st) <> (empty_st).
  Proof.
    unfold not; intros.
    apply H.
    assert ((X !-> v; empty_st) X = empty_st X).
    { rewrite H0. reflexivity. }
    rewrite t_update_eq in H1. rewrite H1. reflexivity.
  Qed.

  (** **** Exercise: 2 point (ceval_is_nondeterministic) *)
  (* Prove that the semantics of Imp+Flip are nondeterministic,
     i.e. that there exists a Imp+Flip program that evaluates to
     distinct final states from the same initial state. *)
  Lemma ceval_is_nondeterministic :
    exists sigmaI sigmaF1 sigmaF2 c,
      sigmaI =[ c ]=> sigmaF1 /\ sigmaI =[ c ]=> sigmaF2 /\ sigmaF1 <> sigmaF2.
  Proof.
    exists (X !-> 0).
    exists (Y !-> 1; X !-> 0).
    exists (X !-> 0).
    exists <{ flip (Y := 1) end}>.
    split.
    apply E_FlipTrue.
    apply E_Ass. reflexivity.
    split.
    apply E_FlipFalse.
    intros contra.
  Qed.
End ImpPlusFlip.

Module ISASemantics.

  (* In the rest of this assignment, you'll be extending the simple ISA
     from the first homework to support indexable memory and
     jumps. These extensions allow programs to store an arbitrary amount
     of data and to (potentially) loop forever.  *)

  (* We model memory as a total map from numeric indexes to a
     value. Since the definitions of maps in Map.v use strings for
     indexes, we duplicate some of its definitions for this
     variant. (Note that if those maps were polymorphic in the index,
     we would be saved from this, but oh well.)  *)
  Definition memory := nat -> nat.

  (* The initial memory has zeros at every index. *)
  Definition initialMem : memory := fun _ => 0.

  (* Updating a memory location works the same as in Maps.v *)
  Definition mem_update (mem : memory)
             (idx v : nat) :=
    fun idx' => if eqb idx idx' then v else mem idx'.

  (* We duplicate the update notation from Maps.v as well. *)
  Notation "x '!->' v ';' m" :=
    (mem_update m x v)
      (at level 100, v at next level, right associativity).

  (* Our ISA has three registers: [ax], [cx], and [dx]. Define an
   algebraic data type for three registers. *)
  Inductive Register : Type :=
  | ax (* Register One *)
  | cx (* Register Two *)
  | dx (* Register Three *).

  (* We introduce two new operands for working with memory:  *)
  Inductive Operand : Type :=
  | reg (r : Register)
  | memImm (idx : nat) (* A location in memory specified by a constant index *)
  | memReg (r : Register) (* A location in memory specified by an index held in a register *)
  | imm (n : nat).  (* Constant / Immediate.*)

  (* We also extend the definition of a machine state to include the
     current memory. *)
  Inductive MachineState :=
  | MState (ax cx ds : nat) (cc : bool) (mem : memory).

  (* We'll also update our getter and setter operations on machine states. *)
  Definition getReg (r : Register) (st : MachineState) : nat :=
    match r, st with
    | ax,  MState n _ _ _ _ => n
    | cx,  MState _ n _ _ _ => n
    | dx,  MState _ _ n _ _ => n
    end.

  Definition setReg (r : Register) (n : nat) (st : MachineState) : MachineState :=
    match r, st with
    | ax,  MState a c d f m => MState n c d f m
    | cx,  MState a c d f m => MState a n d f m
    | dx,  MState a c d f m => MState a c n f m
    end.

  Definition getFlag (st : MachineState) : bool :=
    match st with
    | MState _ _ _ b _ => b
    end.

  Definition setFlag (b : bool) (st : MachineState) : MachineState :=
    match st with
    | MState a c d _ m => MState a c d b m
    end.

  Definition setMemImm (idx v : nat) (st : MachineState) : MachineState :=
    match st with
    | MState a c d b m => MState a c d b (idx !-> v; m)
    end.

  Definition setMemReg (r : Register) (v : nat) (st : MachineState) : MachineState :=
    match r, st with
    | ax, MState a c d b m => MState a c d b (a !-> v; m)
    | cx, MState a c d b m => MState a c d b (c !-> v; m)
    | ds, MState a c d b m => MState a c d b (d !-> v; m)
    end.

  Definition getMemImm (idx : nat) (st : MachineState) : nat :=
    match st with
    | MState a c d b m => m idx
    end.

  Definition getMemReg (r : Register) (st : MachineState) : nat :=
    match r, st with
    | ax, MState a c d b m => m a
    | cx, MState a c d b m => m c
    | ds, MState a c d b m => m d
    end.

  (* The updated set of instructions replaces conditional set [cset]
     with a new move [mov] instruction, which (unconditionally) copies
     the value stored in the source to the destination. We will deal
     with conditionals shortly.

   Instruction |                 Description
   =============================================================================
   add  O1 R2    | Add source operand O1 to destination register R2
                   (i.e. add O1 to the value in R2)
   inc  R        | Increment the value of register R by 1
   cmp  O1 O2    | Set the condition code to reflect whether O1 equals O2
   mov O1 O2     | Move the source operand to the destination operand

   Here's the datatype for this set of instructions.  *)

  Inductive Instr : Type :=
  | add (src : Operand) (dest : Register)
  | inc (dest : Register)
  | cmp (src dest : Operand)
  | mov (src : Operand) (dest : Operand).

  (** **** Exercise: 2 point (Instr_evalR) *)
  (* The semantics of instructions are defined in the big-step style,
  as a inductively defined proposition from an initial state and an
  instruction to a final state. *)

  (* Here, for example is the evaluation rule for adding two registers: *)

  (* ===================================================================
    st =[add (reg r1) r2]=> (setReg r2 (getReg r1 st + getReg r2 st) st) *)

  (* For simplicity, we limit operations on memory to loading values
     into registers and storing values in memory.  Here are the
     evaluation rules dealing with memory as inference rules: *)

  (* ===================================================================
     st =[mov (memReg r1) (reg r2)]=>  setReg r2 (getMemReg r1 st) st *)

  (* ===================================================================
     st =[mov (reg r1) (memReg r2)]=> setMemReg r2 (getReg r1 st) st *)

  (* ======================================================
     st =[mov (memImm idx) (reg r2)]=> setReg r2 (getMemImm idx st) st *)

  (* ===================================================================
     st =[mov (reg r1) (memImm idx)]=> setMemImm idx (getReg r1 st) st *)

  (* Update the follow definition to include these rules: *)
  Inductive Instr_evalR : MachineState -> Instr -> MachineState -> Prop :=
  | E_AddReg : forall (r1 r2 : Register) (st : MachineState),
      Instr_evalR st (add (reg r1) r2) (setReg r2 (getReg r1 st + getReg r2 st) st)
  | E_AddImm : forall (n : nat) (r2 : Register) (st : MachineState),
      Instr_evalR st (add (imm n) r2) (setReg r2 (n + getReg r2 st) st)

  | E_IncReg : forall (r : Register) (st : MachineState),
      Instr_evalR st (inc r) (setReg r (1 + getReg r st) st)

  | E_CmpRegReg : forall (r1 r2 : Register) (st : MachineState),
      Instr_evalR st (cmp (reg r1) (reg r2)) (setFlag (eqb (getReg r1 st) (getReg r2 st)) st)
  | E_CmpRegImm : forall (r1 : Register) (n : nat) (st : MachineState),
      Instr_evalR st (cmp (reg r1) (imm n)) (setFlag (eqb (getReg r1 st) n) st)
  | E_CmpImmReg : forall (n : nat) (r2 : Register) (st : MachineState),
      Instr_evalR st (cmp (imm n) (reg r2)) (setFlag (eqb n (getReg r2 st)) st)

  | E_MovRegReg : forall (r1 r2 : Register) (st : MachineState),
      Instr_evalR st (mov (reg r1) (reg r2)) (setReg r2 (getReg r1 st) st)
  | E_MovImmReg : forall (n : nat) (r2 : Register) (st : MachineState),
      Instr_evalR st (mov (imm n) (reg r2)) (setReg r2 n st)

  (* FILL IN YOUR RULES HERE: *) .

  (* A program in our ISA now consists of a set of named 'basic
     blocks', i.e. straight-line code with no conditionals. Each basic
     block ends with a conditional jump to either another basic block
     or a special 'exit' block representing termination. *)

  (* A block identifier is either a string or a distinguished 'EXIT' token: *)
  Inductive BlockID : Type :=
  | Name (s : string)
  | Exit.

  (* The body of a basic block is simply a list of instructions, which
     by design now have no conditional operations. *)
  Inductive BasicBlock : Type :=
  | Block (BlockName : string) (body : list Instr) (NextBlockT NextBlockF : BlockID).

  Definition Program := total_map BasicBlock.
  (* The empty program maps every identifier to a block that
     immediately exits.*)
  Definition EmptyProgram : Program :=
    fun id => Block id [ ] Exit Exit.

  (** Exercise: 3 point (BasicBlock_step) *)
  (* A program executes a single block at a time, processing each
     instruction until none remain. Once all the instructions in the
     current basic block have been evaluated, execution continues on
     to one of the next blocks, depending on the value of the
     condition flag, transitioning to the first when it is true and
     the second otherwise. In the case that the next block is EXIT,
     evaluation is over and no step is taken.

     Here are two of the small-step evaluation rules capturing this evaluation
     strategy. We write =[ ]=> to refer to the instruction
     evaluation relation and --> for the basic block evaluation. *)

  (*  ms =[i]=> ms'
      =================================================================
      p |- ms, (Block ID (i :: body) NextBlockT NextBlockF) -->
           ms', (Block ID body NextBlockT NextBlockF) *)

  (*  p NextBlockT = (Block NextBlockT body NextBlockT' NextBlockF')
      getFlag ms = true
      =================================================================
      p |- ms, (Block ID [ ] NextBlockT NextBlockF) -->
           ms', (Block ID body NextBlockT' NextBlockF') *)

  (* Encode these rules as the following inductive proposition, and
     add a third rule to cover the case when the conditional flag is
     false. *)
  Inductive BasicBlock_step : Program ->
                              MachineState -> BasicBlock ->
                              MachineState -> BasicBlock -> Prop :=

  (* FILL IN YOUR RULES HERE: *) .

  (* The multistep relation for basic blocks is a standard adaptation
  of the definition in [SmallStep.v]: *)
  Inductive BasicBlock_multistep : Program ->
                                   MachineState -> BasicBlock ->
                                   MachineState -> BasicBlock -> Prop :=
  | BB_multi_refl : forall p st b, BasicBlock_multistep p st b st b
  | BB_multi_trans : forall p st1 st2 st3 b1 b2 b3,
      BasicBlock_step p st1 b1 st2 b2 ->
      BasicBlock_multistep p st2 b2 st3 b3 ->
      BasicBlock_multistep p st1 b1 st3 b3.

  (* Here is a set of instructions representing the 'swap' program
  from the first homework: *)
  Definition asmSwapAC : list Instr :=
    [mov (reg cx) (reg dx);
    mov (reg ax) (reg cx);
    mov (reg dx) (reg ax)].

  (** Exercise: 1 point (asmSwapACOK) *)
  (* Show that this program evaluates to the correct final state
     according to the evaluation rules you defined above: *)
  Example asmSwapACOK : forall p a c d f m,
      BasicBlock_multistep p
                           (MState a c d f m) (Block "Entry" asmSwapAC Exit Exit)
                           (MState c a c f m)
                           (Block "Entry" [] Exit Exit).
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (** Exercise: 1 point (Instr_evalR_deterministic) *)
  (* Prove that the evaluation of instructions is deterministic: *)
  Lemma Instr_evalR_deterministic :
    forall ms i ms1 ms2,
      Instr_evalR ms i ms1 ->
      Instr_evalR ms i ms2 ->
      ms1 = ms2.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (** Exercise: 2 point (BasicBlock_step_deterministic) *)
  (* Prove that the single step evaluation of basic blocks is deterministic: *)
  Lemma BasicBlock_step_deterministic :
    forall (p : Program) (ms ms1 ms2 : MachineState) (b b1 b2 : BasicBlock),
      BasicBlock_step p ms b ms1 b1 ->
      BasicBlock_step p ms b ms2 b2 ->
      ms1 = ms2 /\ b1 = b2.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (** Exercise: 1 point (BB_value) *)
  (* Define a inductive proposition capturing when an basic block is a
  *value*, i.e. it has hit a jump to the EXIT token and is thus done
  evaluating. *)
  Inductive BasicBlock_value : MachineState -> BasicBlock -> Prop :=
  (* FILL IN YOUR RULES HERE: *) .

  (* Recall that we can also define a more /semantic/ notion of when a
     program is done evaluting using the evaluation relation for basic
     blocks.  *)
  Definition normal_form (p : Program) (st : MachineState) (b : BasicBlock) : Prop :=
    ~ exists b' st', BasicBlock_step p st b b' st'.

  (** Exercise: 2 point (value_not_same_as_normal_form) *)
  (* Oftentimes we define value and step such that there are
   expressions that are not a 'value' but which cannot take a step
   according to the step relation (i.e. they are in a normal
   form). Such terms are said to be /stuck/. Sometimes this is caused
   by a mistake in the semantics, but in this case, there are certain
   basic blocks which get stuck by design. Show that our notions of
   value and normal form don't align by identify such a basic block
   and proving the following claim. *)
  Lemma value_not_same_as_normal_form :
    forall (st : MachineState),
    exists b : BasicBlock, ~ BasicBlock_value st b /\ normal_form EmptyProgram st b.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (* As we will discuss in a couple of weeks, we can use type systems
     to ensure that these two notions do align for well-typed
     programs. In other words, we will show that well-typed programs
     do not get 'stuck'.

     For basic blocks, it is possible to define a simple notion of
     well-formedness that ensures that can multistep to a value.

     Just for fun, try to define such a well-formedness condition as
     an inductive proposition and show that a well-formed basic block
     never gets stuck.

     Note this is an OPTIONAL exercise.
 *)

End ISASemantics.
