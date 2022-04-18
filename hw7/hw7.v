(****** Homework 7 (extra credit) for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 12/01/2020 by 6:00PM !!! **)
(* ================================================================= *)
(** ** Submission Guidelines *)

(* This assignment is purely /optional/; any points you receive will
   count toward the homework portion of your final grade. This could
   result in a total of more than 100% on that component of your
   grade, which will be reflected in your final grade. So, if you end
   up with 110% on the homeworks, it would count for 44% of your final
   grade. Assuming that you get 100% on everything else, your final
   grade would be 104, good for an A- in the class.



   Just kidding, that would be an A+. *)

(* This assignment asks you to come up with questions that could
   appear for the final (don't worry, they won't). These should be in
   the same format as the other assignments and tests in the class,
   i.e. a partial Coq development with holes that need to be filled
   in. *)

(* For each question, you are to provide three components:

   1) The rational behind the question [1 point]:
     - what learning objective it is testing, and
     - how it does so.
   2) The question itself [2 points]:
     - the prompt telling the student what to do
     - the Coq portion of the question, with holes for the students
   3) The solution [2 points]:
     - A copy of the question with the holes filled in.  *)

   (* Label 1) with RATIONALE #, 2) with QUESTION #, and 3) with SOLUTION #.
      See below for an example question. *)

(* - You can write up to two questions, for a total of 10 points.
     This assignment be worth half a 'normal' homework.

   - It should be possible to step through your homework using Coq--
     you will not receive full credit if not.

   - Only hand in [hw<n>.v]. Please do not submit auxiliary files,
     such as [Makefile] or [hw<n>_test.v].

   - You can import any files from the standard library, Logical
     Foundations, or Programming Language Foundations. No other
     dependencies are allowed (feel free to copy in definitions, if
     needed.  In other words, it should be possible to step through
     your file using a _CoqProject file like the ones accompanying the
     other homeworks.  *)

(* Here is an example of such a question. *)

From Coq Require Export
     String
     List
     Nat (* For natural number comparision operators. *)
     Arith.PeanoNat. (* For some additional lemmas about natural numbers. *)
Import List.ListNotations.
Import PeanoNat.Nat.

(* RATIONALE 1:
   - Learning Objective Tested: Define an axiomatic semantics for Imp.
   - How it tests this: Asking students to develop proof rules for
     Basic Blocks provides them an additional example of axiomatic
     semantics for another language, helping them to draw connections
     to and contrasts with the Hoare logic for Imp from the lectures,
     deepening their understanding of program logics. *)

(* QUESTION 1:
   - Prompt: *)

(* The inference rules for basic blocks roughly correspond to [H_Skip], [H_Seq],
     and [H_Consequence]:

     |-I {{P}} i {{R}}         |- {{R}} p {{Q}}
     ------------------------------------------------------------------ [H_Seq]
      |- {{P}} i; p {{Q}}

     ------------------------------------------------------------------ [H_End]
      |- {{P}} [ ] {{P}}

      |- {{P'}} p {{Q'}}   P ->> P'       Q ->> Q'
     ------------------------------------------------------------------ [H_Consequence]
     |- {{P}} p {{Q}}
 *)

(* Copies of definitions from the fifth homework, so that this file is self-contained: *)

(* Our ISA has three registers: [ax], [cx], and [dx]. Define an
   algebraic data type for three registers. *)
Inductive Register : Type :=
| ax (* Register One *)
| cx (* Register Two *)
| dx (* Register Three *).

(* The instructions of our ISA have two flavors of operands: registers
     and constants (aka immediate values). *)
Inductive Operand : Type :=
| reg (r : Register)
| imm (n : nat).  (* Constant / Immediate.*)

(* The current state of an execution consists of the values of each
     register (modelled as natural numbers), and the value of a
     condition code (modelled as a boolean flag). *)

Inductive MachineState :=
| MState (ax cx ds : nat) (cc : bool).

(* We'll also update our getter and setter operations on machine states. *)
Definition getReg (r : Register) (st : MachineState) : nat :=
  match r, st with
  | ax,  MState n _ _ _ => n
  | cx,  MState _ n _ _ => n
  | dx,  MState _ _ n _ => n
  end.

Definition setReg (r : Register) (n : nat) (st : MachineState) : MachineState :=
  match r, st with
  | ax,  MState a c d f => MState n c d f
  | cx,  MState a c d f => MState a n d f
  | dx,  MState a c d f => MState a c n f
  end.

Definition getFlag (st : MachineState) : bool :=
  match st with
  | MState _ _ _ b => b
  end.

Definition setFlag (b : bool) (st : MachineState) : MachineState :=
  match st with
  | MState a c d _ => MState a c d b
  end.

(* The informal specifications of the instructions of our ISA are once again:

   Instruction |                 Description
   =============================================================================
   inc  R      | Increment the value of register R by 1
   add  O R    | Add source operand O to destination register R (i.e. add O to the value in R)
   cmp  O1 O2  | Set the condition code to reflect whether O1 equals O2
   cset O R    | Store the value of operand O in register R if the condition code is true, do nothing otherwise.

 *)

Inductive Instr : Type :=
| add (src : Operand) (dest : Register)
| inc (dest : Register)
| cmp (src dest : Operand)
| cset (src : Operand) (dest : Register).

(* For this homework, we will only develop a logic for reasoning about basic
     blocks, ignoring issues of transfering control flow and nontermination.

     In this simpler setting, a basic block is simply a list of instructions. *)
Definition BasicBlock : Type := list Instr.

(* The semantics of instructions are defined in the big-step style,
  as a inductively defined proposition from an initial state and an
  instruction to a final state. *)
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
| E_CmpImmImm : forall (n m: nat) (st : MachineState),
    Instr_evalR st (cmp (imm n) (imm m)) (setFlag (eqb n m) st)

| E_CSetRegT : forall (r1 r2 : Register) (st : MachineState),
    getFlag st = true ->
    Instr_evalR st (cset (reg r1) r2) (setReg r2 (getReg r1 st) st)
| E_CSetRegF : forall (r1 r2 : Register) (st : MachineState),
    getFlag st = false ->
    Instr_evalR st (cset (reg r1) r2) st
| E_CSetImmT : forall (n : nat) (r2 : Register) (st : MachineState),
    getFlag st = true ->
    Instr_evalR st (cset (imm n) r2) (setReg r2 n st)
| E_CSetImmF : forall (n : nat) (r2 : Register) (st : MachineState),
    getFlag st = false ->
    Instr_evalR st (cset (imm n) r2) st.

(* Basic blocks are evaluated by processing each instruction in order. *)
Inductive BasicBlock_evalR : MachineState -> BasicBlock ->
                             MachineState -> Prop :=
| E_Instr : forall (ms ms' ms'' : MachineState)
                   (i : Instr) (body : list Instr),
    Instr_evalR ms i ms' ->
    BasicBlock_evalR ms' body ms'' ->
    BasicBlock_evalR ms (i :: body) ms''
| E_Done : forall (ms  : MachineState),
    BasicBlock_evalR ms [ ] ms.

Definition evalInstr (i : Instr) (st : MachineState) : MachineState :=
  match i with
  | add (reg r1) r2 => setReg r2 (getReg r1 st + getReg r2 st) st
  | add (imm n) r2 => setReg r2 (n + getReg r2 st) st
  | inc r => setReg r (1 + getReg r st) st
  | cmp (reg r1) (reg r2) => setFlag (eqb (getReg r1 st) (getReg r2 st)) st
  | cmp (reg r1) (imm n) => setFlag (eqb (getReg r1 st) n) st
  | cmp (imm n) (reg r2) => setFlag (eqb n (getReg r2 st)) st
  | cmp (imm n) (imm m) => setFlag (eqb n m) st
  | cset (reg r1) r2 =>
    if getFlag st then (setReg r2 (getReg r1 st) st) else st
  | cset (imm n) r2 =>
    if getFlag st then (setReg r2 n st) else st
  end.

Lemma Instr_evalR_OK : forall st i,
    Instr_evalR st i (evalInstr i st).
Proof.
  induction i; simpl.
  - destruct src; econstructor.
  - econstructor.
  - destruct src; destruct dest; try econstructor.
  - destruct src; destruct (getFlag st) eqn: ?; econstructor; eauto.
Qed.


Definition Assertion := MachineState -> Prop.

Reserved Notation " |- {{ P }}  p  {{ Q }}"
         (at level 40, p at next level).

Reserved Notation " |-I {{ P }}  p  {{ Q }}"
         (at level 40, p at next level).

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

(* The Question: *)
(** Exercise: 1 point (BB_proof) *)
(* Formalize these rules as an inductive proposition *)
Inductive BB_proof : Assertion -> BasicBlock -> Assertion -> Prop :=

where " |- {{ P }}  p  {{ Q }}" := (BB_proof P p Q).

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q) (at level 80).

(* SOLUTION 1: *)
(* The solution: *)
Inductive BB_proof' : Assertion -> BasicBlock -> Assertion -> Prop :=
| H_Seq : forall (P Q R : Assertion) (i : Instr) (p : BasicBlock),
    |-I {{P}} i {{R}} ->
    |- {{R}} p {{Q}} ->
    |- {{P}} (i :: p) {{Q}}
| H_End : forall (P : Assertion),
    |- {{P}} [ ] {{P}}
| H_Consequence : forall (P Q P' Q' : Assertion) c,
    |- {{P'}} c {{Q'}} ->
       P ->> P' ->
       Q' ->> Q ->
    |- {{P}} c {{Q}}
where " |- {{ P }}  p  {{ Q }}" := (BB_proof' P p Q).
