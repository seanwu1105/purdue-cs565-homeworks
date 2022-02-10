(****** Homework 1 for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 09/05/2018 by 6:00PM !!! **)
(* ================================================================= *)
(** ** DO NOT REDISTRIBUTE!!!! *)

(** The [Require Export] statement on the next line tells Coq to use
    the [Nat] and PeanoNat modules from the standard library.  *)
From Coq Require Export
        Nat (* For natural number comparision operators. *)
        Arith.PeanoNat. (* For some additional lemmas about natural numbers. *)
Import PeanoNat.Nat.

(* In this homework, you'll be modelling a *very* simple ISA in Coq
   and proving some basic facts about your encoding.

   This ISA is a variant of x86 with only three registers, no memory,
   and a single condition code register that holds the result of the
   last comparision.

   The ISA has only three arithmetic instructions and a single logical
   instruction: add, increment, conditional set, and compare. There
   are no memory or control flow instructions. Again, it's a *very*
   simple ISA.  *)

(* ================================================================= *)
(* Basic Functional Programming: *)
(** **** Exercise: 1 star (Register) *)

(* Our ISA has three registers: [ax], [cx], and [dx]. Define an
   algebraic data type for three registers. *)

Inductive Register : Type :=
| ax (* Register One *)
| cx (* Register Two *)
| dx (* Register Three *).


(** **** Exercise: 1 star (Register) *)
(* The instructions of our ISA have two flavors of operands: registers
   and constants (aka immediate values).  Define an ADT representing
   both. *)
Inductive Operand : Type :=
| reg (ax : Register)
| imm (n : nat).  (* Constant / Immediate.*)


(** **** Exercise: 1 star (Register) *)
(* The current state of an execution consists of the values of each
   register (modelled as natural numbers), and the value of a
   condition code (modelled as a boolean flag). Define an ADT
   representing these machine states. *)
Inductive MachineState :=
| MState (ax cx ds : nat) (cc : bool).


(** **** Exercise: 1 star (getReg, setReg, getFlag, setFlag) *)
(* Define getter and setter functions for the registers an the
   condition code. *)
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

(** **** Exercise: 1 star (Instr) *)
(* At long last, we can now define a datatype representing the
   instructions of our ISA. The informal specifications of these instructions are:

   Instruction |                 Description
   =============================================================================
   inc  R      | Increment the value of register R by 1
   add  O R    | Add source operand O to destination register R (i.e. add O to the value in R)
   cmp  O1 O2  | Set the condition code to reflect whether O1 equals O2
   cset O R    | Store the value of operand O in register R if the condition code is true, do nothing otherwise.

 Define a datatype for this set of instructions.
 *)

Inductive Instr : Type :=
| add (src : Operand) (dest : Register)
| inc (dest : Register)
| cmp (src dest : Operand)
| cset (src : Operand) (dest : Register).


(** **** Exercise: 2 star (evalInstr) *)
(* As we discussed in class, datatypes have no intrinsic meaning on
   their own; it is through functions that use them that we assign
   them an interpretation.  Using the informal specifications from the
   previous exercise, define an evaluation function for single
   instructions. *)
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

(* ================================================================= *)
(* Proof by case analysis: *)
(* Hint: You should be able to complete the proofs in this section
   using just the [intros]; [destruct]; [simpl]; and [reflexivity]
   tactics.*)

(* In boolean algebra, DeMorgan's laws are a pair of equivalences
   between formulas, typically described in English as: - the negation
   of a disjunction is the conjunction of the negations - and the
   negation of a conjunction is the disjunction of the negations.

The following two theorems ([Demorgan1] and [Demorgan2] prove that
these laws hold for the definitions of boolean, logical and, and logic
or from Coq's standard library. *)
(** **** Exercise: 1 star (Demorgan1) *)
Theorem Demorgan1 : forall (a b : bool), negb (andb a b) = orb (negb a) (negb b).
Proof.
  intros [ ] [ ].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


(** **** Exercise: 1 star (Demorgan2) *)
Theorem Demorgan2 : forall (a b : bool), negb (orb a b) = andb (negb a) (negb b).
Proof.
  intros [ ] [ ].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ================================================================= *)
(* One way to validate that your implementation of [evalInstr] is
   correct is to prove that it satisfies some equations implied by the
   informal description of evaluation. One of the advantages of using
   Coq is that we can use it to prove that a function is correct for a
   mixture of specific

*)

(** **** Exercise: 1 star (evalFlagID) *)
(* Prove evaluation of the add instruction leaves the conditional flag
   unchanged for every possible combination of operands and initial
   states. *)
Theorem evalAddFlagID : forall (src : Operand) (dest : Register) (st : MachineState),
    getFlag (evalInstr (add src cx) st) = getFlag st.
Proof.
  intros.
  simpl.
  destruct src.
  - destruct st.
    simpl.
    reflexivity.
  - destruct st.
    simpl.
    reflexivity.
Qed.

(* ================================================================= *)
(* Proof by case analysis + rewrite: *)
(* Hint: You should be able to complete the proofs in this section
   using just the [intros]; [destruct]; [simpl]; [reflexivity]; and
   [rewrite] tactics.*)

(** **** Exercise: 1 star (evalFlagID) *)
(* Prove that [evalInstr] leaves a non-destination register unchanged. *)
Theorem evalCsetOK : forall (src : Operand) (dest : Register) (st : MachineState),
    getFlag st = false ->
    evalInstr (cset src dest) st = st.
Proof.
  intros.
  simpl.
  destruct src.
  - rewrite H.
    reflexivity.
  - rewrite H.
    reflexivity.
Qed.

(** **** Exercise: 1 star (evalAddComm) *)
(* Prove that [evalInstr] is commutative. The theorem [add_comm]
   should prove useful in this proof. *)
Theorem evalAddComm : forall (src dest : Register) (st : MachineState),
    getReg dest (evalInstr (add (reg src) dest) st) =
    getReg src (evalInstr (add (reg dest) src) st).
Proof.
  intros [ ] [ ] [ ].
  - simpl. reflexivity.
  - simpl. rewrite add_comm.
    reflexivity.
  - simpl. rewrite add_comm. reflexivity.
  - simpl. rewrite add_comm. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite add_comm. reflexivity.
  - simpl. rewrite add_comm. reflexivity.
  - simpl. rewrite add_comm. reflexivity.
  - simpl. reflexivity.
Qed.

(* ================================================================= *)
(* Inductive Datatypes: *)

(** **** Exercise: 1 star (AsmProg) *)
(* An assembly program is a sequence of instructions. That is, it is
   either the empty program, or an instruction sequenced with another
   program. Define an inductive datatype for assembly programs. *)
Inductive AsmProg : Type :=
| Seq (i : Instr) (p : AsmProg)
| Empty.

(** **** Exercise: 1 star (evalAsm) *)
(* Using [evalInstr], define an evaluation function for assembly
   programs. *)
Fixpoint evalAsm (p : AsmProg) (st : MachineState) : MachineState :=
  match p with
  | Empty => st
  | Seq i p' => evalAsm p' (evalInstr i st)
  end.

(** **** Exercise: 1 star (asmSwapAC) *)
(* A program is a value of type [AsmProg]. Define a program thatswaps
the ax and cx registers (it's okay if the dx register) is modified in
the process.  *)
Definition asmSwapAC : AsmProg :=
  Seq (cmp (imm 0) (imm 0))
      (Seq (cset (reg cx) dx)
           (Seq (cset (reg ax) cx)
                (Seq (cset (reg dx) ax)
                     Empty))).

(** **** Exercise: 1 star (asmSwapACOK) *)
(* Prove that [asmSwap] progam from the previous exercise correctly
   stores the value of the [cx] register in the [ax] register. *)
Theorem asmSwapACOK : forall st,
    getReg ax (evalAsm asmSwapAC st) = getReg cx st.
Proof.
  intros []; simpl; reflexivity.
Qed.

(** **** Exercise: 1 star (asmSwapACOK) *)
(* Prove that [asmSwap] progam from the previous exercise correctly
   stores the value of the [ax] register in the [cx] register. *)
Theorem asmSwapACOK' : forall st,
    getReg cx (evalAsm asmSwapAC st) = getReg ax st.
Proof.
  intros []; simpl; reflexivity.
Qed.

(** **** Exercise: 1 star (asmTripleAx) *)
(* Write a program that triples the value in the [ax] register. *)
Definition asmTripleAx : AsmProg :=
  Seq (cmp (imm 0) (imm 0))
      (Seq (cset (reg ax) cx)
           (Seq (add (reg cx) ax)
                (Seq (add (reg cx) ax)
                     Empty))).

(** **** Exercise: 2 star (asmTripleAxOK) *)
(* Formalize the claim that "For every starting state, evaluating
   [asmTripleAx] produces a state in which the value in the [ax]
   register is three times its initial value" as a [Theorem], and
   prove that your theorem is correct.

   Hint: the [plus_n_O] fact might be useful in your proof. *)
Theorem asmTripleAxOK : forall st,
  getReg ax (evalAsm asmTripleAx st) = 3 * (getReg ax st).
Proof.
  intros [].
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.
