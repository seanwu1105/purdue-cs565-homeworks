(****** Homework 1 for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 09/05/2020 by 6:00PM !!! **)
(* ================================================================= *)
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

    Each homework (like [hw1.v]) is accompanied by a _test script_
    ([hw1_test.v]). You may want to use them to double-check that your
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
        graded.

    We are using Brightspace for submission. If you submit multiple
    versions of the assignment, you may notice that they are given
    different names.  This is fine: The most recent submission is the
    one that will be graded. *)

(** The [Require Export] statement on the next line tells Coq to use
    the [Nat] and PeanoNat modules from the standard library.  *)
From Coq Require Export
        Nat (* For natural number comparison operators. *)
        Arith.PeanoNat. (* For some additional lemmas about natural numbers. *)
Import PeanoNat.Nat.

(* In this homework, you'll be modelling a *very* simple ISA in Coq
   and proving some basic facts about your encoding.

   This ISA is a variant of x86 with only three registers, no memory,
   and a single condition code register that holds the result of the
   last comparison.

   The ISA has only three arithmetic instructions and a single logical
   instruction: add, increment, conditional set, and compare. There
   are no memory or control flow instructions. Again, it's a *very*
   simple ISA.  *)

(* ================================================================= *)
(* Basic Functional Programming: *)
(** **** Exercise: 1 star (Register) *)

(* Our ISA has three registers: [ax], [cx], and [dx]. Define an
   algebraic data type for three registers. *)

Inductive Register : Type :=   (* FILL IN HERE *).

(** **** Exercise: 1 star (Register) *)
(* The instructions of our ISA have two flavors of operands: registers
   and constants (aka immediate values).  Define an ADT representing
   both. *)
Inductive Operand : Type :=   (* FILL IN HERE *).


(** **** Exercise: 1 star (MachineState) *)
(* The current state of an execution consists of the values of each
   register (modelled as natural numbers), and the value of a
   condition code (modelled as a boolean flag). Define an ADT
   representing these machine states. *)
Inductive MachineState : Type :=   (* FILL IN HERE *).


(** **** Exercise: 1 star (getReg, setReg, getFlag, setFlag) *)
(* Define getter and setter functions for the registers an the
   condition code. *)
Definition getReg (r : Register) (st : MachineState) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.

Definition setReg (r : Register) (n : nat) (st : MachineState) : MachineState
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.

Definition getFlag (st : MachineState) : bool
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.

Definition setFlag (b : bool) (st : MachineState) : MachineState
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.

(** **** Exercise: 1 star (Instr) *)
(* At long last, we can now define a datatype representing the
   instructions of our ISA. The informal specifications of these instructions are:

   Instruction |                 Description
   =============================================================================
   inc  R      | Increment the value of register R by 1
   add  O R    | Add source operand O to destination register R (i.e. add O to the value in R)
   cmp  O1 O2  | Set the condition code to reflect whether O1 equals O2
   cset O R    | Store the value of operand O in register R if the condition code is true, do nothing otherwise.

 Define a datatype for this set of instructions. *)

Inductive Instr : Type :=   (* FILL IN HERE *).


(** **** Exercise: 2 star (evalInstr) *)
(* As we discussed in class, datatypes have no intrinsic meaning on
   their own; it is through functions that use them that we assign
   them an interpretation.  Using the informal specifications from the
   previous exercise, define an evaluation function for single
   instructions. *)
Definition evalInstr (i : Instr) (st : MachineState) : MachineState
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.

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
  (* FILL IN HERE *)
Admitted.


(** **** Exercise: 1 star (Demorgan2) *)
Theorem Demorgan2 : forall (a b : bool), negb (orb a b) = andb (negb a) (negb b).
Proof.
  (* FILL IN HERE *)
Admitted.

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
(* REPLACE THIS LINE WITH "getFlag (evalInstr (add src cx) st) = getFlag st." ONCE YOU HAVE COMPLETED THE [Register] EXERCISE.   *) True.
(* YOU MAY HAVE TO ADJUST THE REGISTER NAMES IN THE THEOREM STATEMENT
TO REFLECT YOUR DEFINITION OF [Register]. *)
Proof.
  (* FILL IN HERE *)
Admitted.


(* ================================================================= *)
(* Proof by case analysis + rewrite: *)
(* Hint: You should be able to complete the proofs in this section
   using just the [intros]; [destruct]; [simpl]; [reflexivity]; and
   [rewrite] tactics.*)

(** **** Exercise: 1 star (evalFlagID) *)
(* Prove that [evalInstr] leaves a non-destination register unchanged. *)
Theorem evalCsetOK : forall (src : Operand) (dest : Register) (st : MachineState),
    getFlag st = false ->
    (* REPLACE THIS LINE WITH "evalInstr (cset src dest) st = st." ONCE YOU HAVE COMPLETED THE [Instr] EXERCISE *) True.
(* YOU MAY HAVE TO ADJUST THE INSTRUCTION NAMES IN THE THEOREM STATEMENT
TO REFLECT YOUR DEFINITION OF [Instr]. *)
Proof.
  (* FILL IN HERE *)
Admitted.


(** **** Exercise: 1 star (evalAddComm) *)
(* Prove that [evalInstr] is commutative. The theorem [add_comm]
   should prove useful in this proof. *)
Theorem evalAddComm : forall (src dest : Register) (st : MachineState),
        (* REPLACE THIS LINE WITH "getReg dest (evalInstr (add (reg src) dest) st) = getReg src (evalInstr (add (reg dest) src) st). " ONCE YOU HAVE COMPLETED THE [Instr] EXERCISE *) True.
Proof.
(* YOU MAY HAVE TO ADJUST THE INSTRUCTION NAMES IN THE THEOREM STATEMENT
TO REFLECT YOUR DEFINITION OF [Instr] and [Operand]. *)
  (* FILL IN HERE *)
Admitted.

(* ================================================================= *)
(* Inductive Datatypes: *)

(** **** Exercise: 1 star (AsmProg) *)
(* An assembly program is a sequence of instructions. That is, it is
   either the empty program, or an instruction sequenced with another
   program. Define an inductive datatype for assembly programs. *)
Inductive AsmProg : Type := (* FILL IN HERE*).


(** **** Exercise: 1 star (evalAsm) *)
(* Using [evalInstr], define an evaluation function for assembly
   programs. *)
Fixpoint evalAsm (p : AsmProg) (st : MachineState) : MachineState
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.


(** **** Exercise: 1 star (asmSwapAC) *)
(* A program is a value of type [AsmProg]. Define a program that swaps
the ax and cx registers (it's okay if the dx register) is modified in
the process.  *)
Definition asmSwapAC : AsmProg
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.


(** **** Exercise: 1 star (asmSwapACOK) *)
(* Prove that [asmSwap] progam from the previous exercise correctly
   stores the value of the [cx] register in the [ax] register. *)
Theorem asmSwapACOK : forall (st : MachineState),
    (* REPLACE THIS LINE WITH "getReg ax (evalAsm asmSwapAC st) = getReg cx st." ONCE YOU HAVE COMPLETED THE [Register] EXERCISE *) True.
(* YOU MAY HAVE TO ADJUST THE REGISTER NAMES IN THE THEOREM STATEMENT
TO REFLECT YOUR DEFINITION OF [Register]. *)
Proof.
  (* FILL IN HERE *)
Admitted.


(** **** Exercise: 1 star (asmSwapACOK') *)
(* Prove that [asmSwap] progam from the previous exercise correctly
   stores the value of the [ax] register in the [cx] register. *)
Theorem asmSwapACOK' : forall (st : MachineState),
    (* REPLACE THIS LINE WITH "getReg cx (evalAsm asmSwapAC st) = getReg ax st." ONCE YOU HAVE COMPLETED THE [Register] EXERCISE *) True.
(* YOU MAY HAVE TO ADJUST THE REGISTER NAMES IN THE THEOREM STATEMENT
TO REFLECT YOUR DEFINITION OF [Register]. *)
Proof.
  (* FILL IN HERE *)
Admitted.


(** **** Exercise: 1 star (asmTripleAx) *)
(* Write a program that triples the value in the [ax] register. *)
Definition asmTripleAx : AsmProg
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.

(** **** Exercise: 2 star (asmTripleAxOK) *)
(* Formalize the claim that "For every starting state, evaluating
   [asmTripleAx] produces a state in which the value in the [ax]
   register is three times its initial value" as a [Theorem], and
   prove that your theorem is correct.

   Hint: the [plus_n_O] fact might be useful in your proof. *)
Theorem asmTripleAxOK :
(* REPLACE THIS LINE WITH "_your definition_ ." ONCE YOU HAVE COMPLETED THE PREVIOUS EXERCISES *) True.
Proof.
  (* FILL IN HERE*)
Admitted.
