From Coq Require Export
     String
     List
     Nat (* For natural number comparision operators. *)
     Arith.PeanoNat. (* For some additional lemmas about natural numbers. *)
Import List.ListNotations.
Import PeanoNat.Nat.


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
