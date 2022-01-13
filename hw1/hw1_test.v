(** Do not submit this file. *)

Require Import hw1.

Parameter MISSING: Type.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => gfail 1 "Type missing:" A
    | ?T => first [unify T B | gfail 1 "Type wrong - should be (" B ")"]
    end.

Ltac nl := idtac "".
Ltac point x := idtac "Possible point:" x.

Goal True.
  idtac "*>" "Register".
  point 1.
  nl.

  idtac "*>" "Operand".
  point 1.
  nl.

  idtac "*>" "MachineState".
  point 1.
  nl.

  idtac "*>" "Getter and setter functions".
  point 1.
  nl.

  idtac "#>" "getReg".
  check_type @getReg ((Register -> MachineState -> nat)).
  idtac "Assumptions:".
  Print Assumptions getReg.
  nl.

  idtac "#>" "setReg".
  check_type @setReg ((Register -> nat -> MachineState -> MachineState)).
  idtac "Assumptions:".
  Print Assumptions setReg.
  nl.

  idtac "#>" "getFlag".
  check_type @getFlag ((MachineState -> bool)).
  idtac "Assumptions:".
  Print Assumptions getFlag.
  nl.

  idtac "#>" "setFlag".
  check_type @setFlag ((bool -> MachineState -> MachineState)).
  idtac "Assumptions:".
  Print Assumptions setFlag.
  nl.

  idtac "*>" "Instr".
  point 1.
  nl.

  idtac "*>" "evalInstr".
  point 2.
  check_type @evalInstr ((Instr -> MachineState -> MachineState)).
  idtac "Assumptions:".
  Print Assumptions evalInstr.
  nl.

  idtac "*>" "Demorgan1".
  point 1.
  check_type @Demorgan1 ((forall (a b : bool), negb (andb a b) = orb (negb a) (negb b))).
  idtac "Assumptions:".
  Print Assumptions Demorgan1.
  nl.

  idtac "*>" "Demorgan2".
  point 1.
  check_type @Demorgan2 ((forall (a b : bool), negb (orb a b) = andb (negb a) (negb b))).
  idtac "Assumptions:".
  Print Assumptions Demorgan2.
  nl.

  idtac "*>" "evalAddFlagID".
  point 1.
  (* check_type @evalAddFlagID ((forall (src : Operand) (dest : Register) (st : MachineState), *)
  (*                                getFlag (evalInstr (add src cx) st) = getFlag st)). *)
  idtac "Assumptions:".
  Print Assumptions evalAddFlagID.
  nl.

  idtac "*>" "evalCsetOK".
  point 1.
  (* check_type @evalCsetOK ((forall (src : Operand) (dest : Register) (st : MachineState), *)
  (*                             getFlag st = false -> *)
  (*                             evalInstr (cset src dest) st = st)). *)
  idtac "Assumptions:".
  Print Assumptions evalCsetOK.
  nl.
 
  idtac "*>" "evalAddComm".
  point 1.
  (* check_type @evalAddComm ((forall (src dest : Register) (st : MachineState), *)
  (*                              getReg dest (evalInstr (add (reg src) dest) st) = getReg src (evalInstr (add (reg dest) src) st))). *)
  idtac "Assumptions:".
  Print Assumptions evalAddComm.
  nl.

  idtac "*>" "AsmProg".
  point 1.
  nl.

  idtac "*>" "evalAsm".
  point 1.
  check_type @evalAsm ((AsmProg -> MachineState -> MachineState)).
  idtac "Assumptions:".
  Print Assumptions evalAsm.
  nl.

  idtac "*>" "asmSwapAC".
  point 1.
  check_type @asmSwapAC ((AsmProg)).
  idtac "Assumptions:".
  Print Assumptions asmSwapAC.
  nl.

  idtac "*>" "asmSwapACOK".
  point 1.
  (* check_type @asmSwapACOK ((forall (st : MachineState), *)
  (*                              getReg ax (evalAsm asmSwapAC st) = getReg cx st)). *)
  idtac "Assumptions:".
  Print Assumptions asmSwapACOK.
  nl.

  idtac "*>" "asmSwapACOK'".
  point 1.
  (* check_type @asmSwapACOK' ((forall (st : MachineState), *)
  (*                              getReg cx (evalAsm asmSwapAC st) = getReg ax st)). *)
  idtac "Assumptions:".
  Print Assumptions asmSwapACOK'.
  nl.

  idtac "*>" "asmTripleAx".
  point 1.
  check_type @asmTripleAx ((AsmProg)).
  idtac "Assumptions:".
  Print Assumptions asmTripleAx.
  nl.

  idtac "*>" "asmTripleAxOK".
  point 2.
  idtac "Assumptions:".
  Print Assumptions asmTripleAxOK.
  nl.

Abort.
