Require Export String.
Open Scope string.

Ltac start m := idtac "----" m.
Ltac nl := idtac "".
Ltac exc x := idtac "Exercise:" x.
Ltac itm x := idtac "Sub-exercise:" x.
Ltac pt x := idtac "Possible points:" x.
Ltac ass := idtac "Assumptions:".

Parameter MISSING: Type.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => gfail 1 "Type missing for" A
    | ?T => unify T B
    end.

Require hw5.

Goal True.
  start "hw5".
  nl.

  exc "ISASemantics.assert_ex_3".
  pt 1.
  check_type @hw5.ISASemantics.assert_ex_3 ((hw5.ISASemantics.Assertion)).
  check_type @hw5.ISASemantics.assert_ex_3_ex ((hw5.ISASemantics.assert_ex_3 (ISA.MState 0 3 4 false))).
  ass.
  Print Assumptions hw5.ISASemantics.assert_ex_3_ex.
  nl.

  exc "ISASemantics.BB_proof".
  pt 1.
  check_type @hw5.ISASemantics.BB_proof ((hw5.ISASemantics.Assertion -> ISA.BasicBlock -> hw5.ISASemantics.Assertion -> Prop)).
  nl.

  exc "ISASemantics.BB_proof_sound".
  pt 3.
  check_type @hw5.ISASemantics.BB_proof_sound ((forall (P : hw5.ISASemantics.Assertion) (p : ISA.BasicBlock) (Q : hw5.ISASemantics.Assertion),
       hw5.ISASemantics.BB_proof P p Q -> hw5.ISASemantics.BB_triple P p Q)).
  ass.
  Print Assumptions hw5.ISASemantics.BB_proof_sound.
  nl.

  exc "ISASemantics.wlp_gen".
  pt 3.
  check_type @hw5.ISASemantics.wlp_gen ((ISA.BasicBlock -> hw5.ISASemantics.Assertion -> hw5.ISASemantics.Assertion)).
  nl.

  exc "ISASemantics.wlp_gen_is_wlp".
  pt 3.
  check_type @hw5.ISASemantics.wlp_gen_is_wlp ((forall (p : ISA.BasicBlock) (Q : hw5.ISASemantics.Assertion),
       hw5.ISASemantics.wlp p Q (hw5.ISASemantics.wlp_gen p Q))).
  ass.
  Print Assumptions hw5.ISASemantics.wlp_gen_is_wlp.
  nl.

  exc "ISASemantics.wlp_is_derivable".
  pt 3.
  check_type @hw5.ISASemantics.wlp_is_derivable ((forall (p : ISA.BasicBlock) (Q : hw5.ISASemantics.Assertion),
       hw5.ISASemantics.BB_proof (hw5.ISASemantics.wlp_gen p Q) p Q)).
  ass.
  Print Assumptions hw5.ISASemantics.wlp_is_derivable.
  nl.

  exc "ISASemantics.BB_proof_complete".
  pt 2.
  check_type @hw5.ISASemantics.BB_proof_complete ((forall (P : hw5.ISASemantics.Assertion) (p : ISA.BasicBlock) (Q : hw5.ISASemantics.Assertion),
       hw5.ISASemantics.BB_triple P p Q -> hw5.ISASemantics.BB_proof P p Q)).
  ass.
  Print Assumptions hw5.ISASemantics.BB_proof_complete.
  nl.

  exc "#ISASemantics.verify_ht_ex".
  pt 1.
  check_type @hw5.ISASemantics.evalAddFlagID' ((forall (src : ISA.Operand) (dest : ISA.Register) (f : bool),
       hw5.ISASemantics.BB_triple (fun st : ISA.MachineState => ISA.getFlag st = f)
         (ISA.add src dest :: nil)%list (fun st : ISA.MachineState => ISA.getFlag st = f))).
  check_type @hw5.ISASemantics.evalCsetOK' ((forall (src : ISA.Operand) (dest : ISA.Register) (P : hw5.ISASemantics.Assertion),
       hw5.ISASemantics.BB_triple (fun st : ISA.MachineState => P st /\ ISA.getFlag st = false)
         (ISA.cset src dest :: nil)%list P)).
  check_type @hw5.ISASemantics.asmSwapACOK' ((forall m n : nat,
       hw5.ISASemantics.BB_triple
         (fun st : ISA.MachineState => ISA.getReg ISA.ax st = m /\ ISA.getReg ISA.cx st = n)
         hw5.ISASemantics.asmSwapAC
         (fun st : ISA.MachineState => ISA.getReg ISA.ax st = n /\ ISA.getReg ISA.cx st = m))).
  check_type @hw5.ISASemantics.asmTripleAxOK' ((forall m : nat,
       hw5.ISASemantics.BB_triple (fun st : ISA.MachineState => ISA.getReg ISA.ax st = m)
         hw5.ISASemantics.asmTriple (fun st : ISA.MachineState => ISA.getReg ISA.ax st = 3 * m))).
  ass.
  Print Assumptions hw5.ISASemantics.evalAddFlagID'.
  Print Assumptions hw5.ISASemantics.evalCsetOK'.
  Print Assumptions hw5.ISASemantics.asmSwapACOK'.
  Print Assumptions hw5.ISASemantics.asmTripleAxOK'.
  nl.

Abort.
