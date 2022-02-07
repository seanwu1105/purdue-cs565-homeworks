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

Require hw3.

Goal True.
  start "hw3".
  nl.

  exc "ev'_ev".
  pt 1.
  check_type @hw3.ev'_ev ((forall n : nat, hw3.ev' n <-> hw3.ev n)).
  ass.
  Print Assumptions hw3.ev'_ev.
  nl.

  exc "ev_ev__ev".
  pt 1.
  check_type @hw3.ev_ev__ev ((forall n m : nat, hw3.ev (n + m) -> hw3.ev n -> hw3.ev m)).
  ass.
  Print Assumptions hw3.ev_ev__ev.
  nl.

  exc "IsPalindrome_equiv".
  pt 1.
  check_type @hw3.IsPalindrome_equiv ((forall l : list nat, hw3.IsPalindrome l -> hw3.IsPalindrome' l)).
  ass.
  Print Assumptions hw3.IsPalindrome_equiv.
  nl.

  exc "ImpPlusFlip.ceval".
  pt 1.
  check_type @hw3.ImpPlusFlip.ceval ((hw3.ImpPlusFlip.com -> Imp.state -> Imp.state -> Prop)).
  nl.

  exc "ImpPlusFlip p1_NN, p1_Y, p1_NY".
  pt 2.
  nl.

  itm "ImpPlusFlip.p1_NN".
  check_type @hw3.ImpPlusFlip.p1_NN
             ((forall sigma : Imp.state,
                  hw3.ImpPlusFlip.ceval hw3.ImpPlusFlip.p1 sigma
                                        (Maps.t_update (Maps.t_update sigma Imp.X 2) Imp.Y 6))).
  ass.
  Print Assumptions hw3.ImpPlusFlip.p1_NN.
  nl.

  itm "ImpPlusFlip.p1_Y".
  check_type @hw3.ImpPlusFlip.p1_Y
             ((forall sigma : Imp.state,
                  hw3.ImpPlusFlip.ceval hw3.ImpPlusFlip.p1 sigma
                                        (Maps.t_update (Maps.t_update (Maps.t_update (Maps.t_update sigma Imp.X 2) Imp.Y 6) Imp.X 4)
                                                       Imp.Y 3))).
  ass.
  Print Assumptions hw3.ImpPlusFlip.p1_Y.
  nl.

  itm "ImpPlusFlip.p1_NY".
  check_type @hw3.ImpPlusFlip.p1_NY
             ((forall sigma : Imp.state,
                  hw3.ImpPlusFlip.ceval hw3.ImpPlusFlip.p1 sigma
                                        (Maps.t_update (Maps.t_update (Maps.t_update sigma Imp.X 2) Imp.Y 6) Imp.Y 2))).
  ass.
  Print Assumptions hw3.ImpPlusFlip.p1_NY.
  nl.

  exc "ImpPlusFlip.ceval_is_nondeterministic".
  pt 2.
  check_type @hw3.ImpPlusFlip.ceval_is_nondeterministic
             ((exists (sigmaI sigmaF1 sigmaF2 : Imp.state) (c : hw3.ImpPlusFlip.com),
                  hw3.ImpPlusFlip.ceval c sigmaI sigmaF1 /\
                  hw3.ImpPlusFlip.ceval c sigmaI sigmaF2 /\ sigmaF1 <> sigmaF2)).
  ass.
  Print Assumptions hw3.ImpPlusFlip.ceval_is_nondeterministic.
  nl.

  exc "ISASemantics.Instr_evalR".
  pt 2.
  check_type @hw3.ISASemantics.Instr_evalR
             ((hw3.ISASemantics.MachineState ->
               hw3.ISASemantics.Instr -> hw3.ISASemantics.MachineState -> Prop)).
  nl.

  exc "ISASemantics.BasicBlock_step".
  pt 3.
  check_type @hw3.ISASemantics.BasicBlock_step
             ((hw3.ISASemantics.Program ->
               hw3.ISASemantics.MachineState ->
               hw3.ISASemantics.BasicBlock ->
               hw3.ISASemantics.MachineState -> hw3.ISASemantics.BasicBlock -> Prop)).
  nl.

  exc "ISASemantics.asmSwapACOK".
  pt 1.
  check_type @hw3.ISASemantics.asmSwapACOK
             ((forall (p : hw3.ISASemantics.Program) (a c d : nat) (f : bool) (m : hw3.ISASemantics.memory),
                  hw3.ISASemantics.BasicBlock_multistep p (hw3.ISASemantics.MState a c d f m)
                                                        (hw3.ISASemantics.Block "Entry" hw3.ISASemantics.asmSwapAC hw3.ISASemantics.Exit
                                                                                hw3.ISASemantics.Exit) (hw3.ISASemantics.MState c a c f m)
                                                        (hw3.ISASemantics.Block "Entry" nil hw3.ISASemantics.Exit hw3.ISASemantics.Exit))).
  ass.
  Print Assumptions hw3.ISASemantics.asmSwapACOK.
  nl.

  exc "ISASemantics.Instr_evalR_deterministic".
  pt 1.
  check_type @hw3.ISASemantics.Instr_evalR_deterministic
             ((forall (ms : hw3.ISASemantics.MachineState) (i : hw3.ISASemantics.Instr)
                 (ms1 ms2 : hw3.ISASemantics.MachineState),
                  hw3.ISASemantics.Instr_evalR ms i ms1 -> hw3.ISASemantics.Instr_evalR ms i ms2 -> ms1 = ms2)).
  ass.
  Print Assumptions hw3.ISASemantics.Instr_evalR_deterministic.
  nl.

  exc "ISASemantics.BasicBlock_step_deterministic".
  pt 2.
  check_type @hw3.ISASemantics.BasicBlock_step_deterministic
             ((forall (p : hw3.ISASemantics.Program) (ms ms1 ms2 : hw3.ISASemantics.MachineState)
                 (b b1 b2 : hw3.ISASemantics.BasicBlock),
                  hw3.ISASemantics.BasicBlock_step p ms b ms1 b1 ->
                  hw3.ISASemantics.BasicBlock_step p ms b ms2 b2 -> ms1 = ms2 /\ b1 = b2)).
  ass.
  Print Assumptions hw3.ISASemantics.BasicBlock_step_deterministic.
  nl.

  exc "ISASemantics.BasicBlock_value".
  pt 1.
  check_type @hw3.ISASemantics.BasicBlock_value
             ((hw3.ISASemantics.MachineState -> hw3.ISASemantics.BasicBlock -> Prop)).
  nl.

  exc "ISASemantics.value_not_same_as_normal_form".
  pt 2.
  check_type @hw3.ISASemantics.value_not_same_as_normal_form
             ((forall st : hw3.ISASemantics.MachineState,
                  exists b : hw3.ISASemantics.BasicBlock,
                    ~ hw3.ISASemantics.BasicBlock_value st b /\
                    hw3.ISASemantics.normal_form hw3.ISASemantics.EmptyProgram st b)).
  ass.
  Print Assumptions hw3.ISASemantics.value_not_same_as_normal_form.
  nl.

Abort.
