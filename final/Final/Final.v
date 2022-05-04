(** !!! Due date: 05/06/2022 by 6:00PM !!! **)
(*** CS 565 Final Exam ***)

(*****************************************************************

    Your Name: *FILL IN HERE*

 *****************************************************************

  There are 23 questions and one bonus question below; please fill in
  all the places that say *FILL IN HERE*. There are 120 points
  possible, plus an additional 5 bonus points.

  As stated on the syllabus, this final is a cumulative assessment of
  individual students' learning over the semester, and you should NOT
  discuss this exam with their classmates. Any clarifying questions
  should be asked via a PRIVATE post on piazza.

  Note that the standard late policy does not apply here. If you
  encounter a problem that could cause you to not submit the final
  before the deadline of 6:00PM on 05/06/2022, let the professor and
  the TAs know IMMEDIATELY!

  You are allowed to use all theorems and exercises in 'Software
  Foundations', (regardless of whether they are proved or not). You
  can also use any lemmas or theorems in Coq's Standard Library.

  Before working on the final, open '_CoqProject' and replace the line
  '-R ../../plf PLF' with '-R
  /path/to/your/programming/language/foundations/directory PLF', as
  you have done on all the homeworks. Make sure you have run `make` in
  your PLF directory before beginning.

  Like the fourth homework, the denotational semantics section of the
  final requires some definitions from [Denotational.v] and
  [Fixpoints.v], which are included with the final. Before you start
  working on the homework, make sure you build those files by running
  'make' in the DenotationalSemantics directory, after updating the
  '_CoqProject' in that directory to point to your copy of PLF.

  Some IDEs have trouble with the unicode notations in [Fixpoints.v]
  and [Denotational.v]. If you encounter a weird lexer error, please
  download the DenotationalSemantics_no_notations archive from
  Brightspace and replace the copies of these two files in the
  DenotationalSemantics subdirectory with their unicode-free
  counterparts.  Note that the only differences between the two files
  are the notations used for set membership (∈) and subset (⊆), and
  that the choice of notations shouldn't affect your solution.


  Good luck!

   ======================= Submission Guidelines =======================

    In order for the grading scripts to work correctly (and
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
        no error. If for some reason 'make' always fails in
        your environment, inform the TA ASAP.
      - Only hand in [Final.v]. Please do not submit auxiliary files,
        such as [Makefile] or [Final_test.v].

        The final is accompanied by a _test script_ ([Final_test.v]).
        You may should use it to double-check that your file is
        well-formed before handing it in by running the 'make' command.

     For full credit, make sure you check the following:
      - The "Assumptions" section for each exercise outputted by
        'make' (or the test script) contains only "Closed under the
        global context", but not "Axioms: ...". If some axioms are
        allowed as per instructions, make sure only those allowed
        axioms are printed out.
      - Before proving a theorem, make sure that the relevant
        definitions are correct first. If your definitions are wrong,
        you will not get full credit for the proof. For example, if
        the definition of [erase] is wrong, then every
        exercise involving [erase] (e.g., [erase_preserves_semantics]) will
        be impacted.
      - Be aware that even if 'make' prints no error or axioms, you
        may still lose points, because some exercises are manually
        graded.

    We are using Brightspace for submission. If you submit multiple
    versions of the final, you may notice that they are given
    different names.  This is fine: The most recent submission is the
    one that will be graded.

  Good luck!

 *********************************************************)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
From PLF Require Hoare2.
From PLF Require Stlc.
From DS Require Fixpoints.
From DS Require Denotational.
From Top Require UntypedLC.
Import Nat.

(**********************************************************************************************
  Part 1: Denotational Semantics and Inductively Defined Propositions               (30 points)
 **********************************************************************************************)

Module DenotationalSemantics.
  Import Imp.
  Import Maps.

(* Inductively Defined Propositions               (10 points) *)

  (* The following inductively defined proposition captures when a
     variable appears in an arithmetic expression. *)
  Inductive AppearsIn : string -> aexp -> Prop :=
  | AppearsInID : forall (x : string), AppearsIn x (AId x)
  | AppearsInPlusL : forall (y : string) (a1 a2 : aexp),
      AppearsIn y a1 -> AppearsIn y (APlus a1 a2)
  | AppearsInPlusR (x : string) (a1 a2 : aexp) (H : AppearsIn x a2)
    : AppearsIn x (APlus a1 a2)
  | AppearsInMultL (x : string) (a1 a2 : aexp) (_ : AppearsIn x a1)
    : AppearsIn x (AMult a1 a2)
  | AppearsInMultR : forall (x : string) (a1 a2 : aexp),
      AppearsIn x a2 -> AppearsIn x (AMult a1 a2)
  | AppearsInMinusL : forall (x : string) (a1 a2 : aexp),
      AppearsIn x a1 -> AppearsIn x (AMinus a1 a2)
  | AppearsInMinusR : forall (x : string) (a1 a2 : aexp),
      AppearsIn x a2 -> AppearsIn x (AMinus a1 a2).

  #[local] Hint Constructors AppearsIn : core.

  (** Question 1 [NotAppearsIn] (5 points) *)
  (* Define another inductively defined proposition that captures when
     a variable does /not/ appear in an arithmetic expression: *)
  Inductive NotAppearsIn : string -> aexp -> Prop :=
  | NotAppearsInNum : forall x n, NotAppearsIn x (ANum n)
  | NotAppearsInID : forall x y, x <> y -> NotAppearsIn x (AId y)
  | NotAppearsInPlus : forall x a1 a2,
      NotAppearsIn x a1 -> NotAppearsIn x a2 -> NotAppearsIn x (APlus a1 a2)
  | NotAppearsInMult : forall x a1 a2,
      NotAppearsIn x a1 -> NotAppearsIn x a2 -> NotAppearsIn x (AMult a1 a2)
  | NotAppearsInMinus : forall x a1 a2,
      NotAppearsIn x a1 -> NotAppearsIn x a2 -> NotAppearsIn x (AMinus a1 a2).

  (** Question 2 [Not_AppearsIn_impl_NotAppearsIn] (5 points) *)
  (* Show that when a variable [x] does not appear in an arithmetic
     expression [a], we can prove that [x] does not appear [a].  (The
     converse direction should hold as well, but you do not need to
     show that). *)
  Lemma Not_AppearsIn_impl_NotAppearsIn : forall (x : string) (a : aexp),
      ~ AppearsIn x a -> NotAppearsIn x a.
  Proof.
    intros.
    induction a.
    - constructor.
    - apply NotAppearsInID. intro. apply H. rewrite H0. eauto.
    - apply NotAppearsInPlus; eauto.
    - apply NotAppearsInMinus; eauto.
    - apply NotAppearsInMult; eauto.
  Qed.

  (* Denotational Semantics              (20 points) *)
  Import Fixpoints.
  Import Denotational.

  (** Question 3 [if_shift] (5 points) *)
  (* Use the denotational semantics of commands to show that the
     following two commands are equivalent: *)
  Theorem if_shift : forall b c1 c2 c3,
    <{ if b then c1 else c2 end; c3 }> ==C <{ if b then c1; c3 else c2; c3 end }>.
  Proof.
    split; intros (?, ?) ?; simpl in *; In_inversion; In_intro; eauto.
  Qed.

  (* Question 4 [three_seq_equiv] (10 points) *)
  (* The fact that command equivalence is a true equivalence (i.e. a
     transitive, symmetric, and reflexive relation) allows us to
     reason about equivalence of commands via equivalences of their
     subterms. Use these properties (see com_eqv_trans, etc. in
     Denotational.v) to prove the following fact.

     Hint 1: writing out this equational proof on paper can help you
     identify the intermediate programs to use with [com_eqv_trans]:
     (c1; c2) == (c1'; c2) == (c1'; c2')

     Hint 2: The [seq_assoc] lemma in Denotational.v will also be
     useful here. *)

  Theorem seq_assoc :
    forall c1 c2 c3,
      <{(c1; c2); c3}> ==C <{c1; (c2; c3)}>.
  Proof.
    split; intros (?, ?) ?; simpl in *; In_inversion; In_intro; eauto.
  Qed.

  Theorem three_seq_equiv
    : forall (c1 c2 c3 c1' c2' c3' : com),
      <{c1; c2}> ==C <{c1'; c2'}> ->
      <{c2; c3}> ==C <{c2; c3'}> ->
      <{c1; c2; c3}> ==C <{c1'; c2'; c3'}>.
  Proof.
    split; intros (?, ?) ?.
    - apply (seq_eq_cong c1) with (x:=(<{c2; c3'}>)) in H1.
      apply seq_assoc in H1.
      apply (seq_eq_cong <{c1'; c2'}>) with (x:=c3') in H1.
    -- In_inversion. apply seq_assoc. In_intro. assumption.
    -- symmetry. assumption.
    -- reflexivity.
    -- reflexivity.
    -- symmetry. assumption.
    - apply (seq_eq_cong c1) with (x:=(<{c2; c3'}>)).
    -- reflexivity.
    -- symmetry. assumption.
    -- apply seq_assoc.
       apply (seq_eq_cong <{c1'; c2'}>) with (x:=c3').
    --- symmetry. assumption.
    --- reflexivity.
    --- In_intro. apply seq_assoc in H1. In_inversion. assumption.
  Qed.

  (* If a variable does not appear in an expression assigned to it, it
     is safe to inline that variable in an assignment statement that
     immediately follows it: *)
  Fixpoint subst_var (x : string) (a : aexp) (a1 : aexp) : aexp :=
    match a1 with
    | ANum n => n
    | AId y => if eqb x y then a else y
    | <{ a1 + a2}> => <{ (subst_var x a a1) + (subst_var x a a2)}>
    | <{ a1 - a2}> => <{ (subst_var x a a1) -  (subst_var x a a2) }>
    | <{ a1 * a2 }> => <{ (subst_var x a a1) * (subst_var x a a2) }>
    end.

  (*Bonus Question [subst_eqv] (5 BONUS points) *)
  (* Prove that it is, in fact, safe to inline a variable in this
     manner.*)

  Theorem subst_eqv : forall (x y : string) (a1 a2 : aexp),
      NotAppearsIn x a1 ->
      <{ x := a1; y := a2}> ==C <{ x := a1; y := subst_var x a1 a2}>.
  Proof.
    intros.
    split; intros (?, ?) ?.
    - induction a2.
    -- simpl in *. assumption.
    -- simpl in *. destruct (x =? x0)%string eqn:eq.
    --- apply eqb_eq in eq.
        In_inversion; subst. In_intro.
        eapply ex_intro.
        split.
    ---- eapply ex_intro. split; eauto.
    ---- eapply ex_intro. split.
    ----- induction H.
    ------ eauto.
    ------ simpl in *. eapply t_update_neq in H.
           rewrite H. assumption.
    ------ simpl in *.
  Admitted.

  (* Question 5 [three_subst_equiv] (5 points) *)
  (* Use [subst_eqv] to prove that it is safe to do multiple such
     inlinings at once.  You can use the admitted of [subst_eqv] in
     the proof of [three_subst_equiv] without any penalty. *)
  Theorem three_subst_eqv : forall (x y z : string) (a1 a2 a3 : aexp),
      NotAppearsIn x a1 ->
      NotAppearsIn y a2 ->
      <{ x := a1; y := a2; z := a3}> ==C
      <{ x := a1; y := subst_var x a1 a2; z := subst_var y a2 a3 }>.
  Proof.
    split; intros (?, ?) ?.
    - apply seq_assoc.
      apply (seq_eq_cong <{ x := a1; y := a2 }>) with (x:=(<{ z := (subst_var y a2 a3) }>)).
    -- apply subst_eqv. assumption.
    -- reflexivity.
    -- apply seq_assoc.
       apply (seq_eq_cong <{ x := a1 }>) with (x:=(<{ y := a2; z := a3 }>)).
    --- reflexivity.
    --- apply subst_eqv. assumption.
    --- assumption.
    - apply (seq_eq_cong <{ x := a1 }>) with (x:=(<{ y := a2; z := (subst_var y a2 a3) }>)).
    -- reflexivity.
    -- symmetry. apply subst_eqv. assumption.
    -- apply seq_assoc.
       apply (seq_eq_cong <{ x := a1; y := (subst_var x a1 a2) }>) with (x:=(<{ z := (subst_var y a2 a3) }>)).
    --- symmetry. apply subst_eqv. assumption.
    --- reflexivity.
    --- apply seq_assoc. assumption.
  Qed.

End DenotationalSemantics.

(*********************************************************
  Part 2: Axiomatic Semantics                  (20 points)
 *********************************************************)

Module AxiomaticSemantics.

  Import Hoare2.
  Import Hoare.
  Import Maps.

  (* Do not remove the following line! *)
  Opaque hoare_triple.

  (* Prove that the validity of the following Hoare triples using the
     Hoare rules.

     Hint: remember that you can use the command [Search XX] to find
     facts about the identifier XX. *)

  (* Question 6 [Hoare_Q1] (5 points) *)
  Theorem Hoare_Q1 :
    forall (m : nat),
      {{X <= Y}}
      <{Z := X * m;
        W := Y * m}>
      {{Z <= W}}.
  Proof.
    intros.
    apply hoare_seq with (Q := (Z <= Y * m)%assertion).
    - eapply hoare_consequence_pre.
    -- apply hoare_asgn.
    -- assn_auto.
    - eapply hoare_consequence_pre.
    -- apply hoare_asgn.
    -- unfold "->>". intros. apply mul_le_mono_r. assumption.
  Qed.

  (* Question 7 [Hoare_Q2] (5 points) *)
  Lemma Hoare_Q2 :
    {{True}}
    <{if Y <= 10 then Y := Y + 1 else Y := 10 end;
      X := Y}>
    {{X <= 11 }}.
  Proof.
    apply hoare_seq with (Q := (Y <= 11)%assertion).
    - eapply hoare_consequence_pre.
    -- apply hoare_asgn.
    -- assn_auto.
    - apply hoare_if.
    -- eapply hoare_consequence_pre.
    --- apply hoare_asgn.
    --- verify_assn.
    -- eapply hoare_consequence_pre.
    --- apply hoare_asgn.
    --- assn_auto.
  Qed.

  (* Question 8 [Hoare_Q3] (10 points) *)
  Example Hoare_Q3 :
    forall (m n : nat),
      {{X = 0 /\ Y = 0}}
      <{ while (~ Y = n) do
                 X := X + m;
                 Y := Y + 1 end }>
      {{X = m * n }}.
  Proof.
    intros.
    eapply hoare_consequence with (P' := (X = m * Y)%assertion).
    - eapply hoare_while.
      eapply hoare_consequence_pre.
    -- eapply hoare_seq.
    --- apply hoare_asgn.
    --- apply hoare_asgn.
    -- verify_assn.
    - verify_assn.
    - verify_assn.
  Qed.

End AxiomaticSemantics.

(***************************************************************
  Part 3: Operational Semantics + Functional Programming      (25 points)
 **************************************************************)

Module TypeErasure.

  Import Stlc.
  Import UntypedLC.
  Import STLC.

  (* Recall that the untyped lambda calculus is simply the STLC with
   no typing annotations on its lambda abstractions.  A type erasure
   function for the simply typed lambda calculus (with booleans) takes
   an STLC expression as input and outputs a untyped lambda calculus
   (with boolean) expression by dropping the type annotations from any
   lambda abstractions according to the following rules: *)

   (* erase x = x
   erase (t1 t2) = (erase t1) (erase t2)
   erase (λx : T.t) = λx. (erase t)
   erase true = true
   erase false = false
   erase (if tc then tt else te) = if (erase tc) then (erase tt) else (erase te) *)

   (* Question 10 (5 points): *)

  (* Define such a type erasure function below.

     The notations for writing pretty-printed versions of the simply typed and
     untyped lambda calculus are <{ t }> and <<{ t }>>, respectively.

     You may need to explicitly use the constructors of untyped lambda
     calculus (e.g. [Utm_app]) in your definition if Coq gives you
     parsing errors when using those notations. *)

  Fixpoint erase (t : tm) : Utm :=
    match t with
    | tm_var x => Utm_var x
    | <{t1 t2}> => Utm_app (erase t1) (erase t2)
    | <{\y:T, t1}> => Utm_abs y (erase t1)
    | <{true}> => <<{true}>>
    | <{false}> => <<{false}>>
    | <{if t1 then t2 else t3}> => Utm_ite (erase t1) (erase t2) (erase t3)
    end.

  (* Question 11 [erase_value] (2 points)

     Prove that erasing the type from a typed STLC value results in an
     untyped LC value.  *)

  Lemma erase_value :
    forall v, value v -> Uvalue (erase v).
  Proof.
    intros.
    induction H; constructor.
  Qed.

  (* Question 12 [erase_subst] (3 points)
     Prove that erasure distributes over substitution: *)

  Lemma erase_subst
    : forall x v t,
      Usubst x (erase v) (erase t) = erase (subst x v t).
  Proof.
    induction t; simpl.
    - destruct (Maps.eqb_string x0 s); reflexivity.
    - rewrite IHt1, IHt2. reflexivity.
    - destruct (Maps.eqb_string x0 s).
    -- reflexivity.
    -- rewrite IHt. reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite IHt1, IHt2, IHt3. reflexivity.
  Qed.

  (* The type erasure function should preserve the semantics of any
   expression it's applied to. In other words: an erased lambda term should
   only evaluate to erased versions of values that the original term
   could evaluate to.

  More formally: for all STLC terms t, for any term t′ that t
  evaluates to, the erasure of t evaluates to the erasure of t′ under
  the evaluation relation for the untyped lambda calculus. That is,
  for all t and t′, t -->* t′ implies erase t -->* erase t′. *)

  (* Questions 13 + 14 [erase_preserves_semantics] (5 points) + (10
  points) State (Q13) and prove (Q14) a lemma,
  [erase_preserves_semantics] showing that type-erasure is semantics
  preserving.

   Note that the notation for the single and multi step relations for
  the untyped lambda calculus are [t -U-> t'] and [t -U->* t'],
  respectively. *)

  Lemma erase_preserves_semantics_single :
    forall t t', t --> t' -> (erase t) -U-> (erase t').
  Proof.
    intros.
    induction H; simpl.
    - rewrite <- erase_subst.
      apply STU_AppAbs.
      apply erase_value in H.
      assumption.
    - apply STU_App1. assumption.
    - apply STU_App2.
    -- apply erase_value. assumption.
    -- assumption.
    - apply STU_IfTrue.
    - apply STU_IfFalse.
    - apply STU_If. assumption.
  Qed.

  Lemma erase_preserves_semantics :
    forall t t', t -->* t' -> (erase t) -U->* (erase t').
  Proof.
    intros.
    induction H.
    - constructor.
    - apply erase_preserves_semantics_single in H.
      eapply Smallstep.multi_step; eassumption.
  Qed.

End TypeErasure.

(***************************************************************
  Part 3: Type Systems                               (45 points)
 **************************************************************)

Module STLC_Extensions.
  Import Smallstep.
  Import Maps.

  (*For this part of the final, you are to augment the formalization
  of the simply-typed lambda calculus and its metatheory with option
  types. Option types have two constructors: Some t, where [t] is a
  term, and None.  *)

  (* One use case for this type is to augment the return type of a
     function with a special error value. Division, for example, can
     use none to signal divide by zero errors: divide m n = if n = 0
     then None else (Some .....) *)

  (* In BNF Notation, the syntax for the types of this language is:
     T := T -> T | bool | Option T

     and the syntax for the language itself is:

       t ::=
       | x                    (variable)
       | \x : T,t                 (abstraction)
       | t t                  (application)
       | true                 (constant true)
       | false                (constant false)
       | if t then t else t   (conditional)

       | Some t                (Some [tm_some])
       | None T                (None [tm_none])
       | case t of             (case [tm_case])
            Some x => t
          | None => t

       (The only difference from the untyped version is the typing
       annotation on lambda abstractions. *)

  Inductive ty : Type :=
  (* Pure STLC *)
  | Ty_Arrow : ty -> ty -> ty
  (* Booleans: *)
  | Ty_Bool  : ty
  (* Type Variables *)
  | Ty_Var : string -> ty
  (* Options *)
  | Ty_Option : ty -> ty.

  Inductive tm : Type :=
  (* Pure STLC *)
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  (* Booleans *)
  | tm_true  : tm
  | tm_false  : tm
  | tm_ite  : tm -> tm -> tm -> tm
  (* Options *)
  | tm_some : tm -> tm
  | tm_none : ty -> tm
  | tm_case : tm -> string -> tm -> tm -> tm.

  Declare Custom Entry stlc_ty.

  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
  Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
  Notation "'if' x 'then' y 'else' z" :=
    (tm_ite x y z) (in custom stlc at level 89,
                       x custom stlc at level 99,
                       y custom stlc at level 99,
                       z custom stlc at level 99,
                       left associativity).
  Notation "'true'"  := tm_true (in custom stlc at level 0).
  Notation "'false'"  := tm_false (in custom stlc at level 0).
  Notation "'some' tm"  := (tm_some tm) (in custom stlc at level 0,
                                            tm custom stlc at level 0).
  Notation "'none' T"  := (tm_none T) (in custom stlc at level 0,
                                          T custom stlc_ty at level 0).

Notation "'case' t0 'of' '|' 'some' x1 '=>' t1 '|' 'none' '=>' t2" :=
  (tm_case t0 x1 t1 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).

Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).

Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0).
Notation "Option T" := (Ty_Option T) (in custom stlc_ty at level 50, right associativity).

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(* Question 15 [subst] (5 points):
   Update the substitution function to handle options.
 *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* Booleans *)
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  (* Options *)
  | <{some t}> =>
      <{some ([x:=s] t)}>
  | <{none T}> =>
      <{none T}>
  | <{case t of | some y => t1 | none => t2}> =>
      if eqb_string x y then
        <{case ([x:=s] t) of | some y => t1 | none => ([x:=s] t2)}>
      else
        <{case ([x:=s] t) of | some y => ([x:=s] t1) | none => ([x:=s] t2)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* Values in this calculus are either lambda abstractions, boolean
   literals, [none], or [some v] where [v] is also a value.  *)

(* Question 16 [value] (2 points):
   Define a proposition capturing when a term is a value.
 *)
Inductive value : tm -> Prop :=
  (* Pure STLC *)
  | v_abs : forall x T11 t12,
      value <{\x : T11, t12}>
  (* Booleans *)
  | v_true : value <{true}>
  | v_false : value <{false}>
  (*Options*)
  | v_some : forall t, value t -> value <{some t}>
  | v_none : forall T, value <{none T}>.

#[local] Hint Constructors value : core.

(* Here are the Call-By-Value reduction rules for Options.

                    t1 --> t1'
             -------------------------                                [ST_some]
               some t1 --> some t1'

                     t1 --> t1'
             -------------------------                                [ST_Case]
               case t1 of | some y => t2 | none => t3 -->
                  case t1' of | some y => t2 | none => t3

                    value v1
             -------------------------                                [ST_CaseSome]
             case (some v1) of | some y => t2 | none => t3 --> [y := v1]t2


             -------------------------                                [ST_CaseNone]
               case (none T) of | some y1 => t2 | none => t3 --> t3

 *)

(* Question 17 [step] (3 points)
   Add these rules to the step relation. *)

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* Booleans *)
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  (* Options *)
  | ST_Some : forall t1 t1',
      t1 --> t1' ->
      <{some t1}> --> <{some t1'}>
  | ST_Case : forall t1 t1' t2 t3 y,
      t1 --> t1' ->
      <{case t1 of | some y => t2 | none => t3}>
        --> <{case t1' of | some y => t2 | none => t3}>
  | ST_CaseSome : forall t2 t3 y v1,
      value v1 ->
      <{case (some v1) of | some y => t2 | none => t3}> --> <{[y := v1] t2}>
  | ST_CaseNone : forall t2 t3 y T,
      <{case (none T) of | some y => t2 | none => t3}> --> t3

  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

#[local] Hint Constructors step : core.

(* ----------------------------------------------------------------- *)
(** *** Typing *)


  (** Here are the typing rules for options:

                          Gamma |- t :  T
                     ----------------------------                       (T_Inl)
                     Gamma |- Some t : Option T

                     ----------------------------                       (T_Inr)
                     Gamma |- None T : Option T

                       Gamma |- t0 : Option T
                       Gamma , x:T |- t1 : T1
                       Gamma |- t2 : T1
         ---------------------------------------------------           (T_Case)
         Gamma |- case t0 of Some x => t1 | None => t2 : T1
   *)

Definition context := partial_map ty.

(** Question 18 [has_type] (2 points)
    Add these rules to the typing relation: *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
    (x |-> T2 ; Gamma) |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  (* Booleans *)
  | T_True : forall Gamma,
      Gamma |- true \in Bool
  | T_False : forall Gamma,
      Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- if t1 then t2 else t3 \in T1
  (* Options *)
  | T_Inl : forall Gamma t T,
      Gamma |- t \in T ->
      Gamma |- some t \in (Option T)
  | T_Inr : forall Gamma T,
      Gamma |- none T \in (Option T)
  | T_Case : forall Gamma t0 t1 t2 x T T1,
      Gamma |- t0 \in (Option T) ->
      (x |-> T ; Gamma) |- t1 \in T1 ->
      Gamma |- t2 \in T1 ->
      Gamma |- case t0 of | some x => t1 | none => t2 \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

#[local] Hint Constructors has_type : core.

(* ################################################################# *)
(* Metatheory *)
(* We can now prove that our type system is sound. *)

(** * Canonical Forms *)

Lemma canonical_forms_bool : forall t,
  empty |- t \in Bool ->
  value t ->
  t = <{true}> \/ t = <{false}>.
Proof.
  intros t HT HVal.
  destruct HVal; eauto;
    inversion HT; eauto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal; inversion HT; subst.
  exists x, t12. reflexivity.
Qed.

(* Question 19 [canonical_forms_option] (3 points)
   Prove that a option value is either [some v] or [none]. *)
Lemma canonical_forms_option : forall t T,
  empty |- t \in (Option T) ->
  value t ->
  t = <{none T}> \/ exists v, value v /\ t = <{some v}>.
Proof.
  intros.
  destruct H0; inversion H; eauto.
Qed.

(* ################################################################# *)
(** * Progress *)

(** Question 20 [progress] (10 points)
    Prove progress for this calculus. *)

Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction H; intros HeqGamma; subst; eauto.
  - discriminate H.
  - destruct IHhas_type1; eauto.
  -- destruct IHhas_type2; eauto.
  --- destruct H1; try solve_by_invert. eauto.
  --- destruct H2; eauto.
  -- destruct H1; eauto.
  - destruct IHhas_type1; eauto.
  -- destruct t1; try solve_by_invert; eauto.
  -- destruct H2. eauto.
  - destruct IHhas_type; eauto. destruct H0. eauto.
  - destruct t0;
    try solve_by_invert;
    destruct IHhas_type1;
    eauto;
    inversion H2;
    eauto.
Qed.

(* ################################################################# *)
(** * Preservation *)

Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
  intros; econstructor; eauto using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* Question 21 [substitution_preserves_typing] (10 points)
   Prove the substitution lemma for this calculus. *)
Lemma substitution_preserves_typing : forall Gamma x U t v T,
    (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros.
  generalize dependent Gamma.
  generalize dependent T.
  induction t0; intros; inversion H; subst; simpl; eauto.
  - destruct (eqb_stringP x s); subst.
  -- rewrite update_eq in H3.
     injection H3 as H3.
     subst.
     apply weakening_empty.
     assumption.
  -- apply T_Var. rewrite update_neq in H3; assumption.
  - destruct (eqb_stringP x s); subst; apply T_Abs.
  -- rewrite update_shadow in H6. assumption.
  -- apply IHt0. rewrite update_permute; auto.
  - destruct (eqb_stringP x s); subst; eapply T_Case; eauto.
  -- rewrite update_shadow in H8. assumption.
  -- apply IHt0_2. rewrite update_permute; auto.
Qed.

(* Question 22 [preservation] (5 points)
   Prove preservation for this calculus. *)
Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t --> t'  ->
  empty |- t' \in T.
Proof.
  intros t t' T HT. generalize dependent t'.
    remember empty as Gamma.
    induction HT; intros; subst; try solve [inversion H; subst; eauto];
    inversion H; subst; eauto;
    eapply substitution_preserves_typing; inversion HT1; eauto.
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

(* Question 23 [soundness] (5 points)
   At long last, prove that the type system for this extension of the STLC is sound. *)
Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  unfold stuck, normal_form, not.
    intros.
    destruct H1.
    induction H0.
    - apply progress in H. destruct H; eauto.
    - apply IHmulti; try eauto.
    -- eapply preservation; eauto.
Qed.

End STLC_Extensions.
