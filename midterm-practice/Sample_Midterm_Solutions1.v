(* Sample Midterm for CS 565 Do not redistribute!

As a refresher, here is a summary of the learning outcomes from the
first seven weeks of the course: The midterm will cover the first six
weeks-- the midterm will not cover denotational semantics. *)

(*  W1:
Write simple functional programs.
Represent the syntax of program as an inductive datatype.
Implement interpreters for a simple language as a recursive function.
Apply basic equational reasoning techniques in Coq.

W2:
Write higher-order functions.
Write polymorphic data types and functions.
Generate induction principles for algebraic data types.
Write proofs by induction in Coq.

W3:

Distinguish between propositions and proofs.
Define evidence of claims using inference rule notation.
Reason about richer propositions in Coq than simple equalities.
Write inductive propositions.

W4+5:

Define the (big-step) operational semantics of a simple imperative language.
Use big-step semantics to reason about nondeterministic languages.
Define the small-step operational semantics of a simple concurrent imperative language.

W6:

Model the semantics of dynamic dispatch in languages with inheritance.
Model the semantics of mutable references into a shared memory (the heap).

W7:

Formalize the syntax and semantics of the lambda calculus, a minimal language with first class functions.
Use the call-by-value semantics to evaluate lambda expressions.
Compare and contrast different evaluation strategies for the untyped lambda calculus.

W8:

Define the denotational semantics of a language.
Reason about the semantic equivalence of programs using denotational semantics.
Formalize the relationship between the big-step, small-step, and denotational semantics of a programming language.
Identify sufficient conditions for the existence of the fixpoint of a function, and use fixpoints to define the denotation of non-terminating programs. *)

(*********************************************************
  Part 1: Basic Functional Programming
 *********************************************************)

From LF Require Export Poly.
From LF Require Export Imp.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Lia.
Import ListNotations.

(* Define a polymorphic [remove] function that removes the nth element
   from a list. if the index is beyond the end of the list, the original
   list is returned. *)

Fixpoint remove {A : Type} (l : list A) (n : nat) : list A :=
  match n, l with
    0, a :: l' => l'
  | S n', a :: l' => a :: (remove l' n')
  | _, _ => nil
  end.

Example remove_ex1 : remove [1; 3; 5; 7] 2 = [1; 3; 7]. reflexivity. Qed.
Example remove_ex2 : remove [1; 3; 5; 7] 5 = [1; 3; 5; 7]. reflexivity. Qed.
Example remove_ex3 : remove [1; 3; 5; 7] 0 = [3; 5; 7]. reflexivity. Qed.
Lemma remove_2 {A} : forall (l : list A), remove l 0 = tl l. destruct l; reflexivity. Qed.


Module BSTs.
  (* Maps with numeric keys can be implemented with binary search trees
   (BSTs). Insert and lookup operations on BSTs take time proportional
   to the height of the tree.  If you don't recall BSTs or haven't
   seen them in a while, see Wikipedia. Define *)

  Inductive Tree (V : Type) : Type :=
  | leaf
  | node (l : Tree V) (key : nat) (value : V) (r : Tree V).

  Arguments leaf {V}.
  Arguments node {V} _ _ _ _.

  (* An example tree:

      4 -> "four"
      /        \
     /          \
  2 -> "two"   5 -> "five" *)


  Definition ex_tree : Tree string :=
    (node (node leaf 2 "two" leaf) 4 "four" (node leaf 5 "five" leaf))%string.
  Definition empty_tree {V : Type} : Tree V := leaf.

  (* A well-formed BST is one which is either a leaf or for every node
    in the tree key [k], all the values of the left subtree
    are less than [k] and all the values of the right subtree are
    greater than [k]. *)

  Notation "x =? y" := (Nat.eqb x y) : nat_scope.
  Notation "x <=? y" := (Nat.leb x y) : nat_scope.

  (* Define a lookup operation on well-formed BSTs.
   [lookup k t] is the value assocated with k in t, or None if k is not bound in t. *)
  Fixpoint lookup {V : Type} (k : nat) (t : @Tree V) : option V :=
    match t with
    | leaf => None
    | node lt k' v rt => if k =? k' then Some v
                         else if k <=? k' then lookup k lt
                              else lookup k rt
    end.

  (* Define an insertion operation on well-formed BSTs: insert k v t
   is the BST updates the value associated with k to v in t, adding it
   if the [k] is not present. *)

  Fixpoint insert {V : Type} (k : nat) (v : V) (t : Tree V) : Tree V :=
    match t with
    | leaf => node leaf k v leaf
    | node lt k' v' rt => if Nat.eqb k k' then node lt k v rt
                          else if k <=? k' then node (insert k v lt) k' v' rt
                               else node lt k' v' (insert k v rt)
    end.

  Open Scope string_scope.
  Example bst_ex1 :
    insert 5 "five" (insert 2 "two" (insert 4 "four" empty_tree)) = ex_tree.
  Proof. reflexivity. Qed.
  Example bst_ex2 : lookup 5 ex_tree = Some "five".
  Proof. reflexivity. Qed.
  Example bst_ex3 : lookup 3 ex_tree = None.
  Proof. reflexivity. Qed.

  (*********************************************************
  Part 2: Inductive Propositions
   *********************************************************)

  (** Note that a tree need not be a BST. Here is one example: *)

  Definition bad_tree : Tree string :=
    node (node leaf 5 "five" leaf) 4 "four" (node leaf 2 "two" leaf).

  (** The [insert] function you wrote above should never produce such
      a tree, but we can still construct manually. When we try to
      lookup [2] in that tree, we get the wrong answer, because
      [lookup] assumes [2] is in the left subtree: *)

  Example not_bst_lookup_wrong :
    lookup 2 bad_tree = None.
  Proof.
    reflexivity.
  Qed.

  (** So, let's formalize when a tree is well-formed. To do so, we first
    define a helper [ForallT] to express that idea that a predicate
    holds at every node of a tree: *)

  Fixpoint ForallT {V : Type} (P: nat -> V -> Prop) (t: Tree V) : Prop :=
    match t with
    | leaf => True
    | node lt k v rt => P k v /\ ForallT P lt /\ ForallT P rt
    end.

  (** Second, we define well-formedness of BSTs:

    - An empty tree is a BST.

    - A non-empty tree is a BST if all its left nodes have a lesser
      key, its right nodes have a greater key, and the left and right
      subtrees are themselves BSTs. *)

  Inductive BST {V : Type} : Tree V -> Prop :=
  | BST_leaf : BST leaf
  | BST_node : forall l x v r,
      ForallT (fun y _ => y < x) l ->
      ForallT (fun y _ => y > x) r ->
      BST l ->
      BST r ->
      BST (node l x v r).

  (** Let's check that [BST] correctly classifies a couple of example
    trees: *)

  Example is_BST_ex :
    BST ex_tree.
  Proof.
    unfold ex_tree.
    repeat (constructor).
  Qed.

  Example not_BST_ex :
    ~ BST bad_tree.
  Proof.
    unfold bad_tree. intros contra.
    inversion contra; subst. inversion H3; subst. lia.
  Qed.

  (** Prove that the empty tree is a BST. *)

  Theorem empty_tree_BST : forall (V : Type),
      BST (@empty_tree V).
  Proof.
    repeat constructor.
  Qed.

  (** Prove that [insert] produces a BST, assuming it is given one.

    Start by proving this helper lemma, which says that [insert]
    preserves any node predicate. Proceed by induction on [t]. *)

  Lemma ForallT_insert : forall (V : Type) (P : nat -> V -> Prop) (t : Tree V),
      ForallT P t -> forall (k : nat) (v : V),
        P k v -> ForallT P (insert k v t).
  Proof.
    induction t; simpl; intros.
    - repeat constructor; assumption.
    - destruct (k =? key)%nat eqn: ?.
      + destruct H as [? [? ?] ].
        simpl; repeat split; try assumption.
      + destruct (k <=? key)%nat eqn: ?; simpl.
        * destruct H as [? [? ?] ]; repeat split; try assumption.
          apply IHt1; assumption.
        * destruct H as [? [? ?] ]; repeat split; try assumption.
          apply IHt2; assumption.
  Qed.

  (** Now prove the main theorem. *)

  Theorem insert_BST : forall (V : Type) (k : nat) (v : V) (t : Tree V),
      BST t -> BST (insert k v t).
  Proof.
    intros ? ? ? ? H; induction H.
    - simpl; repeat constructor.
    - simpl; destruct (k =? x)%nat eqn: ?.
      + apply EqNat.beq_nat_true in Heqb. subst.
        constructor; try assumption.
      + apply EqNat.beq_nat_false in Heqb. subst.
        destruct (k <=? x)%nat eqn: ?; simpl.
        * constructor; try assumption.
          apply Compare_dec.leb_complete in Heqb0.
          apply ForallT_insert; try assumption.
          lia.
        * constructor; try assumption.
          apply Compare_dec.leb_complete_conv in Heqb0.
          apply ForallT_insert; try assumption.
  Qed.

End BSTs.

(*********************************************************
  Part 2.5: More Inductive Propositions
 *********************************************************)

(* Given the following definition of the "less-than-or-equal" relation
  on natural numbers, prove that the relation is reflexive and
  transitive and is symmetric.  *)

Require Import Coq.Init.Nat.

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(* (a) Reflexivity *)

Lemma le_refl : forall n, n <= n.
Proof.
  econstructor.
Qed.

(* (cr) lack of symmetry *)

Lemma le_not_sym : ~ forall m n, m <= n -> n <= m.
Proof.
  unfold not.
  intros.
  assert (2 <= 1).
  - apply H with (m := 1) (n := 2).
    apply le_S.
    apply le_refl.
  - inversion H0.
    subst.
    inversion H3.
Qed.

(* (b) Transitivity *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  generalize dependent m.
  induction H0.
  - intros; eauto.
  - intros.
    inversion H; subst.
    + constructor. assumption.
    + constructor.
      apply IHle.
      constructor.
      assumption.
Qed.

(* Write an inductively-defined proposition for establishing that
   a natural number is odd, and prove that it works for the following examples.  *)
Inductive odd : nat -> Prop :=
| odd1 : odd 1
| oddSS : forall m, odd m -> odd (2 + m).

Example odd_1 : odd 1.
Proof.
  apply odd1.
Qed.

Example odd_7 : odd 7.
Proof.
  repeat constructor.
Qed.

Example even_0 : ~odd 0.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.

Example even_14 : ~odd 14.
Proof.
  unfold not.
  intros H.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
Qed.

(* Prove that an even numbers is never odd: *)
Lemma even_not_not : forall (n : nat),
    even n = true ->
    ~ odd n.
Proof.
  unfold not; intros n ev_n odd_n.
  induction odd_n.
  - simpl in ev_n.
    inversion ev_n.
  - simpl in ev_n.
    apply IHodd_n.
    assumption.
Qed.

(* Now prove that an odd numbers is never even: *)
Lemma odd_not_even : forall (n : nat),
    odd n ->
    even n = false.
Proof.
  intros n odd_n.
  induction odd_n.
  - reflexivity.
  - simpl.
    rewrite IHodd_n.
    reflexivity.
Qed.

(*********************************************************
  Part 3: Big-Step Operational Semantics
 *********************************************************)

Module aevalR_extended.

(* ----------------------------------------------------------------- *)
(* Extending Arithmetic Expressions                                  *)

(* In this exercise, you need to add an exponentiation operation to
   our language of arithmentic expressions. Note that the exponent is
   a number, /not/ another number.

   A := X | N | A^N | A + A | A - A | A * A

  The big-step reduction rule for this operation is what you'd expect:

  st =[a]=>A m
  -----------------
  st =[a^n]=>A m^n *)


  Reserved Notation "st 'A=[' e ']=>' n" (at level 90, left associativity).
  Reserved Notation "st 'AE=[' e ']=>' n" (at level 90, left associativity).

  Inductive aexpExp : Type :=
  | AEPow (a1 : aexpExp) (n : nat)
  | AENum (n : nat)
  | AEId (x : string)
  | AEPlus (a1 a2 : aexpExp)
  | AEMinus (a1 a2 : aexpExp)
  | AEMult (a1 a2 : aexpExp).

  (* ----------------------------------------------------------------- *)

  (* The exponentiation function [pow] is in the standard library. *)
  Inductive aeevalR : state -> aexpExp -> nat -> Prop :=
  (* Add the reduction rule for exponents. *)
  | E_AEPow (st : state) (a : aexpExp) (n m: nat) :
      (st AE=[a]=> m) ->
      st AE=[AEPow a n]=> pow m n
  | E_AENum (st : state) (n : nat) :
      st AE=[AENum n]=> n
  | E_AEId (st : state) (x : string) :
      st AE=[AEId x]=> st x
  | E_AEPlus (st : state) (a1 a2 : aexpExp) (n1 n2 : nat) :
      (st AE=[a1]=> n1) ->
      (st AE=[a2]=> n2) ->
      st AE=[AEPlus a1 a2]=> n1 + n2
  | E_AEMinus (st : state) (a1 a2 : aexpExp) (n1 n2 : nat) :
      (st AE=[a1]=> n1) ->
      (st AE=[a2]=> n2) ->
      st AE=[AEMinus a1 a2]=> n1 - n2
  | E_AEMult (st : state) (a1 a2 : aexpExp) (n1 n2 : nat) :
      (st AE=[a1]=> n1) ->
      (st AE=[a2]=> n2) ->
      (st AE=[AEMult a1 a2]=> n1 * n2)

  where "st 'AE=[' a ']=>' n" := (aeevalR st a n) .

  (* Since the exponents are /numbers/, this extended language can
   always be translated into an equivalent 'vanilla' arithmetic
   expression. Write such a function. *)

  Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  Fixpoint powTimes (a : aexp) (n : nat) : aexp :=
    match n with
    | 0 => ANum 1
    | S n' => AMult a (powTimes a n')
    end.

  Fixpoint aexpExpToaexp (ae : aexpExp) : aexp :=
    match ae with
    | AEPow a1 n => powTimes (aexpExpToaexp a1) n
    | AENum n => ANum n
    | AEId x => AId x
    | AEPlus a1 a2 => APlus (aexpExpToaexp a1) (aexpExpToaexp a2)
    | AEMinus a1 a2 => AMinus (aexpExpToaexp a1) (aexpExpToaexp a2)
    | AEMult a1 a2 => AMult (aexpExpToaexp a1) (aexpExpToaexp a2)
    end.

  (* Now prove this elaboration is sound. *)

  Inductive aevalR : state -> aexp -> nat -> Prop :=
  | E_ANum (st : state) (n : nat) :
      st A=[ANum n]=> n
  | E_AId (st : state) (x : string) :
      st A=[AId x]=> st x
  | E_APlus (st : state) (a1 a2 : aexp) (n1 n2 : nat) :
      (st A=[a1]=> n1) ->
      (st A=[a2]=> n2) ->
      st A=[APlus a1 a2]=> n1 + n2
  | E_AMinus (st : state) (a1 a2 : aexp) (n1 n2 : nat) :
      (st A=[a1]=> n1) ->
      (st A=[a2]=> n2) ->
      st A=[AMinus a1 a2]=> n1 - n2
  | E_AMult (st : state) (a1 a2 : aexp) (n1 n2 : nat) :
      (st A=[a1]=> n1) ->
      (st A=[a2]=> n2) ->
      (st A=[AMult a1 a2]=> n1 * n2)

  where "st 'A=[' a ']=>' n" := (aevalR st a n) .

  Lemma powTimesCorrect : forall st a n m,
      (st A=[ a ]=> m) ->
      st A=[ powTimes a n ]=> m ^ n.
  Proof.
    induction n; simpl; intros.
    - constructor.
    - constructor; try assumption.
      apply IHn. assumption.
  Qed.

  Lemma aexpExpToaexpCorrect : forall ae st m,
      st AE=[ae]=> m -> st A=[aexpExpToaexp ae]=> m.
  Proof.
    intros.
    - induction H; simpl; try solve [constructor; assumption].
      apply powTimesCorrect; try assumption.
  Qed.

End aevalR_extended.

(***************************************************************
  Part 4: Small-Step Operational Semantics + The Lambda Calculus
 ***************************************************************)

From PLF Require Import Smallstep.
Module LCBool.

  (* -- Update the syntax and CBV semantics of the Lambda calculus with booleans. *)
  (* Let's add booleans to our
     lambda calculus!*)
  Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> tm -> tm
  | tm_true  : tm
  | tm_false  : tm
  | tm_ite  : tm -> tm -> tm -> tm.

  (* We define three things: true and false constructors, and an
  if then else expression for doing case analysis on bollenas *)

Declare Custom Entry stlc.
Notation "<<{ e }>>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "'if' x 'then' y 'else' z" :=
  (tm_ite x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).
Notation "\ x , y" :=
  (tm_abs x y) (in custom stlc at level 90, x at level 99,
                     y custom stlc at level 99,
                     left associativity).

Coercion tm_var : string >-> tm.

(** Some more notation magic to set up the concrete syntax, as we did
    in the [Imp] chapter... *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition w : string := "w".
Definition t : string := "t".
Definition f : string := "f".
Definition s : string := "s".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold w : core.
Hint Unfold s : core.


(** Some examples... *)

(* ################################################################# *)
(** * Operational Semantics *)

(* ================================================================= *)
(** ** Values *)

(** true and false are now values: *)
Inductive value : tm -> Prop :=
  | v_abs : forall x t1,
      value <<{ \x, t1}>>
  | v_true :
      value <<{true}>>
  | v_false :
      value <<{false}>>.

Hint Constructors value : core.

(* ================================================================= *)
(** ** LC+Bool Programs *)

(* ================================================================= *)
(** ** Substitution *)

(** Can you fill in the rest of the substitution function?

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x, t)         = \x:T, t
       [x:=s](\y, t)         = \y:T, [x:=s]t         if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)

*)

(** ... and formally: *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <<{\y, t1}>> =>
      if String.eqb x y then t else <<{\y, [x:=s] t1}>>
  | <<{t1 t2}>> =>
    <<{([x:=s] t1) ([x:=s] t2)}>>
  | <<{true}>> => <<{true}>>
  | <<{false}>> => <<{false}>>
  | <<{if t1 then t2 else t3}>> =>
      <<{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** For example... *)

(* ================================================================= *)
(** ** Reduction *)

(**
                               value v2
                     ---------------------------                     (ST_AppAbs)
                     (\x,t1) v2 --> [x:=v2]t1

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'

                           t1 --> t1'
               --------------------------
               iter t1 zero=> cz succ=> cs --> iter t1' zero=> cz succ=> cs

               --------------------------
          iter tm_zero zero=> cz succ=> cs --> cz

              ----------------------------
          iter (tm_succ t1) z zero=> cz succ=> cs -->
          cs (iter t1 z zero=> cz succ=> cs)
*)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x t1 v2, (* <- beta reduction *)
         value v2 ->
         <<{(\x, t1) v2}>> --> <<{ [x:=v2]t1 }>>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <<{t1 t2}>> --> <<{t1' t2}>>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <<{v1 t2}>> --> <<{v1  t2'}>>

  | ST_IfTrue : forall t1 t2,
      <<{if true then t1 else t2}>> --> t1
  | ST_IfFalse : forall t1 t2,
      <<{if false then t1 else t2}>> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <<{if t1 then t2 else t3}>> --> <<{if t1' then t2 else t3}>>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* Write lambda expressions to calculate the and / or / not of booleans. *)

Definition notB : tm := <<{\x, if x then false else true}>>.
Definition andB : tm := <<{\x, \y, if x then y else false}>>.
Definition orB : tm := <<{\x, \y, if x then true else y}>>.

(* That was exhausting, and rather mechanical. Can we do better?  Yes,
   proof automation to the rescue!  note that at each step, only one
   evaluation rule applies. To know if a rule applies, we just need to
   look at the shape of the goal, and (some of the time), tell if a
   subterm is a value.  *)
Ltac next_step :=
  first [apply ST_AppAbs; solve [repeat constructor]
        | apply ST_App2; solve [repeat constructor]
        | apply ST_App1; next_step
        | apply ST_IfTrue
        | apply ST_IfFalse
        | apply ST_If; next_step ].

Ltac normalize_lambda :=
  repeat (eapply multi_step;
          [ next_step | ]); simpl.

Example notB_ex :
  <<{notB true}>> -->* <<{false}>>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example andb_ex :
  <<{notB (andB true false)}>> -->* <<{true}>>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example orb_ex :
  <<{orB (orB true false) (notB (andB true false))}>> -->* <<{true}>>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

Example andb_ex2 :
  <<{orB (andB true (andB true (andB true (andB true false))))
         (andB true (andB true (andB true (andB true true))))}>> -->* <<{true}>>.
Proof.
  normalize_lambda. simpl.
  apply multi_refl.
Qed.

End LCBool.
