(* Sample Midterm for CS 565 Do not redistribute!

As a refresher, here is a summary of the learning outcomes from the
first seven weeks of the course: The midterm will cover the first seven
weeks-- the midterm will not cover denotational semantics. *)

(* W1:
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

From LF Require Export Imp.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Omega.
From Coq Require Import Lia.
Import ListNotations.

(** Exercise:  *)
(* Define a polymorphic [remove] function that removes the nth element
   from a list. if the index is beyond the end of the list, the original
   list is returned. *)
Fixpoint remove {A : Type} (l : list A) (n : nat) : list A := l.

(** Exercise:  *)
Example remove_ex1 : remove [1; 3; 5; 7] 2 = [1; 3; 7].
  (* FILL IN HERE *)
Admitted.

(** Exercise:  *)
Example remove_ex2 : remove [1; 3; 5; 7] 5 = [1; 3; 5; 7].
  (* FILL IN HERE *)
Admitted.

(** Exercise:  *)
Example remove_ex3 : remove [1; 3; 5; 7] 0 = [3; 5; 7].
  (* FILL IN HERE *)
Admitted.

(** Exercise:  *)
Lemma remove_2 {A} : forall (l : list A), remove l 0 = tl l.
  (* FILL IN HERE *)
Admitted.

Module BSTs.
  (* Maps with numeric keys can be implemented with binary search trees
   (BSTs). Insert and lookup operations on BSTs take time proportional
   to the height of the tree.  If you don't recall BSTs or haven't
   seen them in a while, see Wikipedia. *)

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

  (** Exercise: *)
  (* Define a lookup operation on well-formed BSTs.
   [lookup k t] is the value assocated with k in t, or None if k is not bound in t. *)
  Fixpoint lookup {V : Type} (k : nat) (t : @Tree V) : option V :=
    (* Replace this line with your definition. *)  None.

  (** Exercise: *)
  (* Define an insertion operation on well-formed BSTs: insert k v t
   is the BST updates the value associated with k to v in t, adding it
   if the [k] is not present. *)
  Fixpoint insert {V : Type} (k : nat) (v : V) (t : Tree V) : Tree V :=
    match t with
    | leaf => node leaf k v leaf
    | node lt k' v' rt => if k =? k' then node lt k v rt
                          else if k <=? k' then node (insert k v lt) k' v' rt
                               else node lt k' v' (insert k v rt)
    end.

  Open Scope string_scope.
  (** Exercise: *)
  Example bst_ex1 :
    insert 5 "five" (insert 2 "two" (insert 4 "four" empty_tree)) = ex_tree.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (** Exercise: *)
  Example bst_ex2 : lookup 5 ex_tree = Some "five".
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (** Exercise: *)
  Example bst_ex3 : lookup 3 ex_tree = None.
  Proof.
    (* FILL IN HERE *)
  Admitted.

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

  (** Exercise: *)
  Example not_bst_lookup_wrong :
    lookup 2 bad_tree = None.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (** So, let's formalize when a tree is well-formed. To do so, we first
    define a helper [ForallT] to express that idea that a predicate
    holds at every node of a tree: *)

  Fixpoint ForallT {V : Type} (P: nat -> V -> Prop) (t : Tree V) : Prop :=
    match t with
    | leaf => True
    | node lt k v rt => P k v /\ ForallT P lt /\ ForallT P rt
    end.

  Inductive ForallT' {V : Type} (P: nat -> V -> Prop) : Tree V -> Prop :=
  | Forall_leaf : ForallT' P leaf
  | Forall_node : forall lt k v rt,
      P k v ->
      ForallT' P lt ->
      ForallT' P rt ->
      ForallT' P (node lt k v rt).

  Lemma silly_ex : 3 <= 2 -> 2 + 2 = 5.
  Proof.
    intro.
    lia.
  Qed.

  (** Second, we define well-formedness of BSTs:

    - An empty tree is a BST.

    - A non-empty tree is a BST if all its left nodes have a lesser
      key, its right nodes have a greater key, and the left and right
      subtrees are themselves BSTs. *)

  (** Exercise: *)
    Inductive BST {V : Type} : Tree V -> Prop :=
    | BST_leaf : BST leaf
    | BST_node :
        forall lt k v rt,
          ForallT (fun y _ => y < k) lt ->
          ForallT (fun y _ => k < y) rt ->
          BST lt ->
          BST rt ->
          BST (node lt k v rt).

  (** Let's check that [BST] correctly classifies a couple of example
    trees: *)

  (** Exercise: *)
  Example is_BST_ex :
    BST ex_tree.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (* 4
    / \
   5  2
   *)

  (** Exercise: *)
  Example not_BST_ex :
    ~ BST bad_tree.
  Proof.
    unfold not; intro contra.
    inversion contra; subst.
    simpl in H3.
    lia.
  Qed.

  (** Exercise: *)
  (** Prove that the empty tree is a BST. *)
  Theorem empty_tree_BST : forall (V : Type),
      BST (@empty_tree V).
  Proof.
    (* FILL IN HERE *)
  Admitted.


  (** Prove that [insert] produces a BST, assuming it is given one. *)
  (* Start by proving this helper lemma, which says that [insert]
    preserves any node predicate. *)

  (** Exercise: *)
  Lemma ForallT_insert : forall (V : Type) (P : nat -> V -> Prop) (t : Tree V),
      ForallT P t -> forall (k : nat) (v : V),
        P k v -> ForallT P (insert k v t).
  Proof.
    (* FILL IN HERE *)
  Admitted.

  Open Scope nat_scope.

  (** Exercise: *)
  (** Now prove the main theorem. *)
  Theorem insert_BST : forall (V : Type) (k : nat) (v : V) (t : Tree V),
      BST t -> BST (insert k v t).
  Proof.
    intros ? ? ? ? H.
    induction H.
    - simpl; repeat constructor.
    - simpl.
      destruct (k =? k0) eqn: ?.
      + Search Nat.eqb.
        apply Nat.eqb_eq in Heqb.
        subst.
        apply BST_node; assumption.
      + destruct (k <=? k0) eqn: ?; simpl.
        * apply BST_node; try assumption.
          apply ForallT_insert.
          assumption.
          apply Nat.eqb_neq in Heqb.
          Search Nat.leb.
          apply leb_complete in Heqb0.
          lia.
        * apply BST_node; try assumption.
          apply ForallT_insert.
          assumption.
          apply Nat.leb_gt.
          assumption.
  Qed.

End BSTs.

(*********************************************************
  Part 2.5: More Inductive Propositions
 *********************************************************)

(* Given the following definition of the "less-than-or-equal" relation
  on natural numbers, prove that the relation is reflexive and
  transitive and is not necessarily symmetric.  *)

Require Import Coq.Init.Nat.

(** Exercise: *)
(* (a) Reflexivity *)
Lemma le_refl : forall n, n <= n.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Exercise: *)
(* (cr) lack of symmetry *)
Lemma le_not_sym : ~ forall m n, m <= n -> n <= m.
Proof.
  unfold not; intro contra.
  assert (2 <= 1).
  { apply contra.
    apply le_S.
    apply le_n. }
  lia.
Qed.

(** Exercise: *)
(* (b) Transitivity *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Exercise: *)
(* Write an inductively-defined proposition for establishing that
   a natural number is odd, and prove that it works for the following examples.  *)
Inductive odd : nat -> Prop :=
(* FILL IN HERE *) .

(** Exercise: *)
Example odd_1 : odd 1.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Exercise: *)
Example odd_7 : odd 7.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Exercise: *)
Example even_0 : ~odd 0.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Exercise: *)
Example even_14 : ~odd 14.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Exercise: *)
(* Prove that an even number is never odd: *)
Lemma even_not_not : forall (n : nat),
    even n = true ->
    ~ odd n.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Exercise: *)
(* Now prove that an odd numbers is never even: *)
Lemma odd_not_even : forall (n : nat),
    odd n ->
    even n = false.
Proof.
  (* FILL IN HERE *)
Admitted.

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

  (** Exercise: *)
  Inductive aexpExp : Type :=
  (* ADD CONSTRUCTOR HERE *)
  | AENum (n : nat)
  | AEId (x : string)
  | AEPlus (a1 a2 : aexpExp)
  | AEMinus (a1 a2 : aexpExp)
  | AEMult (a1 a2 : aexpExp).

  (* ----------------------------------------------------------------- *)

  (** Exercise: *)
  (* The exponentiation function [pow] is in the standard library,
  feel free to use it here. *)
  Inductive aeevalR : state -> aexpExp -> nat -> Prop :=
  (* FILL IN THE REDUCTION RULE FOR EXPONENTIATION HERE *)
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

  (** Exercise: *)
  (* Define a helper function to help translate AEPow
     ntimes a 0 = a
     ntimes a (S n) = a * (ntimes a n)
*)
  Fixpoint nTimes (a : aexp) (n : nat) : aexp :=
    (* FILL IN HERE *) a.

  (** Exercise: *)
  Fixpoint aexpExpToaexp (ae : aexpExp) : aexp :=
    match ae with
    (* FILL IN HERE *)
    | AENum n => ANum n
    | AEId x => AId x
    | AEPlus a1 a2 => APlus (aexpExpToaexp a1) (aexpExpToaexp a2)
    | AEMinus a1 a2 => AMinus (aexpExpToaexp a1) (aexpExpToaexp a2)
    | AEMult a1 a2 => AMult (aexpExpToaexp a1) (aexpExpToaexp a2)
    end.

  (** Exercise: *)
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

  (** Exercise: *)
  (* Step One: prove that your helper function is sound. *)
  Lemma powTimesCorrect : forall st a n m,
      (st A=[ a ]=> m) ->
      st A=[ nTimes a n ]=> m ^ n.
  Proof.
    (* FILL IN HERE *)
  Admitted.

  (** Exercise: *)
  (* Step Two: Prove your elaboration is sound. *)
  Lemma aexpExpToaexpCorrect : forall ae st m,
      st AE=[ae]=> m -> st A=[aexpExpToaexp ae]=> m.
  Proof.
    (* FILL IN HERE *)
  Admitted.

End aevalR_extended.

(***************************************************************
  Part 4: Small-Step Operational Semantics + The Lambda Calculus
 ***************************************************************)

From PLF Require Import Smallstep.
Module LCBool.

  (* Let's add booleans to the untyped lambda calculus from last
     week's lab !*)

  (* t := ...
     | true
     | false
     | if t then t else t end *)

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

(* (\x, if x then false else true end) true *)

(** Exercise: *)
(** Update the definition of values to reflect that true and false are
    now values.  *)
Inductive value : tm -> Prop :=
  | v_abs : forall x t1,
      value <<{ \x, t1}>>
  | v_true : value tm_true
  | v_false : value <<{false}>>.

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
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3 end) = if [x:=s]t1 then [x:=s]t2 else [x:=s]t3 end

*)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(** Exercise: *)
(* Update the substitution function to account for booleans and if
   expressions.*)
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
    <<{if [x:=s]t1 then [x:=s]t2 else [x:=s]t3}>>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** For example... *)

(* ================================================================= *)
(** ** Reduction *)

(**
   Here are the small-step reduction rules for our extended lambda calculus:

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
               if t1 then t2 else t3 --> if t1' then t2 else t3

               --------------------------
               if true then t2 else t3 --> t2

              ----------------------------
              if false then t2 else t3 --> t3
*)

Reserved Notation "t '-->' t'" (at level 40).

(** Exercise: *)
(* Extend the reduction relation with the three rules above *)
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

  | ST_IfTrue : forall (t2 t3 : tm),
      <<{if true then t2 else t3}>> --> t2

  | ST_IfFalse : forall (t2 t3 : tm),
      <<{if false then t2 else t3}>> --> t3

  | ST_If : forall (t1 t1' t2 t3 : tm),
      t1 --> t1' ->
      <<{if t1 then t2 else t3}>> --> <<{if true then t2 else t3}>>

    (* FILL IN HERE *)

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Exercise: *)
(* Write lambda expressions to calculate the and / or / not of booleans. *)
Definition notB : tm :=
  <<{\x, if x then false else true}>>.

(** Exercise: *)
Definition andB : tm :=
  <<{\x, \y, if x then y else false}>>.

(** Exercise: *)
Definition orB : tm :=
  <<{\x, \y, if x then true else y}>>.

(** Optional Exercise: *)
(* Try to adapt the automation from Lab 6 to handle the rules you
   added above; it will help with the next couple of exercises.  *)
Ltac next_step :=
  first [ apply ST_AppAbs; solve [repeat constructor]
        | apply ST_App2; solve [repeat constructor]
        | apply ST_App1; next_step
        | apply ST_IfTrue
        | apply ST_IfFalse
        | apply ST_If; next_step ].

Ltac normalize_lambda :=
  repeat (eapply multi_step;
          [ next_step | ]); simpl.

(** Exercise: *)
Example notB_ex :
  <<{notB true}>> -->* <<{false}>>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(** Exercise: *)
Example andb_ex :
  <<{notB (andB true false)}>> -->* <<{true}>>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(** Exercise: *)
Example orb_ex :
  <<{orB (orB true false) (notB (andB true false))}>> -->* <<{true}>>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(** Exercise: *)
Example andb_ex2 :
  <<{orB (andB true (andB true (andB true (andB true false))))
         (andB true (andB true (andB true (andB true true))))}>> -->* <<{true}>>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

End LCBool.
