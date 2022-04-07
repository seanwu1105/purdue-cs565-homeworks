(* Lab 9: Programming and Proofs. *)

(* New bits covered:
   - Show Proof. (Command)
   - refine _ (tactic)
   - fix (this is actually a term)
 *)

(** Our job for this lab:
   - Explore the deep connection between programs and proofs,
     types and propositions, and induction and recursion.
 *)

From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From Coq Require Import Lia.

Definition flip (A B C : Type)
   :  (A -> B -> C) -> B -> A -> C :=
fun f b a => f a b.

Lemma flip2 : forall (A B C : Prop),
  (A -> B -> C) -> B -> A -> C.
Proof.
  (* Could do auto, but let's break it down a bit! *)
  (* When we try to build a proof in Coq, actually, we are building a function
     under the hood! *)
  intros A.
  Show Proof.
  intros B C H H0 H2.
  Show Proof.
  apply H.
  Show Proof.
  assumption.
  Show Proof.
  assumption.
  Show Proof.
Qed.

Definition split_fun (A B C : Type)
  : (A -> B -> C) -> (A -> B) -> (A -> C) :=
  fun f g a => f a (g a).

Lemma split_proof (A B C : Prop)
  : (A -> B -> C) -> (A -> B) -> (A -> C).
Proof.
  (* apply split_fun.  <- Apply the function could actually work as Coq does not
     distinguish the different between a function and a proof. *)
  refine (split_fun _ _ _).
Qed.

Lemma flip2' : forall (A B C : Prop),
  (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C.
  refine (fun (x : A -> B -> C) (y : B) (a : A) => _).
  auto.
Qed.

Lemma ge_trans : forall (x y z : nat),
    x >= y -> y >= z -> x >= z.
Proof.
  intros. lia.
Qed.

Lemma flip_ge : forall (x : nat),
    1 >= 0 -> x >= 1 -> x >= 0.
Proof.
  intros.
  eapply flip2.
  Show Proof.
  apply ge_trans.
  Show Proof.
  exact H.
  exact H0.
Qed.

Print flip_ge.

Lemma flip_ge' : forall (x : nat),
  1 >= 0 -> x >= 1 -> x >= 0.
Proof.
  intros.
  refine (ge_trans x 1 0 _ _).
  exact H0.
  exact H.
Qed.

(* Wait a second, if a program is just a proof, can't I 'run' it somehow?*)

Lemma ge_1_0 : 1 >= 0. Proof. lia. Qed.
Lemma ge_2_1 : 2 >= 1. Proof. lia. Qed.

Eval compute in (flip_ge _ ge_1_0 ge_2_1).

(* Let's look at a more interesting proposition (i.e. type!).  *)

Inductive ev : nat -> Prop :=
| ev_O : ev 0
| ev_SS : forall n, ev n -> ev (2 + n).

Lemma ev_plus_4 :
  forall n, ev n -> ev (4 + n).
Proof.
  (* intros.
  refine (ev_SS _ _).
  refine (ev_SS _ _).
  exact H. *)
  intros.
  constructor. (* constructor is actually implemented with refine *)
  constructor.
  assumption.
  Show Proof.
Defined. 
(* Using Defined instead of Qed, Coq will unfold and reduce the proof definition
   when we Eval compute it! *)

(* We can compute with this too! *)
(* Eval compute in (ev_plus_4 _ ev_O). *)

(* That was a little boring, let's try computing a more 'interesting'
   proof term... *)

(* Need an auxillary lemma for the next proof.*)
Lemma add_S_n : forall (n m : nat), n + (S m) = S (n + m).
Proof.
  intro.
  induction n.
  - intros; reflexivity.
  - intros; simpl; apply f_equal; apply IHn.
Defined.

Lemma ev_double:
  forall n, ev n -> ev (n + n).
Proof.
  intros.
  induction H.
  constructor.
  simpl.
  rewrite add_S_n.
  rewrite add_S_n.
  constructor. constructor.
  assumption.
Defined.

Eval compute in (ev_double _ (ev_plus_4 _ (ev_plus_4 _ ev_O))).

(* Hmmm.... if programs are proofs, and we can use Ltac to write proofs...
   OMG, We can means I can write programs using Ltac too! *)
Lemma plus : nat -> nat -> nat.
Proof.
  intros n m.
  Print Nat.add.
  refine ((fix plus' (n : nat) : nat :=
             match n return nat with
             | 0 => _
             | S n' => _
             end) n).
  exact m.
  exact (S (plus' n')).
Show Proof.
Defined.

(* We can actually define Lemma plus with a single auto. But it will generate
   a function only returning the second argument. So, this is the key difference
   between a program and a proof:
   Program cares about the result. Proof does not. *)

Eval compute in (plus 1 2).

Print ev_ind.

(* Here's a rogues gallery of the introduction rules for inductively
   propositions and their corresponding types: *)
(* and / tuples *)
Print and.
Print prod.

(* or / disjoint sum types*)
Print or.
Print sum.

(* Basic propositions: *)
Print True.
Print unit.

Print False.

(* And here are their elimination forms: *)
Print and_ind.
Print prod_ind.

Print or_ind.
Print sum_ind.

Print True_ind.
Print False_ind.

(* Induction principles for types are just (richly-typed) recursive functions! *)
Print nat_ind.
Print ev_ind.
