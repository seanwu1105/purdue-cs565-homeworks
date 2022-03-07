(*** CS 565 Midterm Exam -- Week of October 12, 2020 ***)
(** !!! Due date: 10/16/2020 by 6:00PM !!! **)

(*****************************************************************

    Your Name: *FILL IN HERE*

 *****************************************************************

  Before working on this file, open '_CoqProject' file in the same
  directory and replace the line '-R ../plf PLF' with
  '-R /path/to/your/programming/language/foundations/directory PLF',
  similar to how you did it in previous homework. Compile your
  [Stlc.v] in PLF first.

  There are 24 questions and one bonus question below; please fill in
  all the places that say *FILL IN HERE*. There are 75 points
  possible, plus an additional 5 bonus points.

  As stated on the syllabus, this midterm is a cumulative assessment
  of individual students' learning over the first half of the
  semester, and you should NOT discuss this exam with their
  classmates. Any clarifying questions should be asked via a PRIVATE
  post on piazza.

  Note that the standard late policy does not apply here. If you
  encounter a problem that could cause you to not submit the midterm
  before the deadline of 6:00PM on 10/16/2020, let the professor and
  the TA know IMMEDIATELY!

  You are allowed to use all theorems and exercises in 'Software
  Foundations', (regardless of whether they are proved
  or not). You can also use any lemmas or theorems in Coq's Standard
  Library.

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
      - Only hand in [Midterm.v]. Please do not submit auxiliary files,
        such as [Makefile] or [Midterm_test.v].

        The midterm is accompanied by a _test script_ ([Midterm_test.v]).
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
        the definition of [insert] is wrong, then every
        exercise involving [insert] (e.g., [insert_sort_correct]) will
        be impacted.
      - Be aware that even if 'make' prints no error or axioms, you
        may still lose points, because some exercises are manually
        graded.

    We are using Brightspace for submission. If you submit multiple
    versions of the assignment, you may notice that they are given
    different names.  This is fine: The most recent submission is the
    one that will be graded.

 *********************************************************)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Imp.
From PLF Require Import Maps.

From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Lia.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

(*********************************************************
  Part 1: Basic Functional Programming    (3 points)
 *********************************************************)

(* Given the following definition of a binary tree whose internal
   nodes hold natural numbers *)

Inductive NatTree : Type :=
| leaf
| node (l : NatTree) (n : nat) (r : NatTree).

(* We can represent the tree
               2
                \
                1
               / \
              6  10
                   \
                   11
                  /
                  6
                   \
                   12

as a [NatTree] like so: *)
Example tree_1 := node leaf 2 (node (node leaf 6 leaf) 1
                                    (node leaf 10 (node (node leaf 6 (node leaf 12 leaf))
                                                        11 leaf))).
(* Question 1 [rangeSearch] (2 points):

   Define a function [rangeSearch t l u] that finds all the
   elements in the [NatTree] [t] greater or equal to [l] and less than
   or equal to [u].

   Note: the tree need not be sorted. *)
Fixpoint rangeSearch (t : NatTree) (l u : nat) : list nat :=
[ ] (* REPLACE THIS LINE WITH YOUR DEFINITION *).

(* Question 2 [rangeSearch_tests] (1 point):

   Prove that your implementation of [rangeSearch] behaves as expected on
   the following test cases. For reference, the definition of [Permutation] is:

  Inductive Permutation (A : Type) : list A -> list A -> Prop :=
    perm_nil : Permutation [] []
  | perm_skip : forall (x : A) (l l' : list A), Permutation l l' -> Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A), Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A, Permutation l l' -> Permutation l' l'' -> Permutation l l''. *)

  Example rangeSearch_test_1 : Permutation (rangeSearch tree_1 4 8) [6; 6].
  Proof.
    (* FILL IN HERE *)
  Admitted.

  Example rangeSearch_test_2 : Permutation (rangeSearch tree_1 14 18) [].
  Proof.
    (* FILL IN HERE *)
  Admitted.

  Example rangeSearch_test_3 : Permutation (rangeSearch tree_1 2 10) [2; 6; 10; 6].
  Proof.
    (* FILL IN HERE *)
  Admitted.

  Example rangeSearch_test_4 : Permutation (rangeSearch tree_1 10 2) [].
  Proof.
    (* FILL IN HERE *)
  Admitted.

(*********************************************************
  Part 2: Basic Propositional Reasoning   (4 points)
 *********************************************************)

(* Question 3 [P_And_Not_P] (2 points):

  Prove that a proposition and its negation cannot both hold: *)
Lemma P_And_Not_P : forall (P : Prop), ~ (P /\ ~ P).
Proof.
    (* FILL IN HERE *)
  Admitted.

(* Question 4 [And_Distribute_Or] (2 points):

  Prove that propositional and [/\] distributes over propositional or
  [\/]: *)
Lemma And_Distribute_Or : forall (P Q R : Prop), (P /\ (Q \/ R)) <-> ( (P /\ Q) \/ (P /\ R)).
Proof.
  (* FILL IN HERE *)
Admitted.

(*********************************************************
  Part 3: Inductive Propositions   (13 points)
 *********************************************************)

(* A subsequence is a sequence that can be derived from another
   sequence by deleting some or no elements without changing the order
   of the remaining elements.

  The set of all subsequences for the word "exam" is "", "e", "x", "a",
  "m", "ex", "ea", "em", "xa", "xm", "am", "exa", "exm", "eam", "xam",
  and "exam". A sequence of n distinct elements has 2^n subsequences. *)

(* Question 5 [Subsequence] (4 points):

  Write an inductive proposition that captures when a (polymorphic)
  list is a subsequence of another list: *)
Inductive Subsequence {X : Type} : list X -> list X -> Prop :=
  (* FILL IN HERE *).

Open Scope string_scope.

(* Question 6 [Subsequence_test] (1 point):

   Validate your definition of [Subsequence] by proving the following five facts: *)
Example Subsequence_test_1 : Subsequence ["e"; "x"; "m"] ["e"; "x"; "a"; "m"].
Proof.
  (* FILL IN HERE *)
Admitted.

Example Subsequence_test_2 : Subsequence ["x"; "m"] ["e"; "x"; "a"; "m"].
Proof.
  (* FILL IN HERE *)
Admitted.

Example Subsequence_test_3 : Subsequence [ ] ["e"; "x"; "a"; "m"].
Proof.
  (* FILL IN HERE *)
Admitted.

Example Subsequence_test_4 : Subsequence ["e"; "x"; "a" ] ["e"; "x"; "a"; "m"].
Proof.
  (* FILL IN HERE *)
Admitted.

Example Subsequence_test_5 : Subsequence ["e"; "x"; "a"; "m"] ["e"; "x"; "a"; "m"].
Proof.
  (* FILL IN HERE *)
Admitted.

(* Optional Exercise: This should also be true, but you are not
   required to prove it.  (If you choose to do so, the [inversion]
   tactic will be quite useful. *)
Example Subsequence_test_6 : ~ Subsequence ["a"; "x"] ["e"; "x"; "a"; "m"].
Proof.
  (* OPTIONALLY FILL IN HERE *)
Admitted.

(* Question 7 [Subsequence_refl] (2 points):

   Prove that [Subsequence] is a reflexive relation. *)
Lemma Subsequence_refl {X} : forall (l : list X), Subsequence l l.
Proof.
  (* FILL IN HERE *)
Admitted.

(* Question 8 [Subsequence_not_sym] (2 points):

   Prove that [Subsequence nat] is not symmetric by identifying two
   lists [l1] and [l2] where [l1] is a subsequence of [l2] but not
   vice-versa. *)
Lemma Subsequence_not_sym :
  exists (l1 l2 : list nat),
    Subsequence l1 l2 /\
    ~ Subsequence l2 l1.
Proof.
  (* FILL IN HERE *)
Admitted.

(* Question 9 [Subsequence_trans] (4 points):

   Prove that [Subsequence] is transitive by induction.

   Hint: You will get stuck if you induct on the wrong thing. Sketch
   out the proof on paper first to help identify what to do induction
   on. *)
Lemma Subsequence_trans {X} : forall (l1 l2 l3 : list X),
    Subsequence l1 l2 ->
    Subsequence l2 l3 ->
    Subsequence l1 l3.
Proof.
  (* FILL IN HERE *)
Admitted.

(*********************************************************
  Part 4: Polymorphic + Higher-Order Functions  (14 points)
 *********************************************************)

(* Question 10 [b_opt] (3 points):

  Write a higher-order boolean expression optimizer which takes an
   arithmetic expression optimizer [a_opt] and applies it to /all/
   arithemetic subterms of a boolean expression.

   So: b_opt a_opt (a1 <= a2) = (a_opt a1) <= (a_opt a2), etc.
 *)

Fixpoint b_opt (a_opt : aexp -> aexp) (b : bexp) : bexp :=
  b (* REPLACE THIS LINE WITH YOUR DEFINITION *) .

(* Question 11 [b_opt_sound] (4 points):

   Show that when given a correct arithmetic expression optimizer,
   [b_opt] is semantics preserving. *)
Lemma b_opt_sound
  : forall a_opt,
    (forall (a : aexp) (st : state),
        aeval st (a_opt a) = aeval st a) ->
    forall (b : bexp) (st : state),
      beval st (b_opt a_opt b) = beval st b.
Proof.
  (* FILL IN HERE *)
Admitted.

(* Question 12 [insert] (2 points):

   Define an ordered insertion function on polymorphic lists. *)
Fixpoint insert {X} (leb : X -> X -> bool) (x : X) (l : list X) : list X :=
  l (* REPLACE THIS LINE WITH YOUR DEFINITION *).

(* Question 13 [insert_sort] (2 points):

   Use [insert] to implement insertion sort for polymorphic lists. *)
Fixpoint insert_sort {X} (leb : X -> X -> bool) (l : list X) : list X :=
  l (* REPLACE THIS LINE WITH YOUR DEFINITION *) .

(* Question 14 [insert_sort_test] (1 point):

Prove that your implementation of [insert_sort] behaves as expected on
the following test cases. *)

Example insert_sort_test_1 : insert_sort Nat.leb [1; 4; 6; 8] = [1; 4; 6; 8].
Proof.
  (* FILL IN HERE *)
Admitted.

Example insert_sort_test_2 : insert_sort Nat.leb [1; 8; 6; 4] = [1; 4; 6; 8].
Proof.
  (* FILL IN HERE *)
Admitted.

Example insert_sort_test_3 : insert_sort Nat.leb [8; 8; 3; 4] = [3; 4; 8; 8].
Proof.
  (* FILL IN HERE *)
Admitted.

Inductive SortedList {X} (le : X -> X -> Prop) : list X -> Prop :=
| Sorted_nil : SortedList le [ ]
| Sorted_one : forall (x : X), SortedList le [x]
| Sorted_n : forall (x x' : X) (l : list X),
    le x x' ->
    SortedList le (x' :: l) ->
    SortedList le (x :: x' :: l).

(* Bonus Question [insert_correct] (5 BONUS points):

   Prove that your implementation of [insert] is correct, in that,
   when given a correct comparator [leb] and a sorted list [l],
   it produces a sorted list.

   Note: This is a strictly OPTIONAL bonus question. *)

Lemma insert_correct {X}
  : forall (le : X -> X -> Prop)
      (leb : X -> X -> bool),
    (forall x x', leb x x' = true <-> le x x') ->
    (forall x x', leb x x' = false -> leb x' x = true) ->
    forall x l, SortedList le l ->
                SortedList le (insert leb x l).
Proof.
  (* FILL IN HERE *)
Admitted.

(* Question 15 [insert_sort_correct] (2 points):

   Prove that your implementation of [insert_sort] is correct, in
   that, when given a correct comparator [leb] it will return a sorted
   list.

   Note: You can use the [insert_correct] lemma from above in this
   proof without penalty, even if you chose not to prove it. *)
Lemma insert_sort_correct {X}
  : forall (le : X -> X -> Prop)
      (leb : X -> X -> bool),
    (forall x x', leb x x' = true <-> le x x') ->
    (forall x x', leb x x' = false -> leb x' x = true) ->
    forall l, SortedList le (insert_sort leb l).
Proof.
  (* FILL IN HERE *)
Admitted.

(*********************************************************
  Part 5: Big-Step Operational Semantics   (16 points)
 *********************************************************)

Module IMPRepeat.

  Declare Custom Entry comR.
  Declare Scope comR_scope.
  Notation "<<{ e }>>" := e (at level 0, e custom comR at level 99) : comR_scope.
  Notation "( x )" := x (in custom comR, x at level 99) : comR_scope.
  Notation "x" := x (in custom comR at level 0, x constr at level 0) : comR_scope.
  Notation "f x .. y" := (.. (f x) .. y)
                           (in custom comR at level 0, only parsing,
                               f constr at level 0, x constr at level 9,
                               y constr at level 9) : comR_scope.

(* ----------------------------------------------------------------- *)
(* Extending Imp with repeat Until loops                             *)

(* This portion of the midterm asks you to extend IMP with a new
   "repeat ... until" loop construct. These sorts of loops appear in
   such cutting edge languages as Perl, Visual Basic, and
   Pascal. These loops differ from the standard while loops in two
   ways:

   1) the loop guard is checked /after/ the execution of the body, so
      the loop always executes at least once.

   2) the loop continues executing as long as the condition is false.

*)

  Inductive comR : Type :=
  | CRSkip
  | CRAss (x : string) (a : aexp)
  | CRSeq (c1 c2 : comR)
  | CRIf (b : bexp) (c1 c2 : comR)
  | CRWhile (b : bexp) (c : comR)
  | CRRepeat (c : comR) (b : bexp).

Notation "'skip'"  :=
         CRSkip (in custom comR at level 0) : comR_scope.
Notation "x := y"  :=
         (CRAss x y)
            (in custom comR at level 0, x constr at level 0,
             y custom com at level 85, no associativity) : comR_scope.
Notation "x ; y" :=
         (CRSeq x y)
           (in custom comR at level 90, right associativity) : comR_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CRIf x y z)
           (in custom comR at level 89, x custom com at level 99,
            y custom comR at level 99, z custom comR at level 99) : comR_scope.
Notation "'while' x 'do' y 'end'" :=
         (CRWhile x y)
            (in custom comR at level 89, x custom com at level 99, y at level 99) : comR_scope.
Notation "'repeat' c 'until' b 'end'" :=
         (CRRepeat c b)
            (in custom comR at level 89, c at level 99, b custom com at level 99) : comR_scope.

Open Scope comR_scope.

(* As an example, here is a very inefficient program that stores the
   result of dividing Y by two in the variable X: *)
Definition div_by_two_example : comR :=
  <<{X := 0;
     repeat
     X := X + 1;
     Y := Y - 2
   until (Y = 0) end}>>.

(* Here's another example, where the loop always executes precisely once.  *)
Definition no_repeat_example : comR :=
  <<{X := 0;
      repeat
        (X := X + 1)
      until (true) end}>>.

Reserved Notation
         "st 'CR=[' c ']=>' st'"
         (at level 40, c custom comR at level 99,
          st constr, st' constr at next level).

(* Question 15 [cReval] (4 points):

   Thus, the big-step reduction rules for a repeat until loop look like:

   st =[c]=> st'     st' [b] => true
   ---------------------------------        [ER_RepeatTrue]
   st =[repeat c until b end]=> st'


   st =[c]=> st'     st' [b] => false       st' =[repeat c until b end]=> st''
   ---------------------------------------------------------------------------  [ER_RepeatFalse]
   st =[repeat c until b end]=> st''

 Add these rules to the standard big-step semantics for Imp below: *)

Inductive cReval : comR -> state -> state -> Prop :=
  | ER_Skip : forall st,
      st CR=[ skip ]=> st
  | ER_Ass  : forall st a n x,
      aeval st a = n ->
      st CR=[ x := a ]=> (x !-> n ; st)
  | ER_Seq : forall c1 c2 st st' st'',
      st  CR=[ c1 ]=> st'  ->
      st' CR=[ c2 ]=> st'' ->
      st  CR=[ c1 ; c2 ]=> st''
  | ER_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st CR=[ c1 ]=> st' ->
      st CR=[ if b then c1 else c2 end]=> st'
  | ER_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st CR=[ c2 ]=> st' ->
      st CR=[ if b then c1 else c2 end]=> st'
  | ER_WhileFalse : forall b st c,
      beval st b = false ->
      st CR=[ while b do c end ]=> st
  | ER_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  CR=[ c ]=> st' ->
      st' CR=[ while b do c end ]=> st'' ->
      st  CR=[ while b do c end ]=> st''

(* FILL IN HERE *)

  where "st CR=[ c ]=> st'" := (cReval c st st').

Hint Constructors cReval : core.

Ltac next_step :=
  first [ apply ER_Skip
        | eapply ER_Ass; reflexivity
        | eapply ER_Seq
        | eapply ER_IfTrue; [reflexivity | | ]
        | eapply ER_IfFalse; [reflexivity | | ]
        | eapply ER_WhileFalse; [reflexivity | ]
        | eapply ER_WhileTrue; [reflexivity | | ]
        (* UNCOMMENT THESE LINES AFTER COMPLETING QUESTION 15.
           YOU MAY ADJUST THE NAME ER_RepeatTrue and ER_RepeatFalse to reflect your cReval definition. *)
        (* | eapply ER_RepeatTrue; [ | reflexivity | ]
           | eapply ER_RepeatFalse; [ | reflexivity | ] *)
        ].

(* Question 16 [no_repeat_test] (1 point):

   Use your semantics to prove that [no_repeat_example] behaves as
   expected.  *)

Lemma no_repeat_test :
  forall st,
  exists st',
    (st CR=[no_repeat_example]=> st')
    /\ st' X = 1.
Proof.
  (* FILL IN HERE *)
Admitted.

(* Question 17 [div_by_two_test] (1 point):

   Use your semantics to prove that [div_by_two_example] behaves as
   expected.  *)
Lemma div_by_two_test :
  forall st,
    exists st',
      (Y !-> 8; X !-> 0; st) CR=[div_by_two_example]=> st' /\
                                                  st' Y = 0 /\ st' X = 4.
Proof.
  (* FILL IN HERE *)
Admitted.

(* Question 18 [comRTocom] (4 points):

   Repeat until loops can be convenient, but they are never required:
   every Imp+Repeat program can be translated into an Imp program that
   does the same thing.

   Define a translation function that converts Imp+Repeat programs to
   vanilla Imp programs. *)

Fixpoint comRTocom (c : comR) : com :=
  <{skip}> (* REPLACE THIS LINE WITH YOUR DEFINITION *).

(* Question 19 [comRTocom] (6 points):

   Prove that the implementation of [comRTocom] is correct. *)
Lemma comRToCom_correct :
  forall c st st',
    st CR=[c]=> st' -> st =[comRTocom c]=> st'.
Proof.
  (* FILL IN HERE *)
Admitted.

End IMPRepeat.

(***************************************************************************
  Part 6: Small-Step Operational Semantics + The Lambda Calculus (25 points)
 ***************************************************************************)

From PLF Require Import Smallstep.
Module LCPairsBool.

  (* Most programming languages provide some way to build compound
     data structures. The simpest of these is 'pairs' or 'tuples' of
     values.

     Adding pairs to the untyped lambda-calculus, involves adding two
     new forms of term -- pairing, written [<t1, t2>], and projection,
     written [fst t] for the first projection from [t] and [snd t]
     for the second projection.

     We can use nested pairs with booleans to represent fixed-width
     bit vectors. As an example, we can represent the unsigned 8-bit
     integers [1] and [145] as follows:

     [<false, <false, <false, <false, <false, <false, <false, true>>>>>>>]
     [<true, <false, <false, <true, <false, <false, <false, true>>>>>>>]

 *)


  (* In BNF Notation, the syntax for the untyped lambda calculus +
     Booleans + Pairs is:

       t ::=
       | x                    (variable)
       | \x,t                 (abstraction)
       | t t                  (application)
       | true                 (constant true)
       | false                (constant false)
       | if t then t else t   (conditional)

       | (t,t)                (pair [tm_proj1])
       | t.fst                (first projection [tm_proj2])
       | t.snd                (second projection [tm_pair]) *)

  (* Question 20 [tm] (2 points):

       Extend the following type of Lambda Calculus + Booleans to
       include these three new forms. We will define some custom
       notations in order to make it easier to write expressions in
       this language, so use the names in [...] when writing your
       extensions. *)
  Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_ite   : tm -> tm -> tm -> tm
  (* FILL IN HERE *).

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
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := tm_false (in custom stlc at level 0).
(* UNCOMMENT THESE LINES AFTER COMPLETING QUESTION 20.
Notation "'fst' tm"  := (tm_fst tm) (in custom stlc at level 0).
Notation "'snd' tm"  := (tm_snd tm) (in custom stlc at level 0).
Notation "'<' tm1 ',' tm2 '>'" := (tm_pair tm1 tm2) (in custom stlc at level 0). *)

Notation "\ x , y" :=
  (tm_abs x y) (in custom stlc at level 90, x at level 99,
                     y custom stlc at level 99,
                     left associativity).

Coercion tm_var : string >-> tm.

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

(* Here are lambda expressions for logical negation and swapping the
   elements of a pair *)
Definition notB : tm := <<{\x, if x then false else true}>>.
(* Definition swap : tm := <<{\x, <snd x, fst x> }>>. *)

(* Question 21 [and2B, or2B, not2B] (3 points):

   Write down expressions to calculate the bitwise and, bitwise or,
   and bitwise negation of a pair of booleans (i.e. a 2-bit vector).  *)

Definition not2B : tm :=
<<{x}>> (* REPLACE THIS LINE WITH YOUR DEFINITION *).

Definition and2B : tm :=
  <<{x}>> (* REPLACE THIS LINE WITH YOUR DEFINITION *).

Definition or2B : tm :=
  <<{x}>> (* REPLACE THIS LINE WITH YOUR DEFINITION *).

(* ================================================================= *)
(** ** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(* Question 22 [subst] (6 points):

   Update the substitution function in [Stlc.v] to handle pairs *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  t (* REPLACE THIS LINE WITH YOUR DEFINITION *)

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ================================================================= *)
(** ** Reduction *)

(** Here are the /Call-By-Name/ reduction rules for the Lambda
    Calculus + Booleans + Pairs.

    The Rules [ST_FstPair] and [ST_SndPair] say that, when a pair
    meets a first or second projection, the result is the appropriate
    component. The congruence rules [ST_Fst] and [ST_Snd] allow
    reduction to proceed under projections, in order to reduce the
    subterm to a concrete pair. *)

(*
                     ---------------------------                     [ST_AppAbs]
                     (\x,t1) t2 --> [x:=t2]t1

                              t1 --> t1'
                           ----------------                           [ST_App1]
                           t1 t2 --> t1' t2


                        t1 --> t1'
       ----------------------------------------------------------     [ST_If]
        if t1 then t2 else t3 end --> if t1' then t2 else t3 end

          -----------------------------------                         [ST_IfTrue]
          if true then t2 else t3 end --> t2

          -----------------------------------                         [ST_IfFalse]
          if false then t2 else t3 end --> t3

             -------------------------                                [ST_FstPair]
               fst <t1, t2> --> t1

             -------------------------                                [ST_SndPair]
               snd <t1, t2> --> t2

                    t1 --> t1'
             -------------------------                                [ST_Fst]
               fst t1 --> fst t1'

                    t1 --> t1'
             -------------------------                                [ST_Snd]
               snd t1 --> snd t1'

*)

Reserved Notation "t '-->' t'" (at level 40).

(* Question 23 [step] (10 points):

   Encode the call-by-name small-step operational semantics described
   above as an inductive proposition. *)

Inductive step : tm -> tm -> Prop :=
    (* FILL IN HERE *)


where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* The following tactic [normalize_lambda] tactic is meant to reduce
   lambda expressions to a normal form. It may be helpful when testing
   your reduction rules.  If the function seems to be running forever,
   try to apply the rules by hand. *)
Ltac normalize_lambda :=
  repeat (eapply multi_step;
          [ solve [repeat constructor] | ]); simpl.

(* Question 24 [step_test] (4 points):

   Prove that [step] has the desired semantics. *)
Example notB_ex :
  <<{notB true}>> -->* <<{false}>>.
Proof.
  (* FILL IN HERE *)
Admitted.

Example not2B_ex_1 :
  (* REPLACE THIS LINE WITH "<<{fst (not2B <true, false>)}>> -->* <<{false}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

Example not2B_ex_2 :
  (* REPLACE THIS LINE WITH "<<{snd (not2B <true, false>)}>> -->* <<{true}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

Example and2b_ex_1 :
  (* REPLACE THIS LINE WITH "<<{fst (and2B <true, false> <false, true>)}>> -->* <<{false}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

Example and2b_ex_2 :
  (* REPLACE THIS LINE WITH "<<{snd (and2B <true, false> <false, true>)}>> -->* <<{false}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

Example not2b_ex_3 :
  (* REPLACE THIS LINE WITH "<<{snd (not2B (and2B <true, true> <false, true>))}>> -->* <<{false}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

Example or2b_ex_1 :
  (* REPLACE THESE TWO LINES WITH "<<{fst (and2B (or2B <true, false> <false, true>)
                 (and2B <true, false> <false, true>))}>> -->* <<{false}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

Example or2b_ex_2 :
  (* REPLACE THIS LINE WITH "<<{snd (or2B <true, false> <false, true>)}>> -->* <<{true}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

Example or2b_ex_3 :
  (* REPLACE THESE TWO LINES WITH "<<{snd (and2B (or2B <true, false> <false, true>)
                 (and2B <true, true> <false, true>))}>> -->* <<{true}>>" *) False.
Proof.
  (* FILL IN HERE *)
Admitted.

End LCPairsBool.
