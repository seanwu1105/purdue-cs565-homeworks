(****** Homework 2 for CS-565 Programming Languages - Purdue. ******)
(** !!! Due date: 02/04/2022 by 6:00PM !!! **)
(* ================================================================= *)
(** ** Instructions for homework 2 *)

(** Follow the following instructions for homework 2.
      - Before working on this homework, please open '_CoqProject' file
        in the same directory and replace the line '-R lf LF' with
        '-R /path/to/your/logical_foundations/directory LF'. For example,
        if your [Logic.v] resides in '/home/myname/lf', then replace that
        line with '-R /home/myname/lf LF'.
      - Compile your [Logic.v] first according to 'Software Foundations'.
      - You are allowed to use all theorems and exercises in
        'Software Foundations' up to chapter [Logic.v] (regardless of whether
        they are proved or not). But do not use the exercises of the
        same statement. For example, you are not allowed to use the exercise
        [and_assoc] in [Logic.v] to prove the exercise [and_assoc] here.
      - If you define additional definitions or lemmas, make sure they are
        defined in [hw2.v]. Remember you only hand in [hw2.v].
      - There is no extra credit for solving the optional exercises at the
        end of this homework. Try solve them if you want some challenges.
*)

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

    Each homework (like [hw2.v]) is accompanied by a _test script_
    ([hw2_test.v]). You may want to use them to double-check that your
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

Set Warnings "-notation-overridden,-parsing".
(** The [Require Export] statement on the next line tells Coq to use
    the [Nat] and PeanoNat modules from the standard library.  *)
From LF Require Export Logic.

(* ================================================================= *)
(* Polymorphism and First-Class Functions: *)
(* Note: these definitions use the following notations:
   - "[ ]" = nil
   - "a :: l" = cons a l
   - "l1 ++ l2" = app l1 l2 *)

(* In this section, we first define a data structure that holds student
records. A student record contains their name, age, and major: *)
Inductive Student :=
| personRecord (name : string) (age : nat) (major : string).

(* We can define a getter for a student's age. *)
Definition getAge (p : Student) : nat :=
  match p with
  | personRecord _ a _ => a
  end.

(* The tree holding student records consists is either:
   - an internal node consisting of an age, all the records of students
     of that age, and a left and right subtree
   - OR an empty tree
  *)
Inductive StudentsTree : Type :=
| node (key : nat) (records : list Student) (lt rt : StudentsTree)
| empty.

(* We can define a recursive function that lists all the student
   records in the database: *)
Fixpoint EnumerateStudents (db : StudentsTree) : list Student :=
    match db with
    | node nkey records lt rt =>
      records ++ (EnumerateStudents lt) ++ (EnumerateStudents rt)
    | empty => [ ]
  end.

(* Note that the correctness of the following two function definitions depends
   on them being applied to a 'proper' binary search tree. The final section of
   this homework explores this idea further. *)

(* We can define a query function that lists the records of every
   student of a certain age: *)
Fixpoint FindStudent (age : nat) (db : StudentsTree) :=
  match db with
  | node age' records lt rt => if (age =? age') then records else
                                 if (age <=? age') then FindStudent age lt else FindStudent age rt
  | empty => [ ]
  end.

(* And we can define an update function that inserts a new student in
   the database: *)
Fixpoint AddStudent (person : Student) (db : StudentsTree) : StudentsTree :=
  match db with
  | node age' records lt rt => if (getAge person =? age') then node age' (person :: records) lt rt
                               else if (getAge person <=? age') then node age' records (AddStudent person lt) rt
                                 else node age' records lt (AddStudent person rt)
  | empty => node (getAge person) (person :: [ ]) empty empty
  end.

(* Here are some sample student records, and a database that holds
   them. *)
Definition Alice : Student := personRecord "Alice" 24 "CS".
Definition Bob : Student := personRecord "Bob" 22 "Chemistry".
Definition Carl : Student := personRecord "Carl" 22 "CS".
Definition Donna : Student := personRecord "Donna" 21 "CS".

Definition exampleDB := AddStudent Alice (AddStudent Bob (AddStudent Carl (AddStudent Donna empty))).

(* Here are some sample queries. *)
Compute (FindStudent 21 exampleDB).
Compute (FindStudent 22 exampleDB).
Compute (FindStudent 23 exampleDB).
Compute (FindStudent 24 exampleDB).
Compute (EnumerateStudents exampleDB).

(* The next five problems ask you to generalize these definitions
   using first-class functions and polymorphism, to implement a more
   generic database.  *)

(** **** Exercise: 1 point (SearchTree) *)
(* Define a search tree that is polymorphic over the type of its
   search keys and elements: *)
Inductive SearchTree (* REPLACE THIS LINE WITH ANY TYPE PARAMETERS *) : Type := (* FILL IN HERE *).

(** **** Exercise: 1 point (EnumerateRecords) *)
(* Define a polymorphic function that returns all the elements in a
   database: *)
Fixpoint EnumerateRecords
         (* REPLACE THIS LINE WITH THE PARAMETERS AND RETURN TYPE OF YOUR FUNCTION *) (db : SearchTree) : unit.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) Admitted.

(** **** Exercise: 1 point (FindKey) *)
(* Define a polymorphic higher-order variant of [FindPerson] that
   takes equality and comparision functions as arguments and uses
   them to find all the elements in a database matching a given key:
   *)
Fixpoint FindKey
         (* REPLACE THIS LINE WITH THE PARAMETERS AND RETURN TYPE OF YOUR FUNCTION *) (db : SearchTree) : unit.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) Admitted.

(** **** Exercise: 1 point (AddElement) *)
(* Define a polymorphic higher-order variant of [AddElement] that
   takes equality, comparision, and a projection function from a
   record to its key as arguments and uses them to insert a new
   element into the database: *)
Fixpoint AddElement
         (* REPLACE THIS LINE WITH THE PARAMETERS AND RETURN TYPE OF YOUR FUNCTION *) (db : SearchTree) : unit.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) Admitted.

(* Prefixing the function definitions below with an @ symbol forces their
   implicit arguments to be treated as explicit. Learn more in the
   'Supplying Type Arguments Explicitly' section in Poly.v.

   We can 'recover' our original database by specializing these polymorphic versions: *)
Definition EnumerateStudents' :=
(* REPLACE THIS LINE WITH "@EnumerateRecords nat Student." AFTER FINISHING THE PREVIOUS EXERCISES *) fun (_ : unit) => [] : list Student.
Definition FindStudent' :=
(* REPLACE THIS LINE WITH "@FindKey nat Student eqb leb." AFTER FINISHING THE PREVIOUS EXERCISES *) fun (_ : nat) (_ : unit) => [] : list Student.
Definition AddStudent' :=
(* REPLACE THIS LINE WITH "@AddElement nat Student eqb leb getAge." AFTER FINISHING THE PREVIOUS EXERCISES *) fun (_ : Student) (_ : unit) => tt.

Definition exampleDB' :=
(* REPLACE THIS LINE WITH "AddStudent' Alice (AddStudent' Bob (AddStudent' Carl (AddStudent' Donna EmptyTree)))." AFTER FINISHING THE PREVIOUS EXERCISES *) tt.
(* YOU MAY HAVE TO ADJUST THE NAME 'EmptyTree' IN THE DEFINITION
TO REFLECT YOUR DEFINITION OF [SearchTree]. *)

(** **** Exercise: 1 point (sanity_check) *)
(* You can validate your generalized definitions by testing that these
   specialized versions agree with the original implementation on some
   sample inputs: *)
(* You should be able to complete the following proofs using only [reflexivity]. *)
Example Find_21_OK : FindStudent' 21 exampleDB' = FindStudent 21 exampleDB.
Proof.
  (* FILL IN HERE *)
Admitted.

Example Find_22_OK : FindStudent' 22 exampleDB'  = FindStudent 22 exampleDB.
Proof.
  (* FILL IN HERE *)
Admitted.

Example Find_23_OK : FindStudent' 23 exampleDB'  = FindStudent 23 exampleDB.
Proof.
  (* FILL IN HERE *)
Admitted.

Example Find_24_OK : FindStudent' 24 exampleDB'  = FindStudent 24 exampleDB.
Proof.
  (* FILL IN HERE *)
Admitted.

Example Enumerate_OK : EnumerateStudents' exampleDB' = EnumerateStudents exampleDB.
Proof.
  (* FILL IN HERE *)
Admitted.

(* ================================================================= *)
(* Basic Tactics *)
(* See Tactics.v for more examples of [apply], [discriminate], and
   [injection] and additional exercises. That chapter also contains
   some variants of these tactics. *)

(** **** Exercise: 1 point (apply_Q) *)
(** Complete the following proof using only [intros] and [apply]. *)
Theorem apply_Q :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 4 = true ->
     oddb 3 = true.
Proof.
  (* FILL IN HERE *)
Admitted.

(** **** Exercise: 1 point (injection_Q) *)
(** Complete the following proof using only [intros], [injection], [rewrite], and [reflexivity]. *)
Theorem injection_Q : forall (X : Type) (x y z w : X) (l j : list X),
    x :: y :: l = w :: z :: j ->
    x :: l = z :: [ ] ->
    x = y.
Proof.
  (* FILL IN HERE *)
Admitted.

(** **** Exercise: 1 point (discriminate_Q) *)
(** Complete the following proof using only [intros] and [discriminate]. *)
Theorem discriminate_Q :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  (* FILL IN HERE *)
Admitted.

(* ================================================================= *)
(* Proof by Induction: *)
(* See Induction.v for more examples of the [induction] tactic and
   additional exercises. *)

Module NatGymnasium.


  (* Recall the definitions of natural numbers and addition from the
  standard library: *)
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S p => S (plus p m)
    end.
  (** Prove the following lemmas using induction on natural numbers. *)


  (** **** Exercise: 1 point (plus_n_Sm) *)
  Theorem plus_n_Sm : forall n m : nat,
      S (plus n m) = plus n (S m).
  Proof.
  (* FILL IN HERE *)
  Admitted.

  (** **** Exercise: 1 point (plus_assoc) *)
  Theorem plus_assoc : forall n m p : nat,
      plus n (plus m p) = plus (plus n m) p.
  Proof.
  (* FILL IN HERE *)
Admitted.

  (** **** Exercise: 1 point (plus_comm) *)
  (* Hint 1: you may need to use [plus_n_Sm]. *)
  (* Hint 2: you might need to induct on both numbers.*)
  Theorem plus_comm : forall n m : nat,
    plus n m = plus m n.
  Proof.
  (* FILL IN HERE *)
Admitted.

  (** **** Exercise: 1 point (double_plus)  *)
  (** Consider the following function, which doubles its argument: *)
  Fixpoint double (n:nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

  (** Use induction to prove this simple fact about [double]: *)
  Lemma double_plus : forall n, double n = plus n n .
  Proof.
  (* FILL IN HERE *)
Admitted.

End NatGymnasium.

Module ListGynamsium.

  (* Recall the definitions of polymorphic list, length, and append
     from the standard library: *)
  Inductive list (A : Type) : Type :=
  | nil
  | cons (a : A) (l : list A).

  Arguments nil {_}.
  Arguments cons {_} a l.

  Fixpoint length {A : Type} (l : list A) : nat :=
    match l with
    | nil => O
    | cons h t => S (length t)
    end.

  Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
    match l1 with
    | nil    => l2
    | cons h t => cons h (app t l2)
    end.

  (** **** Exercise: 1 point (app_length)  *)
  (** Prove the follow theorem relating the behaviors of the length
      and append functions. *)
  Theorem app_length {A : Type} : forall l1 l2 : list A,
      length (app l1 l2) = (length l1) + (length l2).
  Proof.
  (* FILL IN HERE *)
  Admitted.

End ListGynamsium.

(* ================================================================= *)
(* Propositional Logic: *)
(* See Logic.v for more examples of the [induction] tactic and
   additional exercises. *)

(** **** Exercise: 1 point (and_assoc)  *)
(** Prove that logical conjunction is associative using [destruct] and [split]. *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    (* FILL IN HERE *)
Admitted.

(** **** Exercise: 1 point (or_commut)  *)
(** Prove that logical disjunction is commutative using [destruct], [left], and [right]. *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *)
Admitted.

(** **** Exercise: 1 point (contrapositive)  *)
(* Prove that evidence of an implication also entails its
   contrapostive using [unfold] and [apply]. *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *)
Admitted.

(* ================================================================= *)
(* Inductively defined propositions: *)
(* See IndProp.v for more examples and additional exercises. *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** **** Exercise: 1 point (ev_double)  *)
(* Prove that doubling a number always results in an even number.
   Hint: you are free to use any previously theorems about addition in
   this proof. *)
Theorem ev_double : forall n,
  ev (n + n).
Proof.
  (* FILL IN HERE *)
Admitted.

(** **** Exercise: 1 point (ev_sum)  *)
(* Prove that the sum of two even numbers is also even.
   Hint: Consider inducting on one of the eveness assumptions. *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* FILL IN HERE *)
Admitted.

(* ================================================================= *)
(* Putting it all together: Search Trees Revisited *)

(* In order for FindStudent and AddStudent to behave as expected, their
   second argument needs to be a well-formed search tree.

   Informally, a search tree is well-formed iff:
   - It is nonempty and:
     * each record in a node needs to be the same age as the node's key
     * all of the people in the left subtree of a node need to be younger than the age in that node
     * all of the people in the right subtree of a node need to be older than the age in that node
     * the left and right subtrees of a node need to be well-formed search trees.
   - OR it is empty.
*)

Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
    Forall_nil : Forall P [ ]
  | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l).

(* Exercise: 3 points (WF_StudentsTree) *)
(* Define an inductive proposition that captures when a StudentsTree is
   well-formed. You might find the [Forall] proposition defined above
   useful.  *)
Inductive WF_StudentsTree : StudentsTree -> Prop :=
  (* FILL IN HERE *) .

(* Exercise: 1 points (exampleDBOK) *)
(* As a sanity check, make sure the example database from above is well-formed. *)
Example exampleDBOK : WF_StudentsTree exampleDB.
Proof.
    (* FILL IN HERE *)
Admitted.

(* OPTIONAL Exercise: (FindStudentOK_1) *)
(* We can also *prove* that search behave correctly, assuming that
   they are called with a well-formed database. This is an OPTIONAL
   challenge problem, however.  *)
Lemma FindStudentOK_1 :
  forall (person : Student) (db : StudentsTree),
    WF_StudentsTree db ->
    FindStudent (getAge person) (AddStudent person db) = person :: (FindStudent (getAge person) db).
Proof.
  (* FILL IN HERE IF YOU ARE FEELING ADVENTUROUS. *)
Admitted.

(* OPTIONAL Exercise: (FindStudentOK_2) *)
Lemma FindStudentOK_2 :
  forall (person : Student) (db : StudentsTree),
    WF_StudentsTree db ->
    forall (age : nat),
      (getAge person =? age) = false ->
      FindStudent age (AddStudent person db) = (FindStudent age db).
Proof.
    (* FILL IN HERE IF YOU ARE FEELING ADVENTUROUS. *)
Admitted.

(* OPTIONAL Exercise: (AddStudentOK) *)
(* We can also *prove* that insertion maintains the invariant that an
   updated database is well-formed. Like the previous lemmas, this is
   an OPTIONAL exercise for your own edification. *)
Lemma AddStudentOK :
  forall (db : StudentsTree),
    WF_StudentsTree db ->
    forall (person : Student),
      WF_StudentsTree (AddStudent person db).
Proof.
    (* FILL IN HERE IF YOU ARE FEELING ADVENTUROUS. *)
Admitted.
