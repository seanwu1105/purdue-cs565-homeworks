
(* Lab 3:  *)
(* Tactics covered:
  * apply
  * apply ... with ...
  * apply ... in ...
  * symmetry
  * transitivity
  * exists
  * rewrite ... with ...
*)

(* In order to step through this file, you'll need to update your path
   so that Coq knows where to look for the libraries from Logical
   Foundations.

   If you're using emacs / proof general, the easiest way to do this
   is to create a file named _CoqProject which includes the line:
   "-Q *PATH_TO_LF* LF", replacing the line *PATH_TO_LF* with the path to
   your local copy of Logical Foundations. This should work for other IDEs
   as well, but I can't promise that. Post problems / solutions this problem
   on piazza.
*)

From LF Require Export Tactics.

(* Sorted example from our slides. *)
Inductive sorted {A : Type} (R : A -> A -> Prop)
  : list A ->  Prop :=
  | sempty : sorted R nil
  | sone : forall a : A, sorted R (cons a nil)
  | stwo : forall (a b : A) (l : list A),
              R a b -> sorted R (cons b l) ->
              sorted R (cons a (cons b l)).

(* Can apply constructors directly to build evidence (i.e.) prove that
   a list is sorted. *)
Example sorted124 : sorted le (cons 1 (cons 2 (cons 4 nil))).
Proof.
  (* How would we build this tree? *)
  (* Can use the [apply] tactic to spell out exactly which rules
  (constructors) to use. *)
  apply stwo.
  - repeat constructor.
  - apply stwo.
    repeat constructor.
    apply sone.
Qed.

Definition sorted_natlist := sorted le.

Example sorted124' : sorted_natlist (cons 1 (cons 2 (cons 4 nil))).
Proof.
  unfold sorted_natlist.
  exact sorted124.
Qed.

(* In fact, all the propositions we saw last time are defined
   similarly!*)
Print or.
Print conj.
Print True.
Print False.
Print eq.

(* ################################################################# *)
(* Working with universally quantified hypotheses using the [apply] tactic *)

(* Note that similar reasoning applies to Theorems whose statements
   involve universal quantifiers (forall / ∀). The following theorem,
   for example, proves a generic fact about the behavior of plus with
  respect to any two particular numbers: *)
Theorem plus_n_n_injective : forall (n m : nat),
    n + n = m + m ->
    n = m.
Proof.
  intro n.  induction n as [| n'].
  - simpl. intros m. induction m as [| m'].
    + intro eq. reflexivity.
    + intro eq. discriminate.
  - intro m. simpl. intro eq.
    destruct m.
    + discriminate.
    + assert (n' = m).
      { rewrite <- IHn'.
        - reflexivity.
        - assert (S (n' + n') = S (m + m)).
          { rewrite plus_n_Sm.
            rewrite plus_n_Sm.
            injection eq as eq.
            rewrite eq.
            reflexivity. }
          injection H as H.
          rewrite H. reflexivity. }
      rewrite -> H.
      reflexivity.
Qed.

(* Thus, we could specialize the above fact to justify any number of
     more specific claims: *)
Theorem plus_2_2_injective : forall m : nat,
    2 + 2 = m + m ->
    2 = m.
Proof.
  intros o eq.
  (* This goal is just a specialization of the fact we proved above.
     The apply tactic allows us to /instantiate/ universally
     quantified variables in a theorem with specific values to build a
     specialized version of the lemma: *)
  apply plus_n_n_injective with (n := 2) (m := o).
  (* apply also works when there are no universally quanitfied variables: *)
  apply eq.
Qed.

Theorem plus_6_6_injective : forall m : nat,
    6 + 6 = m + m ->
    6 = m.
Proof.
  (* Coq is oftentimes smart enough to figure out how to instantiate
  variables so that the conclusion of lemma / fact matches the goal: *)
  intros o eq.
  apply plus_n_n_injective.
  exact eq.
Qed.

(* In other words, once we have proven (or assumed) a fact starting
     with 'forall x, P x', we can use this to justify P v *for any*
     specific choice of v* *)

(* More interesting is that we can also specialize this theorem by
     applying plus_n_injective to specific numbers, just as we
     specialized the polymorphic definition of prod up above: *)
Check (plus_n_n_injective 2).
Check (plus_n_n_injective 4).
Check (plus_n_n_injective 2 4).

(* This means we can apply things without using the specialized (_ := _)
   notation:   *)
Theorem plus_2_2_injective_alt : forall m : nat,
    2 + 2 = m + m ->
    2 = m.
Proof.
  intros m eq.
  apply (plus_n_n_injective 2 m).
  apply eq.
Qed.

(* Let's peel back the curtain a bit to see how apply works more generally: *)

(* This fact is reflected in the elimination rule for the universal quantifier:
   Gamma |- forall (v : nat), P v    Gamma |- n : nat
   ======================================
   Gamma |- P n

  In other words, if I have evidence of the claim that [P v] holds for any number [v],
  and I have a specific number [n], I can establish evidence that [P n] holds.
*)

Lemma forallElim
  : forall (P : nat -> Prop) (n : nat),
    (forall (v : nat), P v) -> P n.
Proof.
  intros P n HP.
  (* The [apply] tactic specializes a universally quantified fact to prove a
     specific goal: *)
  apply HP.
Qed.

(** [apply] can be used with a lemma or assumption with *any* number
    of universally quantified variables.  Observe how Coq picks
    appropriate values for the [forall]-quantified variables of the
    hypothesis: *)
Theorem silly2a : forall (n m : nat),
     (forall (q r : nat), [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq.
  apply eq.
Qed.

(** We can use [apply] when some hypothesis or an earlier lemma
    exactly matches the goal (i.e. it has no variables to specialize): *)
Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

(* Aside: What happens if we omit the parentheses in the hypothesis?
   Can I use [apply] to prove this new claim? *)
Lemma forallElim_alt
  : forall (P : nat -> Prop) (n : nat),
    forall (v : nat), P v -> P n.
Proof.
Abort.

(** [apply] also works with _conditional_ hypotheses: *)
Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

(** Even when those _conditional_ hypotheses have universal quantifiers: *)
Theorem silly2b : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq H.
  apply H.
  apply eq.
Qed.

(** The goal must match the hypothesis _exactly_ for [apply] to
    work: *)
Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5)  ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  Fail apply H.

(** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)

  symmetry.

  simpl. (** This [simpl] is optional, since [apply] will perform
             simplification first, if needed. This is similar to how
             [reflexivity] will automatically unfold and simplify both
             sides of an equality before checking whether they are
             same expression. *)
  apply H.
Qed.

(* AN ASIDE: Equality is an equivalence relation, i.e. it is
   reflexive, symetric, and transitive. We've made extensive use of
   the [reflexivity] tactic when working with equalities, and we just
   encountered the [symmetry] tactic. Perhaps a transitivity tactic is
   available to us as well? *)
Theorem trans_example : forall (n m o : nat),
    n = m -> m = o -> n = o.
Proof.
  intros n m o eq1 eq2.
  Fail transitivity.
  (* What happened? Well, just like in [plus_2_2_injective], Coq isn't
  quite sure how to instantiate the intermediate variable. Let's try
  again: *)
  transitivity m.
  - apply eq1.
  - apply eq2.
Qed.

(* Having seen how apply works, lets revisit using [apply] with
   constructors of inductively defined propositions to build evidence
   of a claim:*)
Example le_4_8 : 4 <= 8.
Proof.
  Print le.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

(* A taste of proof automation to simplify this proof. *)
Example sorted1252 : sorted_natlist (cons 4 (cons 8 (cons 52 nil))).
Proof.
  repeat constructor.
Qed.

(* In fact, we can get this down to a one line tactic. *)
Example sorted1252180 : sorted le (cons 1 (cons 2 (cons 152 (cons 180 nil )))).
Proof.
  repeat constructor.
Qed.

(* Here are the rules for building evidence of the claim that a number
   is even. *)
(*
  =============================
  |- EvenN 0

  |- EvenN n
 =============================
  |- EvenL (2 + n)

*)

(* Here is the corresponding inductively defined proposition in Coq:*)
Inductive EvenN : nat -> Prop :=
| EvenZero : EvenN 0
| EvenSS : forall (n : nat), EvenN n -> EvenN (2 + n).

(* Work in Lab: Define the inductive proposition corresponding to
   these two proof rules: *)
(*
  =============================
  |- EvenL [ ]

  |- EvenN a
  |- EvenL l
 =============================
  |- EvenL (a :: l)

*)

Inductive EvenL : list nat -> Prop :=
| EvenNil : EvenL nil
| EvenCons : forall (a : nat) (l : list nat),
             EvenN a -> EvenL l -> EvenL (a :: l).

(* Using the proposition you defined above, State and prove a theorem
that the list [2; 4; 6] only has even numbers. *)

Theorem even_list_246 : EvenL (cons 2 (cons 4 (cons 6 nil))).
Proof.
  repeat constructor.
Qed.


(* ################################################################# *)
(* Rewriting with theorems that have universal quantifiers *)

(* We could also have used rewriting to prove [plus_2_2_injective]. *)
Theorem plus_2_2_injective' : forall m : nat,
    2 + 2 = m + m ->
    2 = m.
Proof.
  intros o eq.
  (* We've again have a general fact in hand, [plus_n_n_injective],
  but we run into trouble when we try to rewrite with it: *)
  Fail rewrite plus_n_n_injective.
  (* Hmmmm... This is similar to our failed proof of
     [plus_2_2_injective] from before. The solution is to also
     similar: *)
  rewrite plus_n_n_injective with (n := 2) (m := o).
  reflexivity.
  exact eq.
Qed.

Theorem plus_6_6_injective' : forall m : nat,
    6 + 6 = m + m ->
    6 = m.
Proof.
  intros o eq.
  (*WORK IN CLASS*)
Admitted.

Theorem plus_2_2_injective_alt' : forall m : nat,
    2 + 2 = m + m ->
    2 = m.
Proof.
  intros m eq.
  (*WORK IN CLASS*)
Admitted.

(* ################################################################# *)
(* Working with universally quantified goals using the [intro] tactic *)

(* Up to now, we've glossed over what is happening when we use
   [intros] to move universally quantified variables from the goal to
   the set of assumptions.

  Formally, the introduction rule for ∀ looks like:  *)

  (* Gamma, (m : nat) |- P m
  =============================
  Gamma |- forall (n : nat), P n *)

(* Recall that we read "Gamma |- P" as "Assuming the facts in gamma,
   we can conclude P."  So we can read this rule as (ignoring Gamma) :
   In order to prove that [P n] holds for every number [n], it
   suffices to show that [P m] holds assuming some arbitrary, unknown
   number [m]. Note that implicit in this statement is that even
   though [m] is arbitrary, it is some *specific*, *concrete*
   number. We can then use case analysis (or induction to examine how
   this specific [m] was built. *)

(* Let us use this insight to reexamine what happens when our
   inductive hypothesis is insufficiently generalized.*)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.

(** At this point, the induction hypothesis ([IHn']) does _not_ give us
    [n' = m'] -- there is an extra [S] in the way -- so the goal is
    not provable. *)

Abort.
(** What went wrong? *)

(** Trying to carry out this proof by induction on [n] when [m] is
    already in the context doesn't work because we are then trying to
    prove a statement involving _every_ [n] but just a _single_ [m]. *)

(** A successful proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *) simpl.
      discriminate eq.

    + (* m = S m' *)
      apply f_equal.
      apply IHn'. injection eq as goal. apply goal. Qed.

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)


(* Inference rules can be read in two ways. Recall the rule for
   elimination rule for implication (Modus Ponens): *)

(*   |- A -> B    |- A
     ==================
     |- B *)

(* Reading backwards, from the goal up, this says: "We're trying to
    prove [B], so if we can prove [A -> B], and [A] we'll be done."

    Alternatively, we could read this forwards, from the assumptions
    to the goal: "We know [A] and we know [A -> B], so we also know
    [B]."

   The first interpretation is an example of goal directed "backwards
   reasoning", while the second interpretation is an example of
   "forward reasoning" from the set of known facts / assumptions.

   The [apply] is a tactic for backwards reasoning. In contrast, the
   variant [apply... in...] is forward reasoning: *)

Theorem silly3backwards : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5)  ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H.
  symmetry.
  apply eq.
  apply H.
Qed.

(** Many tactics come with "[... in ...]" variants that work on
    hypotheses instead of goals. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros n m b H.
  simpl in H. (* simpl in _ *)
  apply H.
Qed.


Theorem S_inj_true : forall (n m : nat),
     (S n) =? (S m) = true  ->
     n =? m = true.
Proof.
  intros n m H.
  apply S_inj in H. (* apply _ in _ *)
  exact H.
Qed.

Theorem trans_example' : forall (n m o : nat),
    n = m -> m = o -> n = o.
Proof.
  intros n m o eq1 eq2.
  rewrite <- eq1 in eq2. (* rewrite _ in _ *)
  apply eq2.
Qed.

(* As the above examples suggest, the 'direction' you reason in is unimportant. *)
Theorem silly3 : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5)  ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  (* WORK IN CLASS *)
Admitted.

(* ================================================================= *)
(** ** Existential Quantification *)

(** To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t].  Then we prove that [P] holds after
    all occurrences of [x] are replaced by [t]. *)

Definition even (x : nat) : Prop := exists n : nat, x = double n.

Lemma four_is_even : even 4.
Proof.
  unfold even.
  exists 2. reflexivity.
Qed.

Lemma four_is_less_than_something : exists m : nat, 4 <= m.
Proof.
  exists 8.
  apply le_4_8.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  destruct H as [m neq].
  exists (2 + m).
  apply neq.
Qed.

(* Note that exists is defined as just another inductive proposition [ex] *)
Print ex.

(* IF THERE'S TIME AT THE END OF THE LAB: *)
(* ################################################################# *)
(** * Programming with Propositions *)

(** What does it mean to say that "an element [x] occurs in a
    list [l]"?

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if either it is equal to [x'] or it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition (!): *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl.
  apply or_intror.
  apply or_intror.
  apply or_intror.
  apply or_introl.
  reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  intros n Inn.
  simpl in Inn.
  destruct Inn as [neq2 | Inn].
  - exists 1.
    simpl.
    symmetry.
    apply neq2.
  - destruct Inn as [neq4 | Inn].
    + exists 2.
      rewrite <- neq4.
      reflexivity.
    + contradiction.
Qed.

(** We can also prove more generic, higher-level lemmas about [In].

    Note, in the first, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l.
  induction l.
  - simpl.
    intros.
    destruct H.
  - intros x0 H'.
    simpl.
    simpl in H'.
    destruct H' as [H' | H'].
    + rewrite H'.
      left.
      reflexivity.
    + right.
      apply IHl.
      apply H'.
Qed.
