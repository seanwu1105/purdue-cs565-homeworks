# Notes

## Algebraic Data Type

Simply spoken, an ADT is a type which is represented by several other subtypes.

[In Kotlin or Java 15, we can use Sealed Classes to define algebraic data types.](https://en.wikipedia.org/wiki/Algebraic_data_type#cite_note-6)

## Gallina

In the pronunciation, "L"s are muted. The native functional language of Coq.

## Tactics

The proof assistant to prove Gallina.

## [Constructor and Computation Rules](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#NatPlayground)

```coq
Check (S (S (S (S O)))).
(* ===> 4 : nat *)
Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 4).
(* ===> 2 : nat *)
```

The constructor `S` has the type `nat -> nat`, just like functions such as
`pred` and `minustwo`:

```coq
Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.
```

These are all things that can be applied to a number to yield a number. However,
there is a fundamental difference between `S` and the other two: functions like
`pred` and `minustwo` are defined by giving computation rules -- e.g., the
definition of `pred` says that `pred 2` can be simplified to `1` -- while the
definition of `S` has no such behavior attached. Although it is like a function
in the sense that it can be applied to an argument, it does not do anything at
all! It is just a way of writing down numbers.

Think about standard decimal numerals: the numeral 1 is not a computation; it's
a piece of data. When we write 111 to mean the number one hundred and eleven, we
are using 1, three times, to write down a concrete representation of a number.

### `simpl` vs `unfold`

`simpl` == `unfold` and then check if there are terms can changed but if not
DON'T DO ANYTHING.

### `destruct`

- Case analysis == disjunction (OR)
  - `destruct H as [A | B]`
  - `intros [A | B]`
- Proposition chain == conjunction (AND)
  - `destruct H as [A B]`
  - `intros [A B]`
- Destruct existential quantifier to get a witness `x` and the hypothesis
  stating that `P` holds of `x`
  - `destruct H as [x Hx]`

### `discriminate` vs `exfalso`

`discriminate` is used **on a hypothesis** involving an equality between
different constructors (e.g., false = true), and it solves the current goal
immediately.

`exfalso` is to prove **a goal** that is nonsensical (e.g., the goal state is
false = true).

### `induction`

Lab 3 Recording (53:00):

> Only introduce as much as you need to into the set of assumptions before doing
> an induction. Because then, the more universally quantified things you have in
> your goal, the more universally quantified things you will have in your
> inductive hypothesis, which is the more things you have the freedom to choose
> when you apply that inductive hypothesis.

## Commands

### `Search`

- Search for all usages and lemmas of a keyword.
  - `Search nat.`
- Search for the usages and lemmas given a "shape".
  - `Search (_ + _).`

## Constructive Logic vs Classic Logic

- Constructive logic: no excluded middle
  - Coq
- Classic logic: assume excluded middle
  - ZFC
