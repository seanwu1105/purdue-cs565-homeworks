# Notes

## Coq Language

### Algebraic Data Type

Simply spoken, an ADT is a type which is represented by several other subtypes.

[In Kotlin or Java 15, we can use Sealed Classes to define algebraic data types.](https://en.wikipedia.org/wiki/Algebraic_data_type#cite_note-6)

### Gallina

In the pronunciation, "L"s are muted. The native functional language of Coq.

### Tactics

The proof assistant to prove Gallina.

### [Constructor and Computation Rules](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#NatPlayground)

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
