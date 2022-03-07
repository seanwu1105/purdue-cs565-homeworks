# Notes - Languages

## Polymorphism

- Parametric polymorphism
  - Generic in Java
  - Template in C++
- Subtyping polymorphism
  - Inheritance and polymorphism in OOP

## Inference Rules

![](images/inference-rules.png)

## Coq vs. Math

- Functional Extensionality: `|- (forall x . f x = g x) --> f = g`
- Excluded Middle: `|- P or ~P`

## IMP with Function Definitions

![](images/imp-with-fd.png)

## Featherweight Java R-Invk Rule

![](images/fj-r-invk.png)

### 4 ways a FJ program can reach a normal form

- Becomes a value (no field accesses / method class remain)
- Attempts to access a field not declared for the class
- Attempts to invoke a method not declared for the class
- Attempts to cast to something other than a superclass of an object's runtime
  class

## Heap

- Use a total map to model heap.
- Use a partial map to model allocation.
- LJ: Each object has its own partial map to field values.

## Lambda Calculus

### Conventions

![](images/lambda-conventions.png)

### Substitution

![](images/substitution.png)
