Set Warnings "-notation-overridden,-parsing,-require-in-module".
From PLF Require Import Smallstep.
From PLF Require Import Maps.

  (* In BNF Notation, the syntax for the types of this language is:
     T := T -> T | bool | T * T

     and the syntax for the language itself is:

       t ::=
       | x                    (variable)
       | \x : T,t                 (abstraction)
       | t t                  (application)
       | true                 (constant true)
       | false                (constant false)
       | if t then t else t   (conditional)

       | (t,t)                (pair [tm_pair])
       | t.fst                (first projection [tm_fst])
       | t.snd                (second projection [tm_snd])

       (The only difference from the untyped version is the typing
       annotation on lambda abstractions. *)

  Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Bool  : ty
  | Ty_Prod : ty -> ty -> ty
  | Ty_Var : string -> ty.

  Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false  : tm
  | tm_ite  : tm -> tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  | tm_pair : tm -> tm -> tm.

Declare Custom Entry stlc.
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
Notation "'fst' tm"  := (tm_fst tm) (in custom stlc at level 0).
Notation "'snd' tm"  := (tm_snd tm) (in custom stlc at level 0).
Notation "'<' tm1 ',' tm2 '>'" := (tm_pair tm1 tm2) (in custom stlc at level 0).

Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).

Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0).

Coercion tm_var : string >-> tm.
Coercion Ty_Var : string >-> ty.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition w : string := "w".
Definition t : string := "t".
Definition f : string := "f".
Definition s : string := "s".

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".

#[global] Hint Unfold x : core.
#[global] Hint Unfold y : core.
#[global] Hint Unfold z : core.
#[global] Hint Unfold w : core.
#[global] Hint Unfold s : core.

(* Here are lambda expressions for logical negation and swapping the
   elements of a pair *)
Definition notB : tm := <{\x : Bool, if x then false else true}>.
Definition swap : tm := <{\x : Bool * Bool, <snd x, fst x> }>.

(* Question 21 [and2B, or2B, not2B] (3 points):

   Write down expressions to calculate the bitwise and, bitwise or,
   and bitwise negation of a pair of booleans (i.e. a 2-bit vector).  *)

Definition andB : tm := <{\x : Bool, \y : Bool, if x then y else false}>.
Definition and2B : tm := <{\x : Bool * Bool, \y : Bool * Bool, <andB (fst x) (fst y), andB (snd x) (snd y)>}>.

Definition orB : tm := <{\x : Bool, \y : Bool, if x then true else y}>.
Definition or2B : tm := <{\x : Bool * Bool, \y : Bool * Bool, <orB (fst x) (fst y), orB (snd x) (snd y)>}>.

Definition not2B : tm := <{\x : Bool,  <notB (fst x), notB (snd x)>}>.

(* ================================================================= *)
(** ** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
    if String.eqb x y then s else t
  | <{\y: T , t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
    <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{if t1 then t2 else t3}> =>
    <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{fst t}> => <{fst ([x:=s] t)}>
  | <{snd t}> => <{snd ([x:=s] t)}>
  | <{< t1, t2> }> =>
      <{< [x:=s] t1 , [x:=s] t2>}>

  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ================================================================= *)
(** ** Reduction *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Booleans are values: *)
  | v_true :
      value <{true}>
   | v_false :
      value <{false}>
   (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{<v1, v2>}>.

(** We'll be using the Call-By-Value semantics rules for the Lambda
    Calculus + Booleans + Pairs in this exercise. *)

Reserved Notation "t '-->' t'" (at level 40).

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
  (* booleans  *)
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  (* pairs *)

  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        <{ <t1,t2> }> --> <{ <t1' , t2> }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ <v1, t2> }> -->  <{ <v1, t2'> }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ fst t0 }> --> <{ fst t0' }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ fst <v1,v2> }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ snd t0 }> --> <{ snd t0' }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ snd <v1,v2> }> --> v2

  where "t '-->' t'" := (step t t').

#[global] Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.
