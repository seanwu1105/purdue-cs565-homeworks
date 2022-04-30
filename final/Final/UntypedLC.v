Set Warnings "-notation-overridden,-parsing".

From PLF Require Import Stlc.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

  (* In BNF Notation, the syntax for the untyped lambda calculus +
     Booleans is:
       t ::=
       | x                    (variable)
       | \x,t                 (abstraction)
       | t t                  (application)
       | true                 (constant true)
       | false                (constant false)
       | if t then t else t   (conditional) *)

  Inductive Utm : Type :=
  | Utm_var   : string -> Utm
  | Utm_app   : Utm -> Utm -> Utm
  | Utm_abs   : string -> Utm -> Utm
  | Utm_true  : Utm
  | Utm_false  : Utm
  | Utm_ite  : Utm -> Utm -> Utm -> Utm.

Declare Custom Entry utlc.
Notation "<<{ e }>>" := e (e custom utlc at level 99).
Notation "( x )" := x (in custom utlc, x at level 99).
Notation "x" := x (in custom utlc at level 0, x constr at level 0).
Notation "x y" := (Utm_app x y) (in custom utlc at level 1, left associativity).
Notation "'if' x 'then' y 'else' z" :=
  (Utm_ite x y z) (in custom utlc at level 89,
                    x custom utlc at level 99,
                    y custom utlc at level 99,
                    z custom utlc at level 99,
                    left associativity).
Notation "'true'"  := Utm_true (in custom utlc at level 0).
Notation "'false'"  := Utm_false (in custom utlc at level 0).

Notation "\ x , y" :=
  (Utm_abs x y) (in custom utlc at level 90, x at level 99,
                     y custom utlc at level 99,
                     left associativity).

Coercion Utm_var : string >-> Utm.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition w : string := "w".
Definition t : string := "t".
Definition f : string := "f".
Definition s : string := "s".

#[global] Hint Unfold x : core.
#[global] Hint Unfold y : core.
#[global] Hint Unfold z : core.
#[global] Hint Unfold w : core.
#[global] Hint Unfold s : core.

(* ================================================================= *)
(** ** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom utlc at level 20, x constr).

Fixpoint Usubst (x : string) (s : Utm) (t : Utm) : Utm :=
  match t with
  | Utm_var y =>
      if eqb_string x y then s else t
  | <<{\y, t1}>> =>
      if eqb_string x y then t else <<{\y, [x:=s] t1}>>
  | <<{t1 t2}>> =>
    <<{([x:=s] t1) ([x:=s] t2)}>>
  | <<{true}>> => <<{true}>>
  | <<{false}>> => <<{false}>>
  | <<{if t1 then t2 else t3}>> =>
    <<{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>>

  end

where "'[' x ':=' s ']' t" := (Usubst x s t) (in custom utlc).

(* ================================================================= *)
(** ** Reduction *)

(** Here are the /Call-By-Value/ reduction rules for the Lambda
    Calculus + Booleans. *)

(*                          value t2
                     ---------------------------                     [ST_AppAbs]
                     (\x,t1) t2 --> [x:=t2]t1

                              t1 --> t1'
                           ----------------                           [ST_App1]
                           t1 t2 --> t1' t2

                       value v1      t2 --> t2'
                     ----------------------------                           [ST_App1]
                           v1 t2 --> v1 t2'



                        t1 --> t1'
       ----------------------------------------------------------     [ST_If]
        if t1 then t2 else t3 end --> if t1' then t2 else t3 end

          -----------------------------------                         [ST_IfTrue]
          if true then t2 else t3 end --> t2

          -----------------------------------                         [ST_IfFalse]
          if false then t2 else t3 end --> t3

*)

  Inductive Uvalue : Utm -> Prop :=
  | Uv_abs : forall x t,
      Uvalue <<{\x, t}>>
  | Uv_true :
      Uvalue <<{true}>>
  | Uv_false :
      Uvalue <<{false}>>.

Reserved Notation "t '-U->' t'" (at level 40).

Inductive Ustep : Utm -> Utm -> Prop :=
| STU_AppAbs : forall x t1 v2,
    Uvalue v2 ->
    <<{(\x, t1) v2}>> -U-> <<{ [x:=v2]t1 }>>
| STU_App1 : forall t1 t1' t2,
    t1 -U-> t1' ->
    <<{t1 t2}>> -U-> <<{t1' t2}>>
| STU_App2 : forall v1 t2 t2',
    Uvalue v1 ->
    t2 -U-> t2' ->
    <<{v1 t2}>> -U-> <<{v1 t2'}>>

  | STU_IfTrue : forall t1 t2,
      <<{if true then t1 else t2}>> -U-> t1
  | STU_IfFalse : forall t1 t2,
      <<{if false then t1 else t2}>> -U-> t2
  | STU_If : forall t1 t1' t2 t3,
      t1 -U-> t1' ->
      <<{if t1 then t2 else t3}>> -U-> <<{if t1' then t2 else t3}>>

where "t '-U->' t'" := (Ustep t t').

#[global] Hint Constructors step : core.

Notation Umultistep := (multi Ustep).
Notation "t1 '-U->*' t2" := (Umultistep t1 t2) (at level 40).
