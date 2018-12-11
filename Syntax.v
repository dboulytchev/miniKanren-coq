Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.
Require Import Unify.
  
Inductive goal : Set :=
(* unification *) | Unify  : term -> term -> goal
(* disjunction *) | Disj   : goal -> goal -> goal
(* conjunction *) | Conj   : goal -> goal -> goal
(* fresh       *) | Fresh  : name -> goal -> goal
(* invoke      *) | Invoke : name -> list term -> goal.

Definition def  : Set := name * list name * goal.
Definition spec : Set := list def.