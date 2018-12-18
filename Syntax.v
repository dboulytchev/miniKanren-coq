Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.
Require Import Unify.
  
Inductive goal : Set :=
(* unification *) | Unify  : term -> term -> goal
(* disjunction *) | Disj   : goal -> goal -> goal
(* conjunction *) | Conj   : goal -> goal -> goal
(* fresh       *) | Fresh  : (name -> goal) -> goal
(* invoke      *) | Invoke : name -> list term -> goal.

Definition rel  : Set := @sigT nat (fun n => forall (args : list term), n = length args -> goal).  
Definition def  : Set := name * rel. 
Definition spec : Set := list def.

Definition a : rel.
  unfold rel. exists 0. intros. exact (Unify (Var 0) (Var 0)).
Defined.

Print a.

Lemma any_n: forall n, {l : list term & length l = n}.
Proof.
  intros.
  induction n. exists []. auto. inversion IHn. exists ((Var 0) :: x). simpl. auto.
Qed.
     
Definition x : rel -> goal.
  intro. inversion H. pose (any_n x). inversion s. eauto.
Defined.

Print x.
 
  
  
  

(* Partial state *) 
Inductive state' : Set :=
(* (goal, subst, first free semantic variable) *) | Leaf : goal -> subst -> nat -> state'
(* sum of two states'                          *) | Sum  : state' -> state' -> state'
(* product of two states'                      *) | Prod : state' -> goal   -> state'.

(* Complete state *)
Inductive state : Set :=
(* end of evaluation *) | Stop  : state  
(* a partial state   *) | State : state' -> state.

(* Labels *)
Inductive label : Set :=
(* nothing                                       *) | Step   : label
(* answer: (subst, first free semantic variable) *) | Answer : subst -> nat -> label.

(* Transitions *)
Section Transitions.

  Variable P : spec.
  
  Inductive eval_step : state' -> label -> state -> Prop :=
  | UnifyFail    : forall t1 t2 s    n, MGU (apply s t1) (apply s t2) None      -> eval_step (Leaf (Unify t1 t2) s n) Step Stop
  | UnifySuccess : forall t1 t2 s s' n, MGU (apply s t1) (apply s t2) (Some s') -> eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s' s) n) Stop
  | DisjS        : forall g1 g2       s n, eval_step (Leaf (Disj g1 g2) s n) Step (State (Sum (Leaf g1 s n) (Leaf g2 s n)))
  | ConjS        : forall g1 g2       s n, eval_step (Leaf (Conj g1 g2) s n) Step (State (Prod (Leaf g1 s n) g2))
  | FreshS       : forall fg          s n, eval_step (Leaf (Fresh fg) s n) Step (State (Leaf (fg n) s (S n)))
  | InvokeS      : forall f rf args e m s n, find (fun x => Nat.eqb (fst x) f) P = Some (f, e) ->
                                             length args = m ->
                                             eval_step (Leaf (Invoke f args) s n) Step (State (Leaf (rf args) s n)).

End Transitions.
                                 