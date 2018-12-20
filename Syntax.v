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

(* N-ary function type from term to goals *)
Fixpoint n_ary (n : nat) : Set :=
  match n with
  | 0   => goal
  | S k => term -> n_ary k
  end.

(* Application primitive *)
Definition n_apply (n : nat) (f : n_ary n) (args : list term) : length args = n -> goal.
revert args. induction n.
* intros. refine f.
* intros. destruct args.
  + inversion H.
  + inversion H. refine (IHn (f t) args H1).
Defined.

(* rel is a body of a relational symbol *)
Inductive rel : Set :=
  Def : forall n, n_ary n -> rel.

(* Some checks *)
Definition d0 : rel := Def 0 (           Unify (Var 0) (Var 0)).
Definition d1 : rel := Def 1 (fun t   => Unify t       (Var 0)).
Definition d2 : rel := Def 2 (fun t q => Unify t       q      ).

(* def is a definition of a relational symbol *)
Definition def : Set := name * rel.

(* spec is a list of definitions *)
Definition spec : Set := list def.

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
  | InvokeS      : forall f args (rf : n_ary (length args)) s n, find (fun x => Nat.eqb (fst x) f) P = Some (f, Def (length args) rf) ->
                                                                 eval_step (Leaf (Invoke f args) s n) Step (State (Leaf (n_apply (length args) rf args (eq_refl (length args))) s n))
  | SumE         : forall st1 st2      l, eval_step st1 l  Stop        -> eval_step (Sum st1 st2) l (State st2)
  | SumNE        : forall st1 st1' st2 l, eval_step st1 l (State st1') -> eval_step (Sum st1 st2) l (State (Sum st2 st1'))
  | ProdSE       : forall st g,         eval_step st  Step         Stop       -> eval_step (Prod st g) Step Stop
  | ProdAE       : forall st g s n,     eval_step st (Answer s n)  Stop       -> eval_step (Prod st g) Step (State (Leaf g s n))
  | ProdSNE      : forall st g     st', eval_step st  Step        (State st') -> eval_step (Prod st g) Step (State (Prod st' g))
  | ProdANE      : forall st g s n st', eval_step st (Answer s n) (State st') -> eval_step (Prod st g) Step (State (Sum (Leaf g s n) (Prod st' g))).

End Transitions.
