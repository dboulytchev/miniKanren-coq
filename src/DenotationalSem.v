Require Import List.
Import ListNotations.
Require Import Stream.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import OperationalSem.

Definition gt_fun : Set := name -> ground_term.

Fixpoint apply_gt_fun (f : gt_fun) (t : term) : term :=
  match t with
  | Var x => proj1_sig (f x)
  | Cst n => Cst n
  | Con n l r => Con n (apply_gt_fun f l) (apply_gt_fun f r)
  end.

Variable P : spec.

(* Simple variant *)
Inductive in_denotational_sem_goal : goal -> gt_fun -> Prop :=
| dsgUnify  : forall f t1 t2 (UnH : apply_gt_fun f t1 = apply_gt_fun f t2),
                            in_denotational_sem_goal (Unify t1 t2) f
| dsgDisjL  : forall f g1 g2 (Hg : in_denotational_sem_goal g1 f),
                            in_denotational_sem_goal (Disj g1 g2) f
| dsgDisjR  : forall f g1 g2 (Hg : in_denotational_sem_goal g2 f),
                            in_denotational_sem_goal (Disj g1 g2) f
| dsgConj   : forall f g1 g2 (Hg1 : in_denotational_sem_goal g1 f)
                            (Hg2 : in_denotational_sem_goal g2 f),
                            in_denotational_sem_goal (Conj g1 g2) f
| dsgFresh  : forall f fn a fg (fvH : forall n, ~ In a (fv_goal n (Fresh fg)))
                              (Hg : in_denotational_sem_goal (fg a) fn)
                              (Hease : forall (x : name) (neq : x <> a), fn x = f x),
                              in_denotational_sem_goal (Fresh fg) f
| dsgInvoke : forall r t f (Hbody : in_denotational_sem_goal (proj1_sig (P r) t) f),
                          in_denotational_sem_goal (Invoke r t) f.

(**)

(* Variant with levels * )

Inductive in_denotational_sem_with_env (env_in : name -> term -> gt_fun -> Prop) : gt_fun ->
                                                                                     goal ->
                                                                                     Prop :=
| dsEnvUnify  : forall f t1 t2 (UnH : apply_gt_fun f t1 = apply_gt_fun f t2),
                               in_denotational_sem_with_env env_in f (Unify t1 t2)
| dsEnvDisjL  : forall f g1 g2 (Hg : in_denotational_sem_with_env env_in f g1),
                               in_denotational_sem_with_env env_in f (Disj g1 g2)
| dsEnvDisjR  : forall f g1 g2 (Hg : in_denotational_sem_with_env env_in f g2),
                               in_denotational_sem_with_env env_in f (Disj g1 g2)
| dsEnvConj   : forall f g1 g2 (Hg1 : in_denotational_sem_with_env env_in f g1)
                               (Hg2 : in_denotational_sem_with_env env_in f g2),
                               in_denotational_sem_with_env env_in f (Conj g1 g2)
| dsEnvFresh  : forall f fn a fg (fvH : forall n, ~ In a (fv_goal n (Fresh fg)))
                                 (Hg : in_denotational_sem_with_env env_in fn (fg a))
                                 (Hease : forall (x : name) (neq : x <> a), fn x = f x),
                                 in_denotational_sem_with_env env_in f (Fresh fg)
| dsEnvInvoke : forall r t f (Henv : env_in r t f),
                             in_denotational_sem_with_env env_in f (Invoke r t).

Inductive in_denotational_sem_lev : nat -> gt_fun -> goal -> Prop :=
| dsLev : forall lev f g (dsEnvH : in_denotational_sem_with_env (fun r t f => in_denotational_sem_lev lev f (proj1_sig (P r) t)) f g),
                         in_denotational_sem_lev (S lev) f g.

Definition in_denotational_sem (f : gt_fun) (g : goal) : Prop := exists lev, in_denotational_sem_lev lev f g.
( **)

Definition in_denotational_sem_subst (s : subst) (f : gt_fun) : Prop :=
  exists (f' : gt_fun), forall (x : name), apply_gt_fun f' (apply_subst s (Var x)) = proj1_sig (f x).

Inductive in_denotational_sem_state' : state' -> gt_fun -> Prop :=
| dsst'Leaf : forall g s n f (Hgoal : in_denotational_sem_goal g f)
                             (Hsubst : in_denotational_sem_subst s f),
                             in_denotational_sem_state' (Leaf g s n) f
| dsst'SumL : forall st1' st2' f (Hst1' : in_denotational_sem_state' st1' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'SumR : forall st1' st2' f (Hst1' : in_denotational_sem_state' st2' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'Prod : forall st' g f (Hgoal : in_denotational_sem_goal g f)
                             (Hst' : in_denotational_sem_state' st' f),
                             in_denotational_sem_state' (Prod st' g) f.

Inductive in_denotational_sem_state : state -> gt_fun -> Prop :=
| dsstState : forall st' f (Hst' : in_denotational_sem_state' st' f),
                           in_denotational_sem_state (State st') f.

Definition in_denotational_analog (t : trace) (f : gt_fun) : Prop :=
  exists (s : subst) (n : nat), in_stream (Answer s n) t /\ in_denotational_sem_subst s f.

Fixpoint first_nats (k : nat) : list nat :=
  match k with
  | 0   => []
  | S n => n :: first_nats n
  end.

Lemma correctness
      (g   : goal)
      (k   : nat)      
      (HC  : closed_goal_in_context (first_nats k) g)
      (f   : gt_fun)
      (t   : trace)
      (HOP : op_sem (State (Leaf g empty_subst k)) t)
      (HDA : in_denotational_analog t f) : exists f', forall n, In n (first_nats k) -> f n = f' n.
Proof.