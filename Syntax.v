Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.
Require Eqdep_dec Arith.
Require Import Unify.

Inductive goal : Set :=
(* unification *) | Unify  : term -> term -> goal
(* disjunction *) | Disj   : goal -> goal -> goal
(* conjunction *) | Conj   : goal -> goal -> goal
(* fresh       *) | Fresh  : (name -> goal) -> goal
(* invoke      *) | Invoke : name -> list term -> goal.

(* Free variable monadic enumerator *)
Fixpoint fvm (n : name) (g : goal) : list name * name :=
  match g with
  | Unify t1 t2 => (fv_term t1 ++ fv_term t2, n)
  | Disj  g1 g2
  | Conj  g1 g2 => let (t1, n1) := fvm n  g1 in
                   let (t2, n2) := fvm n1 g2 in
                   (t1 ++ t2, n2)
  | Fresh fg    => let g := fg n in
                   let (ts, n') := fvm (S n) g in
                   (remove Nat.eq_dec n ts, n')
  | Invoke _ ts => (fv_terms ts, n)
  end.

(* Free variables enumerator *)
Definition fv_goal n g := fst (fvm n g).

(* Closedness of goals *)
Definition closed_goal_in_context (c : list name) (g : goal) : Prop :=
  forall x, (forall n, In x (fv_goal n g)) -> In x c.

Definition closed_goal : goal -> Prop := closed_goal_in_context [].

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
  Rel : forall n, n_ary n -> rel.

(* Arity of a relational symbol *)
Definition arity (r : rel) : nat :=
  match r with
  | Rel n _ => n
  end.

(* Application of a relational symbol *)
Definition apply_rel (r : rel) (args : list term) (c : length args = arity r) : goal.
  destruct r eqn:R. simpl in c. apply (n_apply n n0 args c).
Defined.

(* Closedness of a relational symbol *)
Definition closed_rel (r : rel) : Prop :=
  forall (args : list term) (c : length args = arity r),
    closed_goal_in_context (fv_terms args) (apply_rel r args c).

(* Some checks *)
Module SmokeTest.

  Definition g0 : goal := Fresh (fun x => Unify (Var x) (Cst 2)).
  Definition g1 : goal := Fresh (fun x => Fresh (fun y => Unify (Var x) (Var y))).

  Lemma g0_closed : closed_goal g0.
  Proof.
    unfold closed_goal. unfold closed_goal_in_context. intros x H.
    unfold fv_goal in H. unfold fvm in H. unfold g0 in H. simpl in H.
    specialize (H x). destruct (Nat.eq_dec x x) eqn:D. assumption. contradiction.
  Qed.
  
  Lemma g1_closed : closed_goal g1.
  Proof.
    unfold closed_goal. unfold closed_goal_in_context. intros x H.
    unfold fv_goal in H. unfold fvm in H. unfold g1 in H. unfold fv_term in H.
    specialize (H x). simpl in H. destruct (Nat.eq_dec x x) eqn:D. destruct x. simpl in H. auto.
    destruct (Nat.eq_dec (S x) x). simpl in H. auto. simpl in H. destruct (Nat.eq_dec x x). auto. contradiction. contradiction.
  Qed.
    
  Definition r0 : rel := Rel 0 (           Unify (Cst 0) (Cst 0)).
  Definition r1 : rel := Rel 1 (fun t   => Fresh (fun q => Unify t (Var q))).
  Definition r2 : rel := Rel 2 (fun t q => Unify t q).

  Lemma r0_closed : closed_rel r0.
  Proof.
    unfold closed_rel. intros. simpl in c. destruct args eqn:A.
    * unfold fv_terms. simpl. unfold closed_goal_in_context. simpl. auto.
    * simpl in c. inversion c.
  Qed.

  Lemma r1_closed : closed_rel r1.
  Proof.
    unfold closed_rel. intros. simpl in c. destruct args eqn:A.
    * simpl in c. inversion c.
    * simpl in c. inversion c. unfold length in H0. destruct l eqn:L.
      + simpl in c.
        assert (App: apply_rel r1 [t] c = Fresh (fun q => Unify t (Var q))).
          simpl. replace c with (eq_refl 1). auto. apply Eqdep_dec.UIP_dec, eq_nat_dec.  (* Wow! Wow! *)
        rewrite App. unfold fv_terms. simpl. unfold closed_goal_in_context. intros. unfold fv_goal in H.
        unfold fvm in H. simpl in H. remember (free_var t) as FV. inversion_clear FV.
        specialize (H x0).
        assert (HH: remove Nat.eq_dec x0 (fv_term t ++ [x0]) = fv_term t). admit.
        rewrite <-HH. auto.
      + simpl in c. inversion c.
  Admitted.
    
  Lemma r2_closed : closed_rel r2.
  Proof.
    unfold closed_rel. intros. simpl in c. unfold length in c. destruct args eqn:A.
    * inversion c.
    * destruct l. inversion c.
      + destruct l.
         - assert (App: apply_rel r2 [t; t0] c = Unify t t0).
             simpl. replace c with (eq_refl 2). simpl. reflexivity. apply Eqdep_dec.UIP_dec, eq_nat_dec. (* Wow! Wow! *)
           rewrite App. unfold fv_terms. simpl. unfold closed_goal_in_context. intros. unfold fv_goal in H.
           unfold fvm in H. simpl in H. auto.
         - inversion c.
  Qed.
  
End SmokeTest.

(* def is a definition of a closed relational symbol *)
Inductive def : Set :=
  Def : forall (r: rel), closed_rel r -> def.

(* spec is a list of definitions *)
Definition spec : Set := list (name * def).

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
  | UnifyFail    : forall t1 t2     s    n , MGU (apply s t1) (apply s t2) None      -> eval_step (Leaf (Unify t1 t2) s n) Step Stop
  | UnifySuccess : forall t1 t2     s s' n , MGU (apply s t1) (apply s t2) (Some s') -> eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s' s) n) Stop
  | DisjS        : forall g1 g2        s n , eval_step (Leaf (Disj g1 g2) s n) Step (State (Sum (Leaf g1 s n) (Leaf g2 s n)))
  | ConjS        : forall g1 g2        s n , eval_step (Leaf (Conj g1 g2) s n) Step (State (Prod (Leaf g1 s n) g2))
  | FreshS       : forall fg           s n , eval_step (Leaf (Fresh fg) s n)   Step (State (Leaf (fg n) s (S n)))
                                                       
  | InvokeS      : forall f args r s n (c : length args = arity r) (cl : closed_rel r),
                     find (fun x => Nat.eqb (fst x) f) P = Some (f, Def r cl) -> 
                     eval_step (Leaf (Invoke f args) s n) Step (State (Leaf (apply_rel r args c) s n))
                                                      
  | SumE         : forall st1 st2        l , eval_step st1 l  Stop                    -> eval_step (Sum st1 st2) l (State st2)
  | SumNE        : forall st1 st1' st2   l , eval_step st1 l (State st1')             -> eval_step (Sum st1 st2) l (State (Sum st2 st1'))
  | ProdSE       : forall st g             , eval_step st     Step         Stop       -> eval_step (Prod st g) Step Stop
  | ProdAE       : forall st g s n         , eval_step st    (Answer s n)  Stop       -> eval_step (Prod st g) Step (State (Leaf g s n))
  | ProdSNE      : forall st g     st'     , eval_step st     Step        (State st') -> eval_step (Prod st g) Step (State (Prod st' g))
  | ProdANE      : forall st g s n st'     , eval_step st    (Answer s n) (State st') -> eval_step (Prod st g) Step (State (Sum (Leaf g s n) (Prod st' g))).

End Transitions.
