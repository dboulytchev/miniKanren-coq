Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Omega.
Require Eqdep_dec Arith.
Require Import Unify.

Inductive goal : Set :=
(* unification *) | Unify  : term -> term -> goal
(* disjunction *) | Disj   : goal -> goal -> goal
(* conjunction *) | Conj   : goal -> goal -> goal
(* fresh       *) | Fresh  : (name -> goal) -> goal
(* invoke      *) | Invoke : name -> term -> goal.

(* Free variable monadic enumerator *)
Fixpoint fvm (n : name) (g : goal) : list name * name :=
  match g with
  | Unify t1 t2 => (var_set_union (fv_term t1) (fv_term t2), n)
  | Disj  g1 g2
  | Conj  g1 g2 => let (s1, n1) := fvm n  g1 in
                   let (s2, n2) := fvm n1 g2 in
                   (var_set_union s1 s2, n2)
  | Fresh fg    => let g := fg n in
                   let (ts, n') := fvm (S n) g in
                   (var_set_remove n ts, n')
  | Invoke _ t => (fv_term t, n)
  end.

(* Free variables enumerator *)
Definition fv_goal n g := fst (fvm n g).

(* Closedness of goals *)
Definition closed_goal_in_context (c : list name) (g : goal) : Prop :=
  forall x n, In x (fv_goal n g) -> In x c.

Definition closed_goal : goal -> Prop := closed_goal_in_context [].

(* rel is a body of a relational symbol *)
Definition rel : Set := term -> goal.

(* Closedness of a relational symbol *)
Definition closed_rel (r : rel) : Prop :=
  forall (arg : term), closed_goal_in_context (fv_term arg) (r arg).

(* Some checks *)
Module SmokeTest.

  Definition g0 : goal := Fresh (fun x => Unify (Var x) (Cst 2)).
  Definition g1 : goal := Fresh (fun x => Fresh (fun y => Unify (Var x) (Var y))).

  Lemma g0_closed : closed_goal g0.
  Proof.
    red. red. intros. unfold fv_goal in H. unfold fvm in H.
    simpl in H. destruct (name_eq_dec n n).
    * auto.
    * contradiction.
  Qed.

  Lemma g1_closed : closed_goal g1.
  Proof.
    red. red. intros. unfold fv_goal in H. unfold fvm in H.
    simpl in H. destruct n.
    * auto.
    * destruct (name_eq_dec (S n) n).
      + omega.
      + unfold var_set_remove in H.
        unfold set_remove in H.
        destruct (name_eq_dec (S (S n)) (S n));
        destruct (name_eq_dec (S (S n)) (S (S n)));
        destruct (name_eq_dec (S n) (S n));
        try omega. auto.
  Qed.

  Definition r0 : rel := (fun t => Fresh (fun x => Fresh (fun y =>
      Conj (Unify t (Con 0 (Var x) (Var y))) (Unify (Var x) (Var y))))).
  Definition r1 : rel := (fun t => Fresh (fun x => Unify (Var 0) t)).

  Lemma r0_closed : closed_rel r0.
  Proof.
    red. red. intros. unfold fv_goal in H. unfold fvm in H.
    red in H. red in H. red in H. fold In in H.
    assert (NoDup (var_set_union
               (var_set_union (fv_term arg)
                  (fv_term (Con 0 (Var n) (Var (S n)))))
               (var_set_union (fv_term (Var n))
                  (fv_term (Var (S n)))))).
    { apply set_union_nodup; apply set_union_nodup; apply fv_term_nodup. }
    assert (NoDup
       (var_set_remove (S n)
            (var_set_union
               (var_set_union (fv_term arg)
                  (fv_term (Con 0 (Var n) (Var (S n)))))
               (var_set_union (fv_term (Var n))
                  (fv_term (Var (S n))))))).
    { apply set_remove_nodup. auto. }
    unfold var_set_remove in H.
    apply (set_remove_iff name_eq_dec _ _ H1) in H. destruct H.
    apply (set_remove_iff name_eq_dec _ _ H0) in H. destruct H.
    unfold var_set_union in H. apply set_union_elim in H. destruct H.
    + apply set_union_elim in H. destruct H.
      - auto.
      - simpl in H. destruct n.
        { destruct H; try omega. destruct H; try omega. inversion H. }
        { destruct (name_eq_dec (S n) n); try omega.
          destruct H; try omega. destruct H; try omega. inversion H. }
    + simpl in H. destruct n.
      { destruct H; try omega. destruct H; try omega. inversion H. }
      { destruct (name_eq_dec (S n) n); try omega.
        destruct H; try omega. destruct H; try omega. inversion H. }
  Qed.

  Lemma r1_non_closed : ~ closed_rel r1.
  Proof.
    intro C. red in C. red in C.
    specialize (C (Cst 0) 0 1). apply C.
    simpl. auto.
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

  Inductive well_formed_goal : goal -> Prop :=
  | wfUnify  : forall t1 t2, well_formed_goal (Unify t1 t2)
  | wfDisj   : forall g1 g2, well_formed_goal g1 -> well_formed_goal g2 -> well_formed_goal (Disj g1 g2)
  | wfConj   : forall g1 g2, well_formed_goal g1 -> well_formed_goal g2 -> well_formed_goal (Conj g1 g2)
  | wfFresh  : forall fg, (forall n, well_formed_goal (fg n)) -> well_formed_goal (Fresh fg)
  | wfInvoke : forall f arg, (exists r cl, find (fun x => Nat.eqb (fst x) f) P = Some (f, Def r cl)) ->
                             well_formed_goal (Invoke f arg).

  Hint Constructors well_formed_goal.

  Variable P_well_formed : forall f r cl arg, In (f, Def r cl) P -> well_formed_goal (r arg).

  Inductive well_formed_state' : state' -> Prop :=
  | wfLeaf : forall g s n,     well_formed_goal g ->
                               well_formed_state' (Leaf g s n)
  | wfSum  : forall st'1 st'2, well_formed_state' st'1 ->
                               well_formed_state' st'2 ->
                               well_formed_state' (Sum st'1 st'2)
  | wfProd : forall st' g,     well_formed_state' st' ->
                               well_formed_goal g ->
                               well_formed_state' (Prod st' g).

  Hint Constructors well_formed_state'.


  Inductive eval_step : state' -> label -> state -> Prop :=
  | UnifyFail    : forall t1 t2     s    n , unify (apply s t1) (apply s t2) None      -> eval_step (Leaf (Unify t1 t2) s n) Step Stop
  | UnifySuccess : forall t1 t2     s s' n , unify (apply s t1) (apply s t2) (Some s') -> eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s' s) n) Stop
  | DisjS        : forall g1 g2        s n , eval_step (Leaf (Disj g1 g2) s n) Step (State (Sum (Leaf g1 s n) (Leaf g2 s n)))
  | ConjS        : forall g1 g2        s n , eval_step (Leaf (Conj g1 g2) s n) Step (State (Prod (Leaf g1 s n) g2))
  | FreshS       : forall fg           s n , eval_step (Leaf (Fresh fg) s n)   Step (State (Leaf (fg n) s (S n)))

  | InvokeS      : forall f arg r s n (cl : closed_rel r),
                     find (fun x => Nat.eqb (fst x) f) P = Some (f, Def r cl) ->
                     eval_step (Leaf (Invoke f arg) s n) Step (State (Leaf (r arg) s n))

  | SumE         : forall st1 st2        l (H: eval_step st1 l  Stop), eval_step (Sum st1 st2) l (State st2)
  | SumNE        : forall st1 st1' st2   l , eval_step st1 l (State st1')             -> eval_step (Sum st1 st2) l (State (Sum st2 st1'))
  | ProdSE       : forall st g             , eval_step st     Step         Stop       -> eval_step (Prod st g) Step Stop
  | ProdAE       : forall st g s n         , eval_step st    (Answer s n)  Stop       -> eval_step (Prod st g) Step (State (Leaf g s n))
  | ProdSNE      : forall st g     st'     , eval_step st     Step        (State st') -> eval_step (Prod st g) Step (State (Prod st' g))
  | ProdANE      : forall st g s n st'     , eval_step st    (Answer s n) (State st') -> eval_step (Prod st g) Step (State (Sum (Leaf g s n) (Prod st' g))).

  Hint Constructors eval_step.

  Lemma well_formedness_preservation :
    forall (st' st'_next : state') (l : label),
      eval_step st' l (State st'_next) -> well_formed_state' st' -> well_formed_state' st'_next.
  Proof.
    intros. remember (State st'_next).
    generalize dependent Heqs. revert st'_next.
    induction H; intros st'_next eq; inversion eq.
    1-3: inversion H0; inversion H2; auto.
    2-6: inversion H0; subst; auto.
    * apply find_some in H. destruct H. eauto.
  Qed.

  Lemma eval_step_exists : forall (st' : state'),
    well_formed_state' st' -> exists (st : state) (l : label), eval_step st' l st.
  Proof.
    intros st' wf_st'. induction st'.
    * destruct g.
      2-4: repeat eexists; econstructor.
      + assert (exists r, unify (apply s t) (apply s t0) r). { apply unify_exists. }
        destruct H. destruct x.
        all: repeat eexists; eauto.
      + inversion wf_st'. inversion H0.
        destruct H4. destruct H4.
        repeat eexists. eauto.
    * inversion wf_st'. specialize (IHst'1 H1).
      destruct IHst'1 as [st1 [l1 IH1]]. destruct st1.
      all: repeat eexists; eauto.
    * inversion wf_st'. specialize (IHst' H1).
      destruct IHst' as [st [l IH]]. destruct st; destruct l.
      all: repeat eexists; eauto.
  Qed.

  Lemma eval_step_unique :
    forall (st' : state') (l1 l2 : label) (st1 st2 : state),
      eval_step st' l1 st1 -> eval_step st' l2 st2 -> l1 = l2 /\ st1 = st2.
  Proof.
    induction st'.
    * intros. destruct g; inversion H; inversion H0; subst.
      + auto.
      + assert (C : None = Some s').
        { eapply unify_unique; eassumption. }
        inversion C.
      + assert (C : None = Some s').
        { eapply unify_unique; eassumption. }
        inversion C.
      + assert (C : Some s' = Some s'0).
        { eapply unify_unique; eassumption. }
        inversion C. auto.
      + auto.
      + auto.
      + auto.
      + rewrite H14 in H7. inversion H7. auto.
    * intros. inversion H; inversion H0; subst;
      specialize (IHst'1 _ _ _ _ H5 H10); inversion IHst'1;
      inversion H2; subst; auto.
    * intros. inversion H; inversion H0; subst;
      specialize (IHst' _ _ _ _ H5 H10); inversion IHst'; subst;
      inversion H1; inversion H2; auto.
  Qed.

End Transitions.
