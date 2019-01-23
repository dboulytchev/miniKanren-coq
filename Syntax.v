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
  | Unify t1 t2 => (fv_term t1 ++ fv_term t2, n)
  | Disj  g1 g2
  | Conj  g1 g2 => let (t1, n1) := fvm n  g1 in
                   let (t2, n2) := fvm n1 g2 in
                   (t1 ++ t2, n2)
  | Fresh fg    => let g := fg n in
                   let (ts, n') := fvm (S n) g in
                   (remove Nat.eq_dec n ts, n')
  | Invoke _ t => (fv_term t, n)
  end.

(* Free variables enumerator *)
Definition fv_goal n g := fst (fvm n g).

(* Closedness of goals *)
Definition closed_goal_in_context (c : list name) (g : goal) : Prop :=
  forall x, (forall n, In x (fv_goal n g)) -> In x c.

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

  Definition bad_r : rel := (fun t => Fresh (fun x => Unify (Var 0) t)).

  Lemma remove_reduces : forall x y l, In x (remove Nat.eq_dec y l) -> In x l.
  Proof.
    intros. induction l.
    { auto. }
    {
      unfold remove in H. destruct (Nat.eq_dec y a).
      { right. auto. }
      { destruct H.
        { left. auto. }
        { right. auto. }}}
  Qed.

  Lemma contratest : closed_rel bad_r.
  Proof.
    red. red. intros. specialize (H 0). unfold fv_goal in H.
    simpl in H. eapply remove_reduces. eauto.
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
