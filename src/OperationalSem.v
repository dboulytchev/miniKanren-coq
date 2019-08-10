Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Stream.
Require Import Omega.

(* Partial state *) 
Inductive state' : Set :=
(* (goal, subst, first free semantic variable) *) | Leaf : goal -> subst -> nat -> state'
(* sum of two states'                          *) | Sum  : state' -> state' -> state'
(* product of two states'                      *) | Prod : state' -> goal   -> state'.

(* Complete state *)
Inductive state : Set :=
(* end of evaluation *) | Stop  : state
(* a partial state   *) | State : state' -> state.

Inductive is_fv_of_state' : name -> state' -> Prop :=
| isfvst'Leaf  : forall x g s n     (isfvH : is_fv_of_goal x g),      is_fv_of_state' x (Leaf g s n)
| isfvst'SumL  : forall x st'1 st'2 (isfvH : is_fv_of_state' x st'1), is_fv_of_state' x (Sum st'1 st'2)
| isfvst'SumR  : forall x st'1 st'2 (isfvH : is_fv_of_state' x st'2), is_fv_of_state' x (Sum st'1 st'2)
| isfvst'ProdL : forall x st' g     (isfvH : is_fv_of_state' x st'),  is_fv_of_state' x (Prod st' g)
| isfvst'ProdR : forall x st' g     (isfvH : is_fv_of_goal x g),      is_fv_of_state' x (Prod st' g).

Hint Constructors is_fv_of_state'.

Inductive is_fv_of_state : name -> state -> Prop :=
| isfvstC : forall x st' (isfv'H : is_fv_of_state' x st'), is_fv_of_state x (State st').

Hint Constructors is_fv_of_state.

Inductive is_counter_of_state' : nat -> state' -> Prop :=
| iscst'Leaf  : forall g s n,                                            is_counter_of_state' n (Leaf g s n)
| iscst'SumL  : forall n st'1 st'2 (iscH : is_counter_of_state' n st'1), is_counter_of_state' n (Sum st'1 st'2)
| iscst'SumR  : forall n st'1 st'2 (iscH : is_counter_of_state' n st'2), is_counter_of_state' n (Sum st'1 st'2)
| iscst'Prod  : forall n st' g     (iscH : is_counter_of_state' n st'),  is_counter_of_state' n (Prod st' g).

Hint Constructors is_counter_of_state'.

Inductive well_formed_state' : state' -> Set :=
| wfLeaf : forall g s frn   (domLTCounter : forall x, in_subst_dom s x -> x < frn)
                            (vranLTCounter : forall x, in_subst_vran s x -> x < frn)
                            (FVLTCounter : forall x, is_fv_of_goal x g -> x < frn),
                            well_formed_state' (Leaf g s frn)
| wfSum  : forall st'1 st'2 (wfst'1 : well_formed_state' st'1)
                            (wfst'2 : well_formed_state' st'2),
                            well_formed_state' (Sum st'1 st'2)
| wfProd : forall st' g     (wfst': well_formed_state' st')
                            (FVLTCounter : forall x frn, is_counter_of_state' frn st' ->
                                                         is_fv_of_goal x g ->
                                                         x < frn),
                            well_formed_state' (Prod st' g).

Hint Constructors well_formed_state'.

Inductive well_formed_state : state -> Set :=
| wfEmpty    : well_formed_state Stop
| wfNonEmpty : forall st' (wfState : well_formed_state' st'), well_formed_state (State st').

Hint Constructors well_formed_state.

(* Labels *)
Inductive label : Set :=
(* nothing                                       *) | Step   : label
(* answer: (subst, first free semantic variable) *) | Answer : subst -> nat -> label.

(* Transitions *)
Inductive eval_step : state' -> label -> state -> Set :=
| FailS        : forall           s    n, eval_step (Leaf Fail s n) Step Stop
| UnifyFail    : forall t1 t2     s    n, unify (apply_subst s t1) (apply_subst s t2) None      -> eval_step (Leaf (Unify t1 t2) s n) Step Stop
| UnifySuccess : forall t1 t2     s s' n, unify (apply_subst s t1) (apply_subst s t2) (Some s') -> eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s s') n) Stop
| DisjS        : forall g1 g2     s    n, eval_step (Leaf (Disj g1 g2) s n) Step (State (Sum (Leaf g1 s n) (Leaf g2 s n)))
| ConjS        : forall g1 g2     s    n, eval_step (Leaf (Conj g1 g2) s n) Step (State (Prod (Leaf g1 s n) g2))
| FreshS       : forall fg        s    n, eval_step (Leaf (Fresh fg) s n)   Step (State (Leaf (fg n) s (S n)))
| InvokeS      : forall r arg     s    n, eval_step (Leaf (Invoke r arg) s n) Step (State (Leaf (proj1_sig (MiniKanrenSyntax.P r) arg) s n))
| SumE         : forall st1 st2        l (H: eval_step st1 l  Stop), eval_step (Sum st1 st2) l (State st2)
| SumNE        : forall st1 st1' st2   l, eval_step st1 l (State st1')             -> eval_step (Sum st1 st2) l (State (Sum st2 st1'))
| ProdSE       : forall st g            , eval_step st     Step         Stop       -> eval_step (Prod st g) Step Stop
| ProdAE       : forall st g s n        , eval_step st    (Answer s n)  Stop       -> eval_step (Prod st g) Step (State (Leaf g s n))
| ProdSNE      : forall st g     st'    , eval_step st     Step        (State st') -> eval_step (Prod st g) Step (State (Prod st' g))
| ProdANE      : forall st g s n st'    , eval_step st    (Answer s n) (State st') -> eval_step (Prod st g) Step (State (Sum (Leaf g s n) (Prod st' g))).

Hint Constructors eval_step.

Lemma counter_in_answer
      (st' : state')
      (s : subst)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s n) st) :
      is_counter_of_state' n st'.
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; auto.
Qed.

Lemma counter_in_next_state
      (n : nat)
      (st' st'_next : state')
      (l : label)
      (EV : eval_step st' l (State st'_next))
      (Hisc_st' :  is_counter_of_state' n st'_next) :
      exists n', n' <= n /\ is_counter_of_state' n' st'.
Proof.
  remember (State st'_next) as st.
  revert Heqst Hisc_st'. revert st'_next.
  induction EV; intros; good_inversion Heqst.
  { exists n. split.
    { constructor. }
    { good_inversion Hisc_st'; good_inversion iscH; auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion Hisc_st'; good_inversion iscH; auto. } }
  { good_inversion Hisc_st'. exists n0. split.
    { repeat constructor. }
    { auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion Hisc_st'; auto. } }
  { exists n. split.
    { constructor. }
    { auto. } }
  { specialize (IHEV st1' eq_refl). good_inversion Hisc_st'.
    { exists n. split.
      { constructor. }
      { auto. } }
    { apply IHEV in iscH. destruct iscH as [n' [Hle iscH]].
      exists n'; auto. } }
  { good_inversion Hisc_st'. exists n0.
    eapply counter_in_answer in EV. split; auto. }
  { specialize (IHEV st' eq_refl). good_inversion Hisc_st'.
    apply IHEV in iscH. destruct iscH as [n' [Hle iscH]].
    exists n'; auto.  }
  { specialize (IHEV st' eq_refl). good_inversion Hisc_st'.
    { good_inversion iscH. exists n0.
      eapply counter_in_answer in EV. split; auto. }
    { good_inversion iscH. apply IHEV in iscH0.
      destruct iscH0 as [n' [Hle iscH]]. exists n'; auto. } }
Qed.

Lemma well_formed_subst_in_answer
      (st' : state')
      (s : subst)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s n) st)
      (wf_st' : well_formed_state' st') :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; good_inversion wf_st'; auto.
  assert (FVt1 : forall x, In x (fv_term (apply_subst s0 t1)) -> x < n).
  { clear u s'. intros. induction t1.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply vranLTCounter. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt1_1; auto. intros. apply FVLTCounter.
        good_inversion H0; auto. apply fvUnifyL. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt1_2; auto. intros. apply FVLTCounter.
        good_inversion H0; auto. apply fvUnifyL. simpl.
        apply set_union_intro. right. auto. } } }
  assert (FVt2 : forall x, In x (fv_term (apply_subst s0 t2)) -> x < n).
  { clear u s'. intros. induction t2.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply vranLTCounter. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt2_1; auto. intros. apply FVLTCounter.
        good_inversion H0; auto. apply fvUnifyR. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt2_2; auto. intros. apply FVLTCounter.
        good_inversion H0; auto. apply fvUnifyR. simpl.
        apply set_union_intro. right. auto. } } }
  specialize (MGU_dom _ _ _ u). intro s'Dom.
  specialize (MGU_vran _ _ _ u). intro s'VRan.
  split.
  { intros. apply compose_dom in H. destruct H; auto.
    apply s'Dom in H. destruct H; auto. }
  { intros. apply compose_vran in H. destruct H; auto.
    apply s'VRan in H. destruct H; auto. }
Qed.

Lemma well_formedness_preservation
      (st' : state')
      (l : label)
      (st : state)
      (EV : eval_step st' l st)
      (wf_st' : well_formed_state' st') :
      well_formed_state st.
Proof.
  intros. induction EV; good_inversion wf_st'; auto.
  { constructor. auto. }
  { constructor. constructor; auto.
    intros. good_inversion H. subst. auto. }
  { constructor. constructor.
    1-2: intros; eapply lt_trans; eauto.
    intros. destruct (eq_nat_dec n x).
    { omega. }
    { apply Nat.lt_lt_succ_r. apply FVLTCounter. econstructor; eauto. } }
  { constructor. constructor; auto.
    specialize (proj2_sig (MiniKanrenSyntax.P r)). intro Hcc.
    simpl in Hcc. destruct Hcc as [Hcl _]. red in Hcl. red in Hcl. auto. }
  { specialize (IHEV wfst'1).
    good_inversion IHEV. auto. }
  { constructor. constructor.
    1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
    intros. apply FVLTCounter; auto. eapply counter_in_answer; eauto. }
  { specialize (IHEV wfst'). good_inversion IHEV.
    constructor. constructor; auto. intros.
    eapply counter_in_next_state in EV; eauto.
    destruct EV as [frn' [Hle Hisc]]. eapply lt_le_trans.
    2: eauto.
    auto. }
  { specialize (IHEV wfst'). good_inversion IHEV.
    constructor. constructor.
    { constructor.
      1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
      intros. apply FVLTCounter; auto.
      eapply counter_in_answer; eauto. }
    { constructor; auto. intros.
      eapply counter_in_next_state in EV; eauto.
      destruct EV as [frn' [Hle Hisc]]. eapply lt_le_trans.
      2: eauto.
      auto. } }
Qed.

Lemma eval_step_exists : forall (st' : state'), {l : label & {st : state & eval_step st' l st}}.
Proof.
  induction st'.
  * destruct g.
    1,3-6: repeat eexists; econstructor.
    + assert ({r & unify (apply_subst s t) (apply_subst s t0) r}). { apply unify_exists. }
      destruct H. destruct x.
      all: repeat eexists; eauto.
  * destruct IHst'1 as [l1 [st1 IH1]]. destruct st1.
    all: repeat eexists; eauto.
  * destruct IHst' as [l [st IH]]. destruct st; destruct l.
    all: repeat eexists; eauto.
Qed.

Lemma eval_step_unique :
  forall (st' : state') (l1 l2 : label) (st1 st2 : state),
    eval_step st' l1 st1 -> eval_step st' l2 st2 -> l1 = l2 /\ st1 = st2.
Proof.
  induction st'.
  * intros. destruct g; inversion H; inversion H0; subst; auto.
    + assert (C : None = Some s').
      { eapply unify_unique; eassumption. }
      inversion C.
    + assert (C : None = Some s').
      { eapply unify_unique; eassumption. }
      inversion C.
    + assert (C : Some s' = Some s'0).
      { eapply unify_unique; eassumption. }
      inversion C. auto.
  * intros. inversion H; inversion H0; subst;
    specialize (IHst'1 _ _ _ _ H5 H10); inversion IHst'1;
    inversion H2; subst; auto.
  * intros. inversion H; inversion H0; subst;
    specialize (IHst' _ _ _ _ H5 H10); inversion IHst'; subst;
    inversion H1; inversion H2; auto.
Qed.

(* Traces *)
Definition trace : Set := @stream label.

CoInductive op_sem : state -> trace -> Set :=
| osStop : op_sem Stop Nil
| osState : forall st' l st t (EV: eval_step st' l st)
                              (OP: op_sem st t),
                              op_sem (State st') (Cons l t).

Hint Constructors op_sem.

CoFixpoint trace_from (st : state) : trace :=
  match st with
  | Stop => Nil
  | State st' =>
    match eval_step_exists st' with
    | existT _ l (existT _ st'' ev_st'_st'') =>
      Cons l (trace_from st'')
    end
  end.

Lemma trace_from_correct : forall st, op_sem st (trace_from st).
Proof.
  cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl. destruct (eval_step_exists s).
    destruct s0. econstructor. eauto. eauto. }
Qed.

Lemma op_sem_exists (st : state) : {t : trace & op_sem st t}.
Proof.
  eexists. eapply trace_from_correct.
Qed.

Lemma op_sem_unique :
  forall st t1 t2, op_sem st t1 -> op_sem st t2 -> equal_streams t1 t2.
Proof.
  cofix CIH. intros. inversion H; inversion H0;
  rewrite <- H1 in H3; inversion H3.
  * constructor.
  * subst.
    specialize (eval_step_unique _ _ _ _ _ EV EV0).
    intro. destruct H1. constructor.
    + auto.
    + subst. eapply CIH; eauto.
Qed.

Lemma counter_in_trace
      (g : goal)
      (s sr : subst)
      (n nr : nat)
      (tr : trace)
      (OP : op_sem (State (Leaf g s n)) tr)
      (HIn : in_stream (Answer sr nr) tr) :
      n <= nr.
Proof.
  remember (Leaf g s n) as st'.
  assert (forall n', is_counter_of_state' n' st' -> n <= n').
  { intros. subst. good_inversion H. auto. }
  clear Heqst'. revert H OP. revert n st'.
  remember (Answer sr nr). induction HIn; intros; subst.
  { good_inversion OP. apply counter_in_answer in EV. auto. }
  { good_inversion OP. destruct st.
    { good_inversion OP0. good_inversion HIn. }
    { apply IHHIn with s0; auto. intros.
      specialize (counter_in_next_state _ _ _ _ EV H0). intros.
      destruct H1. destruct H1. apply H in H2.
      eapply le_trans; eauto. } }
Qed.

Lemma well_formed_subst_in_trace
      (st : state)
      (wf_st' : well_formed_state st)
      (t : trace)
      (OP : op_sem st t)
      (s : subst)
      (n : nat)
      (isAns: in_stream (Answer s n) t) :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). revert wf_st' OP. revert st.
  induction isAns; intros.
  { good_inversion OP. good_inversion wf_st'.
    eapply well_formed_subst_in_answer; eauto. }
  { good_inversion OP. good_inversion wf_st'.
    apply IHisAns with st0; auto.
    eapply well_formedness_preservation; eauto. }
Qed.

Lemma sum_op_sem : forall st'1 st'2 t1 t2 t, op_sem (State st'1) t1 ->
                                             op_sem (State st'2) t2 ->
                                             op_sem (State (Sum st'1 st'2)) t ->
                                             interleave t1 t2 t.
Proof.
  cofix CIH. intros. inversion H. subst. inversion H1. subst.
  inversion EV0; subst; specialize (eval_step_unique _ _ _ _ _ EV H6);
  intro; destruct H2; subst; constructor.
  * inversion OP. subst. specialize (op_sem_unique _ _ _ H0 OP0).
    intro. inversion H2; subst.
    + constructor. constructor.
    + constructor. constructor. auto.
  * eapply CIH; eassumption.
Qed.

Lemma disjunction_finite_commutativity :
  forall g1 g2 s n t12 t21
    (ops11 : op_sem (State (Leaf (Disj g1 g2) s n)) t12)
    (ops21 : op_sem (State (Leaf (Disj g2 g1) s n)) t21)
    (fin12 : finite t12), finite t21.
Proof.
  intros.
  inversion ops11; subst.
  inversion EV; subst.
  inversion fin12; subst.
  inversion ops21; subst.
  inversion EV0; subst.
  constructor.
  specialize (op_sem_exists (State (Leaf g1 s n))). intro. destruct H as [t1 OP1].
  specialize (op_sem_exists (State (Leaf g2 s n))). intro. destruct H as [t2 OP2].
  specialize (sum_op_sem _ _ _ _ _ OP1 OP2 OP). intro.
  specialize (sum_op_sem _ _ _ _ _ OP2 OP1 OP0). intro.
  specialize (interleave_finite _ _ _ H). intro.
  specialize (interleave_finite _ _ _ H1). intro.
  apply H3. apply and_comm. apply H2. auto.
Qed.

Lemma prod_op_sem_in
      (st' : state')
      (g : goal)
      (s : subst)
      (n : nat)
      (t1 t2 t : trace)
      (r : label)
      (OP : op_sem (State (Prod st' g)) t)
      (OP1 : op_sem (State st') t1)
      (OP2 : op_sem (State (Leaf g s n)) t2)
      (HIn1 : in_stream (Answer s n) t1)
      (HIn2 : in_stream r t2) :
      in_stream r t.
Proof.
  revert OP OP1. revert t st'. remember (Answer s n) as r1.
  induction HIn1; intros; subst.
  { good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV H3);
    intro eqs; destruct eqs; subst; good_inversion H.
    { constructor. specialize (op_sem_unique _ _ _ OP2 OP1).
      intros. eapply in_equal_streams; eauto. }
    { constructor. specialize (op_sem_exists (State (Leaf g s0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (State (Prod st'0 g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. left. specialize (op_sem_unique _ _ _ OP2 OP3).
      intros. eapply in_equal_streams; eauto. } }
  { specialize (IHHIn1 eq_refl).
    good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV H3);
    intro eqs; destruct eqs; subst.
    1-2: good_inversion OP0; good_inversion HIn1.
    { constructor. eapply IHHIn1; eauto. }
    { constructor. specialize (op_sem_exists (State (Leaf g s0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (State (Prod st'0 g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. right. eapply IHHIn1; eauto. } }
Qed.
