
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Stream.
Require Import Omega.
Require Import Extraction.

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
| isfvst'Leaf  : forall x g s n     (X_FV_G : is_fv_of_goal x g),
                                    is_fv_of_state' x (Leaf g s n)
| isfvst'SumL  : forall x st'1 st'2 (X_FV : is_fv_of_state' x st'1),
                                    is_fv_of_state' x (Sum st'1 st'2)
| isfvst'SumR  : forall x st'1 st'2 (X_FV : is_fv_of_state' x st'2),
                                    is_fv_of_state' x (Sum st'1 st'2)
| isfvst'ProdL : forall x st' g     (X_FV : is_fv_of_state' x st'),
                                    is_fv_of_state' x (Prod st' g)
| isfvst'ProdR : forall x st' g     (X_FV : is_fv_of_goal x g),
                                    is_fv_of_state' x (Prod st' g).

Hint Constructors is_fv_of_state'.

Inductive is_fv_of_state : name -> state -> Prop :=
| isfvstC : forall x st' (X_FV_ST' : is_fv_of_state' x st'),
                         is_fv_of_state x (State st').

Hint Constructors is_fv_of_state.

Inductive is_counter_of_state' : nat -> state' -> Prop :=
| iscst'Leaf  : forall g s n,      is_counter_of_state' n (Leaf g s n)
| iscst'SumL  : forall n st'1 st'2 (ISC : is_counter_of_state' n st'1),
                                   is_counter_of_state' n (Sum st'1 st'2)
| iscst'SumR  : forall n st'1 st'2 (ISC : is_counter_of_state' n st'2),
                                   is_counter_of_state' n (Sum st'1 st'2)
| iscst'Prod  : forall n st' g     (ISC : is_counter_of_state' n st'),
                                   is_counter_of_state' n (Prod st' g).

Hint Constructors is_counter_of_state'.

Inductive well_formed_state' : state' -> Set :=
| wfLeaf : forall g s frn   (DOM_LT_COUNTER :  forall x (X_IN_DOM : in_subst_dom s x),
                                                        x < frn)
                            (VRAN_LT_COUNTER : forall x (X_IN_VRAN : in_subst_vran s x),
                                                        x < frn)
                            (FV_LT_COUNTER :   forall x (X_FV : is_fv_of_goal x g),
                                                        x < frn),
                            well_formed_state' (Leaf g s frn)
| wfSum  : forall st'1 st'2 (WF_L : well_formed_state' st'1)
                            (WF_R : well_formed_state' st'2),
                            well_formed_state' (Sum st'1 st'2)
| wfProd : forall st' g     (WF_L : well_formed_state' st')
                            (FV_LT_COUNTER : forall x frn (FRN_COUNTER : is_counter_of_state' frn st')
                                                          (X_FV : is_fv_of_goal x g),
                                                          x < frn),
                            well_formed_state' (Prod st' g).

Hint Constructors well_formed_state'.

Inductive well_formed_state : state -> Set :=
| wfEmpty    : well_formed_state Stop
| wfNonEmpty : forall st' (wfState : well_formed_state' st'),
                          well_formed_state (State st').

Hint Constructors well_formed_state.

(* Labels *)
Inductive label : Set :=
(* nothing                                       *) | Step   : label
(* answer: (subst, first free semantic variable) *) | Answer : subst -> nat -> label.

(* Transitions *)
Inductive eval_step : state' -> label -> state -> Set :=
| esFail         : forall           s    n, eval_step (Leaf Fail s n) Step Stop
| esCut          : forall           s    n, eval_step (Leaf Cut s n)  (Answer s n) Stop
| esUnifyFail    : forall t1 t2     s    n  (MGU : mgu (apply_subst s t1) (apply_subst s t2) None),
                                            eval_step (Leaf (Unify t1 t2) s n) Step Stop
| esUnifySuccess : forall t1 t2     s s' n  (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some s')),
                                            eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s s') n) Stop
| esDisj         : forall g1 g2     s    n, eval_step (Leaf (Disj g1 g2) s n) Step (State (Sum (Leaf g1 s n) (Leaf g2 s n)))
| esConj         : forall g1 g2     s    n, eval_step (Leaf (Conj g1 g2) s n) Step (State (Prod (Leaf g1 s n) g2))
| esFresh        : forall fg        s    n, eval_step (Leaf (Fresh fg) s n)   Step (State (Leaf (fg n) s (S n)))
| esInvoke       : forall r arg     s    n, eval_step (Leaf (Invoke r arg) s n) Step (State (Leaf (proj1_sig (MiniKanrenSyntax.P r) arg) s n))
| esSumE         : forall st1 st2        l  (STEP_L : eval_step st1 l  Stop),
                                            eval_step (Sum st1 st2) l (State st2)
| esSumNE        : forall st1 st1' st2   l  (STEP_L : eval_step st1 l (State st1')),
                                            eval_step (Sum st1 st2) l (State (Sum st2 st1'))
| esProdSE       : forall st g              (STEP_L : eval_step st Step Stop),
                                            eval_step (Prod st g) Step Stop
| esProdAE       : forall st g s n          (STEP_L : eval_step st (Answer s n) Stop),
                                            eval_step (Prod st g) Step (State (Leaf g s n))
| esProdSNE      : forall st g     st'      (STEP_L : eval_step st Step (State st')),
                                            eval_step (Prod st g) Step (State (Prod st' g))
| esProdANE      : forall st g s n st'      (STEP_L : eval_step st (Answer s n) (State st')),
                                            eval_step (Prod st g) Step (State (Sum (Leaf g s n) (Prod st' g))).

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
      (ISC_NEXT :  is_counter_of_state' n st'_next) :
      exists n', n' <= n /\ is_counter_of_state' n' st'.
Proof.
  remember (State st'_next) as st.
  revert Heqst ISC_NEXT. revert st'_next.
  induction EV; intros; good_inversion Heqst.
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { good_inversion ISC_NEXT. exists n0. split.
    { repeat constructor. }
    { auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; auto. } }
  { exists n. split.
    { constructor. }
    { auto. } }
  { specialize (IHEV st1' eq_refl). good_inversion ISC_NEXT.
    { exists n. split.
      { constructor. }
      { auto. } }
    { apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
      exists n'; auto. } }
  { good_inversion ISC_NEXT. exists n0.
    eapply counter_in_answer in EV. split; auto. }
  { specialize (IHEV st' eq_refl). good_inversion ISC_NEXT.
    apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
    exists n'; auto. }
  { specialize (IHEV st' eq_refl). good_inversion ISC_NEXT.
    { good_inversion ISC. exists n0.
      eapply counter_in_answer in EV. split; auto. }
    { good_inversion ISC. apply IHEV in ISC0.
      destruct ISC0 as [n' [LE ISC]]. exists n'; auto. } }
Qed.

Lemma well_formed_subst_in_answer
      (st' : state')
      (s : subst)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s n) st)
      (WF : well_formed_state' st') :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; good_inversion WF; auto.
  assert (FV_LT_N_1 : forall x, In x (fv_term (apply_subst s0 t1)) -> x < n).
  { clear MGU s'. intros. induction t1.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt1_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt1_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. right. auto. } } }
  assert (FV_LT_N_2 : forall x, In x (fv_term (apply_subst s0 t2)) -> x < n).
  { clear MGU s'. intros. induction t2.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt2_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt2_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. right. auto. } } }
  specialize (mgu_dom _ _ _ MGU). intro S'_DOM.
  specialize (mgu_vran _ _ _ MGU). intro S'_VRAN.
  split.
  { intros. apply compose_dom in H. destruct H; auto.
    apply S'_DOM in H. destruct H; auto. }
  { intros. apply compose_vran in H. destruct H; auto.
    apply S'_VRAN in H. destruct H; auto. }
Qed.

Lemma well_formedness_preservation
      (st' : state')
      (l : label)
      (st : state)
      (EV : eval_step st' l st)
      (WF : well_formed_state' st') :
      well_formed_state st.
Proof.
  intros. induction EV; good_inversion WF; auto.
  { constructor. auto. }
  { constructor. constructor; auto.
    intros. good_inversion FRN_COUNTER. subst. auto. }
  { constructor. constructor.
    1-2: intros; eapply lt_trans; eauto.
    intros. destruct (eq_nat_dec n x).
    { omega. }
    { apply Nat.lt_lt_succ_r. apply FV_LT_COUNTER. econstructor; eauto. } }
  { constructor. constructor; auto.
    specialize (proj2_sig (MiniKanrenSyntax.P r)). intro CC.
    simpl in CC. destruct CC as [CL _]. red in CL. red in CL. auto. }
  { specialize (IHEV WF_L).
    good_inversion IHEV. auto. }
  { constructor. constructor.
    1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
    intros. apply FV_LT_COUNTER; auto. eapply counter_in_answer; eauto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor; auto. intros.
    eapply counter_in_next_state in EV; eauto.
    destruct EV as [frn' [LE ISC]]. eapply lt_le_trans.
    2: eauto.
    auto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor.
    { constructor.
      1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
      intros. apply FV_LT_COUNTER; auto.
      eapply counter_in_answer; eauto. }
    { constructor; auto. intros.
      eapply counter_in_next_state in EV; eauto.
      destruct EV as [frn' [Le ISC]]. eapply lt_le_trans.
      2: eauto.
      auto. } }
Qed.

Lemma eval_step_exists
      (st' : state') :
      {l : label & {st : state & eval_step st' l st}}.
Proof.
  induction st'.
  { destruct g.
    1-2,4-7: repeat eexists; econstructor.
    { assert ({r & mgu (apply_subst s t) (apply_subst s t0) r}).
      { apply mgu_exists. }
      destruct H. destruct x.
      all: repeat eexists; eauto. } }
  { destruct IHst'1 as [l1 [st1 IH1]]. destruct st1.
    all: repeat eexists; eauto. }
  { destruct IHst' as [l [st IH]]. destruct st; destruct l.
    all: repeat eexists; eauto. }
Qed.

Lemma eval_step_unique
      (st' : state')
      (l1 l2 : label)
      (st1 st2 : state)
      (STEP_1 : eval_step st' l1 st1)
      (STEP_2 : eval_step st' l2 st2) :
      l1 = l2 /\ st1 = st2.
Proof.
  revert STEP_1 STEP_2. revert l1 l2 st1 st2. induction st'.
  { intros. destruct g; good_inversion STEP_1; good_inversion STEP_2; auto.
    { assert (C : None = Some s').
      { eapply mgu_unique; eassumption. }
      inversion C. }
    { assert (C : None = Some s').
      { eapply mgu_unique; eassumption. }
      inversion C. }
    { assert (C : Some s' = Some s'0).
      { eapply mgu_unique; eassumption. }
      inversion C. auto. } }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHst'1 _ _ _ _ STEP_L STEP_L0); inversion IHst'1;
    inversion H0; subst; auto. }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHst' _ _ _ _ STEP_L STEP_L0); inversion IHst'; subst;
    inversion H; inversion H0; auto. }
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

Lemma trace_from_correct 
      (st : state) :
      op_sem st (trace_from st).
Proof.
  revert st. cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl. destruct (eval_step_exists s).
    destruct s0. econstructor; eauto. }
Qed.

Lemma op_sem_exists
      (st : state) :
      {t : trace & op_sem st t}.
Proof.
  eexists. eapply trace_from_correct.
Qed.

Extraction Language Haskell.

Extraction "extracted/interpreter.hs" op_sem_exists.

Lemma op_sem_unique
      (st : state)
      (t1 t2 : trace)
      (OP_1 : op_sem st t1)
      (OP_2 : op_sem st t2) :
      equal_streams t1 t2.
Proof.
  revert OP_1 OP_2. revert t1 t2 st.
  cofix CIH. intros. inversion OP_1; inversion OP_2;
  rewrite <- H1 in H; inversion H.
  { constructor. }
  { subst.
    specialize (eval_step_unique _ _ _ _ _ EV EV0).
    intros [EQL EQST]. constructor.
    { auto. }
    { subst. eapply CIH; eauto. } }
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
  assert (CNT_GE : forall n', is_counter_of_state' n' st' -> n <= n').
  { intros. subst. good_inversion H. auto. }
  clear Heqst'. revert CNT_GE OP. revert n st'.
  remember (Answer sr nr). induction HIn; intros; subst.
  { good_inversion OP. apply counter_in_answer in EV. auto. }
  { good_inversion OP. destruct st.
    { good_inversion OP0. good_inversion HIn. }
    { apply IHHIn with s0; auto. intros.
      specialize (counter_in_next_state _ _ _ _ EV H). intros.
      destruct H0. destruct H0. apply CNT_GE in H1.
      eapply le_trans; eauto. } }
Qed.

Lemma well_formed_subst_in_trace
      (st : state)
      (WF : well_formed_state st)
      (t : trace)
      (OP : op_sem st t)
      (s : subst)
      (n : nat)
      (IS_ANS: in_stream (Answer s n) t) :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). revert WF OP. revert st.
  induction IS_ANS; intros.
  { good_inversion OP. good_inversion WF.
    eapply well_formed_subst_in_answer; eauto. }
  { good_inversion OP. good_inversion WF.
    apply IHIS_ANS with st0; auto.
    eapply well_formedness_preservation; eauto. }
Qed.

Lemma sum_op_sem
      (st'1 st'2 : state')
      (t1 t2 t : trace)
      (OP_1 : op_sem (State st'1) t1)
      (OP_2 : op_sem (State st'2) t2)
      (OP_12 : op_sem (State (Sum st'1 st'2)) t) :
      interleave t1 t2 t.
Proof.
  revert OP_1 OP_2 OP_12. revert t1 t2 t st'1 st'2.
  cofix CIH. intros. inversion OP_1. subst. inversion OP_12. subst.
  inversion EV0; subst; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
  intros [EQL EQST]; subst; constructor.
  { inversion OP. subst. specialize (op_sem_unique _ _ _ OP_2 OP0).
    intro EQS. inversion EQS; subst.
    { constructor. constructor. }
    { constructor. constructor. auto. } }
  { eapply CIH; eassumption. }
Qed.

Lemma disjunction_finite_commutativity
      (g1 g2 : goal)
      (s : subst)
      (n : nat)
      (t12 t21 : trace)
      (OP_12 : op_sem (State (Leaf (Disj g1 g2) s n)) t12)
      (OP_21 : op_sem (State (Leaf (Disj g2 g1) s n)) t21)
      (FIN_12 : finite t12) :
      finite t21.
Proof.
  intros.
  inversion OP_12; subst.
  inversion EV; subst.
  inversion FIN_12; subst.
  inversion OP_21; subst.
  inversion EV0; subst.
  constructor.
  specialize (op_sem_exists (State (Leaf g1 s n))). intro. destruct H as [t1 OP1].
  specialize (op_sem_exists (State (Leaf g2 s n))). intro. destruct H as [t2 OP2].
  specialize (sum_op_sem _ _ _ _ _ OP1 OP2 OP). intro.
  specialize (sum_op_sem _ _ _ _ _ OP2 OP1 OP0). intro.
  specialize (interleave_finite _ _ _ H). intro.
  specialize (interleave_finite _ _ _ H0). intro.
  apply H2. apply and_comm. apply H1. auto.
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
      (IN_1 : in_stream (Answer s n) t1)
      (IN_2 : in_stream r t2) :
      in_stream r t.
Proof.
  revert OP OP1. revert t st'. remember (Answer s n) as r1.
  induction IN_1; intros; subst.
  { good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
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
  { specialize (IHIN_1 eq_refl).
    good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
    intro eqs; destruct eqs; subst.
    1-2: good_inversion OP0; good_inversion IN_1.
    { constructor. eapply IHIN_1; eauto. }
    { constructor. specialize (op_sem_exists (State (Leaf g s0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (State (Prod st'0 g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. right. eapply IHIN_1; eauto. } }
Qed.
