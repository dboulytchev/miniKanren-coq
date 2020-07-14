Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Extraction.

Require Import Unification.
Require Import Streams.
Require Import Language.
Require Import DenotationalSem.


(************************* States *************************)

Inductive nt_state : Set :=
| Leaf : goal -> subst -> nat -> nt_state
| Sum  : nt_state -> nt_state -> nt_state
| Prod : nt_state -> goal   -> nt_state.

Inductive state : Set :=
| Stop  : state
| NTState : nt_state -> state.

Inductive is_fv_of_nt_state : name -> nt_state -> Prop :=
| isfvnstLeaf  : forall x g s n  (X_FV_G : is_fv_of_goal x g),
                                    is_fv_of_nt_state x (Leaf g s n)
| isfvnstSumL  : forall x nst1 nst2 (X_FV : is_fv_of_nt_state x nst1),
                                    is_fv_of_nt_state x (Sum nst1 nst2)
| isfvnstSumR  : forall x nst1 nst2 (X_FV : is_fv_of_nt_state x nst2),
                                    is_fv_of_nt_state x (Sum nst1 nst2)
| isfvnstProdL : forall x nst g     (X_FV : is_fv_of_nt_state x nst),
                                    is_fv_of_nt_state x (Prod nst g)
| isfvnstProdR : forall x nst g     (X_FV : is_fv_of_goal x g),
                                    is_fv_of_nt_state x (Prod nst g).

Hint Constructors is_fv_of_nt_state : core.

Inductive is_fv_of_state : name -> state -> Prop :=
| isfvstC : forall x nst (X_FV_NT_ST : is_fv_of_nt_state x nst),
                         is_fv_of_state x (NTState nst).

Hint Constructors is_fv_of_state : core.

Inductive is_counter_of_nt_state : nat -> nt_state -> Prop :=
| iscnstLeaf  : forall g s n,      is_counter_of_nt_state n (Leaf g s n)
| iscnstSumL  : forall n nst1 nst2 (ISC : is_counter_of_nt_state n nst1),
                                   is_counter_of_nt_state n (Sum nst1 nst2)
| iscnstSumR  : forall n nst1 nst2 (ISC : is_counter_of_nt_state n nst2),
                                   is_counter_of_nt_state n (Sum nst1 nst2)
| iscnstProd  : forall n nst g     (ISC : is_counter_of_nt_state n nst),
                                   is_counter_of_nt_state n (Prod nst g).

Hint Constructors is_counter_of_nt_state : core.

Inductive well_formed_nt_state : nt_state -> Prop :=
| wfLeaf : forall g s frn
           (DOM_LT_COUNTER  : forall x (X_IN_DOM : in_subst_dom s x), x < frn)
           (VRAN_LT_COUNTER : forall x (X_IN_VRAN : in_subst_vran s x), x < frn)
           (FV_LT_COUNTER   : forall x (X_FV : is_fv_of_goal x g), x < frn),
           well_formed_nt_state (Leaf g s frn)
| wfSum  : forall nst1 nst2 (WF_L : well_formed_nt_state nst1)
                            (WF_R : well_formed_nt_state nst2),
                            well_formed_nt_state (Sum nst1 nst2)
| wfProd : forall nst g     (WF_L : well_formed_nt_state nst)
                            (FV_LT_COUNTER : forall x frn (FRN_COUNTER : is_counter_of_nt_state frn nst)
                                                          (X_FV : is_fv_of_goal x g),
                                                          x < frn),
                            well_formed_nt_state (Prod nst g).

Hint Constructors well_formed_nt_state : core.

Fixpoint first_nats (k : nat) : list nat :=
  match k with
  | 0   => []
  | S n => n :: first_nats n
  end.

Lemma first_nats_less (n k : nat) (H : In n (first_nats k)) : n < k.
Proof.
  induction k.
  { inversion H. }
  { inversion H. { omega. } { apply IHk in H0. omega. } }
Qed.

Lemma well_formed_initial_state
      (g   : goal)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g) :
      well_formed_nt_state (Leaf g empty_subst k).
Proof.
  constructor.
  { intros. good_inversion X_IN_DOM. good_inversion H. }
  { intros. good_inversion X_IN_VRAN. destruct H as [t0 [H0 _]]. good_inversion H0. }
  { red in HC. intros. apply first_nats_less; auto. }
Qed.


Inductive well_formed_state : state -> Prop :=
| wfTerminal    : well_formed_state Stop
| wfNonTerminal : forall nst (wfState : well_formed_nt_state nst),
                             well_formed_state (NTState nst).

Hint Constructors well_formed_state : core.



(************************** LTS ***************************)
(* Labels *)
Inductive label : Set :=
| Step   : label
| Answer : subst -> nat -> label.

(* Transitions *)
Inductive eval_step : nt_state -> label -> state -> Prop :=
| esFail    : forall s n, eval_step (Leaf Fail s n) Step Stop
| esUnifyFail    : forall t1 t2 s   n (MGU : mgu (apply_subst s t1) (apply_subst s t2) None),
                                      eval_step (Leaf (Unify t1 t2) s n) Step Stop
| esUnifySuccess : forall t1 t2 s d n (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some d)),
                                      eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s d) n) Stop
| esDisj         : forall g1 g2 s n, eval_step (Leaf (Disj g1 g2) s n)   Step (NTState (Sum (Leaf g1 s n) (Leaf g2 s n)))
| esConj         : forall g1 g2 s n, eval_step (Leaf (Conj g1 g2) s n)   Step (NTState (Prod (Leaf g1 s n) g2))
| esFresh        : forall fg    s n, eval_step (Leaf (Fresh fg) s n)     Step (NTState (Leaf (fg n) s (S n)))
| esInvoke       : forall r arg s n, eval_step (Leaf (Invoke r arg) s n) Step (NTState (Leaf (proj1_sig (Language.Prog r) arg) s n))
| esSumE         : forall nst1       nst2 l (STEP_L : eval_step nst1 l  Stop),
                                            eval_step (Sum nst1 nst2) l (NTState nst2)
| esSumNE        : forall nst1 nst1' nst2 l (STEP_L : eval_step nst1 l (NTState nst1')),
                                            eval_step (Sum nst1 nst2) l (NTState (Sum nst2 nst1'))
| esProdSE       : forall nst g          (STEP_L : eval_step nst Step Stop),
                                         eval_step (Prod nst g) Step Stop
| esProdAE       : forall nst g s n      (STEP_L : eval_step nst (Answer s n) Stop),
                                         eval_step (Prod nst g) Step (NTState (Leaf g s n))
| esProdSNE      : forall nst g     nst' (STEP_L : eval_step nst Step (NTState nst')),
                                         eval_step (Prod nst g) Step (NTState (Prod nst' g))
| esProdANE      : forall nst g s n nst' (STEP_L : eval_step nst (Answer s n) (NTState nst')),
                                         eval_step (Prod nst g) Step (NTState (Sum (Leaf g s n) (Prod nst' g))).

Hint Constructors eval_step : core.

Lemma counter_in_answer
      (nst : nt_state)
      (s : subst)
      (n : nat)
      (st : state)
      (EV : eval_step nst (Answer s n) st) :
      is_counter_of_nt_state n nst.
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; auto.
Qed.

Lemma counter_in_next_state
      (n : nat)
      (nst nst_next : nt_state)
      (l : label)
      (EV : eval_step nst l (NTState nst_next))
      (ISC_NEXT :  is_counter_of_nt_state n nst_next) :
      exists n', n' <= n /\ is_counter_of_nt_state n' nst.
Proof.
  remember (NTState nst_next) as st.
  revert Heqst ISC_NEXT. revert nst_next.
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
  { specialize (IHEV nst1' eq_refl). good_inversion ISC_NEXT.
    { exists n. split.
      { constructor. }
      { auto. } }
    { apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
      exists n'; auto. } }
  { good_inversion ISC_NEXT. exists n0.
    eapply counter_in_answer in EV. split; auto. }
  { specialize (IHEV nst' eq_refl). good_inversion ISC_NEXT.
    apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
    exists n'; auto. }
  { specialize (IHEV nst' eq_refl). good_inversion ISC_NEXT.
    { good_inversion ISC. exists n0.
      eapply counter_in_answer in EV. split; auto. }
    { good_inversion ISC. apply IHEV in ISC0.
      destruct ISC0 as [n' [LE ISC]]. exists n'; auto. } }
Qed.

Lemma well_formed_subst_in_answer
      (nst : nt_state)
      (s : subst)
      (n : nat)
      (st : state)
      (EV : eval_step nst (Answer s n) st)
      (WF : well_formed_nt_state nst) :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; good_inversion WF; auto.
  assert (FV_LT_N_1 : forall x, In x (fv_term (apply_subst s0 t1)) -> x < n).
  { clear MGU. clear d. intros. induction t1.
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
  { clear MGU. clear d. intros. induction t2.
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
      (nst : nt_state)
      (l : label)
      (st : state)
      (EV : eval_step nst l st)
      (WF : well_formed_nt_state nst) :
      well_formed_state st.
Proof.
  intros. induction EV; good_inversion WF; auto.
  { constructor. auto. }
  { constructor. constructor; auto.
    intros. good_inversion FRN_COUNTER. subst. auto. }
  { constructor. constructor; auto.
    1-2: intros; eapply lt_trans; eauto.
    intros. destruct (eq_nat_dec n x).
    { omega. }
    { apply Nat.lt_lt_succ_r. apply FV_LT_COUNTER. econstructor; eauto. } }
  { constructor. constructor; auto.
    specialize (proj2_sig (Language.Prog r)). intro CC.
    simpl in CC. destruct CC as [CL _]. red in CL. red in CL. auto. }
  { specialize (IHEV WF_L).
    good_inversion IHEV. auto. }
  { constructor. constructor; auto.
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
      (nst : nt_state) :
      {l : label & {st : state & eval_step nst l st}}.
Proof.
  induction nst.
  { destruct g.
    1,3-6: repeat eexists; econstructor.
    { assert ({r & mgu (apply_subst s t) (apply_subst s t0) r}).
      { apply mgu_result_exists. }
      destruct H. destruct x.
      { repeat eexists; eauto. }
      { repeat eexists; eauto. } } }
  { destruct IHnst1 as [l1 [st1 IH1]]. destruct st1.
    all: repeat eexists; eauto. }
  { destruct IHnst as [l [st IH]]. destruct st; destruct l.
    all: repeat eexists; eauto. }
Defined.

Lemma eval_step_unique
      (nst : nt_state)
      (l1 l2 : label)
      (st1 st2 : state)
      (STEP_1 : eval_step nst l1 st1)
      (STEP_2 : eval_step nst l2 st2) :
      l1 = l2 /\ st1 = st2.
Proof.
  revert STEP_1 STEP_2. revert l1 l2 st1 st2. induction nst.
  { intros. destruct g; good_inversion STEP_1; good_inversion STEP_2; auto.
    { assert (C : None = Some d).
      { eapply mgu_result_unique; eassumption. }
      inversion C. }
    { assert (C : None = Some d).
      { eapply mgu_result_unique; eassumption. }
      inversion C. }
    { assert (EQ : Some d = Some d0).
      { eapply mgu_result_unique; eassumption. }
      good_inversion EQ. auto. } }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHnst1 _ _ _ _ STEP_L STEP_L0); inversion IHnst1;
    inversion H0; subst; auto. }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHnst _ _ _ _ STEP_L STEP_L0); inversion IHnst; subst;
    inversion H; inversion H0; auto. }
Qed.



(***************** Operational Semantics ******************)

Definition trace : Set := @stream label.

CoInductive op_sem : state -> trace -> Prop :=
| osStop : op_sem Stop Nil
| osNTState : forall nst l st t (EV: eval_step nst l st)
                                (OP: op_sem st t),
                                op_sem (NTState nst) (Cons l t).

Hint Constructors op_sem : core.

CoFixpoint trace_from (st : state) : trace :=
  match st with
  | Stop => Nil
  | NTState nst =>
    match eval_step_exists nst with
    | existT _ l (existT _ nst' ev_nst_nst') =>
      Cons l (trace_from nst')
    end
  end.

Lemma trace_from_correct
      (st : state) :
      op_sem st (trace_from st).
Proof.
  revert st. cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl. destruct (eval_step_exists n).
    destruct s. econstructor; eauto. }
Qed.

Lemma op_sem_exists
      (st : state) :
      {t : trace & op_sem st t}.
Proof.
  eexists. eapply trace_from_correct.
Defined.

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

Definition in_denotational_analog (t : trace) (f : repr_fun) : Prop :=
  exists (s : subst) (n : nat),
    in_stream (Answer s n) t /\ [ s ,  f ].

Notation "{| t , f |}" := (in_denotational_analog t f).

Lemma counter_in_trace
      (g : goal)
      (s sr : subst)
      (n nr : nat)
      (tr : trace)
      (OP : op_sem (NTState (Leaf g s n)) tr)
      (HIn : in_stream (Answer sr nr) tr) :
      n <= nr.
Proof.
  remember (Leaf g s n) as nst.
  assert (CNT_GE : forall n', is_counter_of_nt_state n' nst -> n <= n').
  { intros. subst. good_inversion H. auto. }
  clear Heqnst. revert CNT_GE OP. revert n nst.
  remember (Answer sr nr). induction HIn; intros; subst.
  { good_inversion OP. apply counter_in_answer in EV. auto. }
  { good_inversion OP. destruct st.
    { good_inversion OP0. good_inversion HIn. }
    { apply IHHIn with n0; auto. intros.
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
      (nst1 nst2 : nt_state)
      (t1 t2 t : trace)
      (OP_1 : op_sem (NTState nst1) t1)
      (OP_2 : op_sem (NTState nst2) t2)
      (OP_12 : op_sem (NTState (Sum nst1 nst2)) t) :
      interleave t1 t2 t.
Proof.
  revert OP_1 OP_2 OP_12. revert t1 t2 t nst1 nst2.
  cofix CIH. intros. inversion OP_1. subst. inversion OP_12. subst.
  inversion EV0; subst; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
  intros [EQL EQST]; subst; constructor.
  { inversion OP. subst. specialize (op_sem_unique _ _ _ OP_2 OP0).
    intro EQS. inversion EQS; subst.
    { constructor. constructor. }
    { constructor. constructor. auto. } }
  { eapply CIH; eassumption. }
Qed.

Lemma sum_op_sem_in
      (nst1 nst2 : nt_state)
      (t1 t2 t : trace)
      (r : label)
      (OP_1 : op_sem (NTState nst1) t1)
      (OP_2 : op_sem (NTState nst2) t2)
      (OP_12 : op_sem (NTState (Sum nst1 nst2)) t) :
      in_stream r t <-> in_stream r t1 \/ in_stream r t2.
Proof.
  apply interleave_in. eapply sum_op_sem; eauto.
Qed.

Lemma disj_termination
      (g1 g2 : goal)
      (s : subst)
      (n : nat)
      (t1 t2 t : trace)
      (r : label)
      (OP_1 : op_sem (NTState (Leaf g1 s n)) t1)
      (OP_2 : op_sem (NTState (Leaf g2 s n)) t2)
      (OP_12 : op_sem (NTState (Leaf (Disj g1 g2) s n)) t) :
      finite t <-> finite t1 /\ finite t2.
Proof.
  good_inversion OP_12. good_inversion EV.
  assert (forall t, finite (Cons Step t) <-> finite t).
  { intros; split; intros H.
    { inversion H; auto. }
    { constructor; auto. } }
  eapply RelationClasses.iff_Transitive. eapply (H t0).
  apply interleave_finite. eapply sum_op_sem; eauto.
Qed.

Lemma prod_op_sem_in
      (nst : nt_state)
      (g : goal)
      (s : subst)
      (n : nat)
      (t1 t2 t : trace)
      (r : label)
      (OP : op_sem (NTState (Prod nst g)) t)
      (OP1 : op_sem (NTState nst) t1)
      (OP2 : op_sem (NTState (Leaf g s n)) t2)
      (IN_1 : in_stream (Answer s n) t1)
      (IN_2 : in_stream r t2) :
      in_stream r t.
Proof.
  revert OP OP1. revert t nst. remember (Answer s n) as r1.
  induction IN_1; intros; subst.
  { good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
    intro eqs; destruct eqs; subst; good_inversion H.
    { constructor. specialize (op_sem_unique _ _ _ OP2 OP1).
      intros. eapply in_equal_streams; eauto. }
    { constructor. specialize (op_sem_exists (NTState (Leaf g s0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (NTState (Prod nst' g))).
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
    { constructor. specialize (op_sem_exists (NTState (Leaf g s0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (NTState (Prod nst' g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. right. eapply IHIN_1; eauto. } }
Qed.

Extraction Language Haskell.

Extraction "extracted/interleaving_interpreter.hs" op_sem_exists.
