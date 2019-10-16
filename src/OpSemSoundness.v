
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Stream.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import OperationalSem.
Require Import DenotationalSem.
Require Import Omega.

Definition in_denotational_sem_subst (s : subst) (f : gt_fun) : Prop :=
  exists (f' : gt_fun), gt_fun_eq (subst_gt_fun_compose s f') f.

Definition in_denotational_analog (t : trace) (f : gt_fun) : Prop :=
  exists (s : subst) (n : nat), in_stream (Answer s n) t /\ in_denotational_sem_subst s f.

Inductive in_denotational_sem_state' : state' -> gt_fun -> Prop :=
| dsst'Leaf : forall g s n f (DSG : in_denotational_sem_goal g f)
                             (DSS : in_denotational_sem_subst s f),
                             in_denotational_sem_state' (Leaf g s n) f
| dsst'SumL : forall st1' st2' f (DSST' : in_denotational_sem_state' st1' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'SumR : forall st1' st2' f (DSST' : in_denotational_sem_state' st2' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'Prod : forall st' g f (DSG : in_denotational_sem_goal g f)
                             (DSST' : in_denotational_sem_state' st' f),
                             in_denotational_sem_state' (Prod st' g) f.

Hint Constructors in_denotational_sem_state'.

Inductive in_denotational_sem_state : state -> gt_fun -> Prop :=
| dsstState : forall st' f (DSST' : in_denotational_sem_state' st' f),
                           in_denotational_sem_state (State st') f.

Hint Constructors in_denotational_sem_state.


Lemma answer_correct
      (s : subst)
      (n : nat)
      (f : gt_fun)
      (DSS : in_denotational_sem_subst s f)
      (st' : state')
      (st : state)
      (EV : eval_step st' (Answer s n) st) :
      in_denotational_sem_state' st' f.
Proof.
  remember (Answer s n) as l.
  induction EV; good_inversion Heql.
  1, 3-4: auto.
  destruct DSS as [f' ff'_con].
  constructor.
  { constructor. red.
    specialize (gt_fun_eq_apply _ _ t1 ff'_con). intro. rewrite <- H.
    specialize (gt_fun_eq_apply _ _ t2 ff'_con). intro. rewrite <- H0.
    rewrite gt_fun_apply_compose. rewrite gt_fun_apply_compose.
    rewrite compose_correctness. rewrite compose_correctness.
    apply mgu_unifies in MGU. rewrite MGU. reflexivity. }
  { red. exists (subst_gt_fun_compose s' f').
    red. intros. red.
    red in ff'_con. specialize (ff'_con x). red in ff'_con.
    rewrite <- ff'_con. unfold subst_gt_fun_compose.
    replace (fun x0 : name => apply_gt_fun f' (apply_subst s' (Var x0)))
      with (subst_gt_fun_compose s' f').
    2: reflexivity.
    rewrite gt_fun_apply_compose. rewrite compose_correctness.
    reflexivity. }
Qed.

Lemma next_state_correct
      (f : gt_fun)
      (st : state)
      (DSS : in_denotational_sem_state st f)
      (st' : state')
      (WF : well_formed_state' st')
      (h : label)
      (EV : eval_step st' h st) :
      in_denotational_sem_state' st' f.
Proof.
  induction EV; good_inversion DSS.
  { good_inversion DSST'; good_inversion DSST'0; constructor; auto. }
  { good_inversion DSST'. good_inversion DSST'0. auto. }
  { good_inversion WF. good_inversion DSST'.
    constructor; auto. econstructor; eauto.
    intros HIn. apply FV_LT_COUNTER in HIn.
    { omega. }
    { reflexivity. } }
  { good_inversion DSST'. auto. }
  { auto. }
  { good_inversion WF. good_inversion DSST'; auto. }
  { good_inversion DSST'. constructor; auto.
    eapply answer_correct; eauto. }
  { good_inversion WF. good_inversion DSST'. auto. }
  { good_inversion WF. good_inversion DSST'.
    { good_inversion DSST'0. constructor; auto.
      eapply answer_correct; eauto. }
    { good_inversion DSST'0. auto. } }
Qed.

Lemma search_correctness_generalized
      (st   : state)
      (WF : well_formed_state st)
      (f    : gt_fun)
      (t    : trace)
      (HOP  : op_sem st t)
      (HDA  : in_denotational_analog t f) :
      in_denotational_sem_state st f.
Proof.
  revert HOP WF. revert st.
  red in HDA. destruct HDA as [s [n [HInStr DSS]]].
  remember (Answer s n) as l. induction HInStr.
  { intros. inversion HOP; clear HOP; subst.
    constructor. eapply answer_correct; eauto. }
  { specialize (IHHInStr Heql). intros.
    inversion HOP; clear HOP; subst.
    inversion WF; clear WF; subst.
    specialize (well_formedness_preservation _ _ _ EV wfState).
    intro wf_st0.
    specialize (IHHInStr st0 OP wf_st0).
    constructor. eapply next_state_correct; eauto. }
Qed.

Fixpoint first_nats (k : nat) : list nat :=
  match k with
  | 0   => []
  | S n => n :: first_nats n
  end.

Lemma first_nats_less
      (n k : nat)
      (H : In n (first_nats k)) :
      n < k.
Proof.
  induction k.
  { inversion H. }
  { inversion H. { omega. } { apply IHk in H0. omega. } }
Qed.

Lemma search_correctness
      (g   : goal)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g)
      (f   : gt_fun)
      (t   : trace)
      (HOP : op_sem (State (Leaf g empty_subst k)) t)
      (HDA : in_denotational_analog t f) : in_denotational_sem_goal g f.
Proof.
  remember (State (Leaf g empty_subst k)) as st.
  assert (in_denotational_sem_state st f).
  { eapply search_correctness_generalized; eauto.
    subst. constructor. constructor.
    { intros. good_inversion X_IN_DOM. good_inversion H. }
    { intros. good_inversion X_IN_VRAN. destruct H as [t0 [H0 _]]. good_inversion H0. }
    { intros. apply HC in X_FV. apply first_nats_less. auto. } }
  subst. inversion H. inversion DSST'. auto.
Qed.
