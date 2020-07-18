Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Omega.
Require Import Coq.Program.Equality.

Require Import Stream.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import DenotationalSem.
Require Import OperationalSem.


Module OperationalSemSoundnessAbstr (CS : ConstraintStoreSig).

Import CS.

Module OperationalSemCS := OperationalSemAbstr CS.

Import OperationalSemCS.

Lemma answer_correct
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (f : repr_fun)
      (DSS : [ s , f ])
      (DSCS : [| s , cs , f |])
      (st' : state')
      (WF : well_formed_state' st')
      (st : state)
      (EV : eval_step st' (Answer s cs n) st) :
      in_denotational_sem_state' st' f.
Proof.
  (* eapply wf_cs_in_answer in WF; eauto. *) remember (Answer s cs n) as l.
  induction EV; good_inversion Heql; good_inversion WF; auto.
  { assert (DSS_copy := DSS). apply (denotational_sem_uni _ _ _ _ MGU _) in DSS.
    destruct DSS as [DSS EQ]. constructor; auto.
    eapply proj1. apply (upd_cs_success_condition _ _ _ _ WF_CS UPD_CS f). auto. }
  { specialize (add_constraint_success_condition _ _ _ _ _ WF_CS ADD_C f). intro ADD_C_COND.
    specialize (conj DSCS DSS). intro CONJ. apply ADD_C_COND in CONJ.
    destruct CONJ as [DSCS0 [_ GT_NEQ]].
    constructor; auto. }
Qed.

Lemma next_state_correct
      (f : repr_fun)
      (st : state)
      (DSS : in_denotational_sem_state st f)
      (st' : state')
      (WF : well_formed_state' st')
      (h : label)
      (EV : eval_step st' h st) :
      in_denotational_sem_state' st' f.
Proof.
  induction EV; good_inversion DSS.
  { good_inversion DSST'; good_inversion DSST'0;
    constructor; auto. }
  { good_inversion DSST'. good_inversion DSST'0. auto. }
  { good_inversion WF. good_inversion DSST'.
    constructor; auto. econstructor; eauto.
    intros HIn. apply FV_LT_COUNTER in HIn.
    { omega. }
    { reflexivity. } }
  { good_inversion DSST'. auto. }
  { auto. }
  { good_inversion WF. good_inversion DSST'; auto. }
  { good_inversion WF. good_inversion DSST'. constructor; auto.
    eapply answer_correct; eauto. }
  { good_inversion WF. good_inversion DSST'. auto. }
  { good_inversion WF. good_inversion DSST'.
    { good_inversion DSST'0. constructor; auto.
      eapply answer_correct; eauto. }
    { good_inversion DSST'0. auto. } }
Qed.

Lemma search_correctness_generalized
      (st   : state)
      (WF   : well_formed_state st)
      (f    : repr_fun)
      (t    : trace)
      (HOP  : op_sem st t)
      (HDA  : {| t , f |}) :
      in_denotational_sem_state st f.
Proof.
  revert HOP WF. revert st.
  red in HDA. destruct HDA as [s [cs [n [HInStr [DSS DSCS]]]]].
  remember (Answer s cs n) as l. induction HInStr.
  { intros. good_inversion HOP. good_inversion WF.
    constructor. eapply answer_correct; eauto. }
  { specialize (IHHInStr Heql). intros.
    good_inversion HOP. good_inversion WF.
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
      (f   : repr_fun)
      (t   : trace)
      (HOP : op_sem (State (Leaf g empty_subst init_cs k)) t)
      (HDA : {| t , f |}) :
      [| g , f |].
Proof.
  remember (State (Leaf g empty_subst init_cs k)) as st.
  assert (in_denotational_sem_state st f).
  { eapply search_correctness_generalized; eauto.
    subst. constructor. apply well_formed_initial_state; auto. }
  subst. inversion H. inversion DSST'. auto.
Qed.

End OperationalSemSoundnessAbstr.
