Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Omega.

Require Import Unification.
Require Import Streams.
Require Import LanguageSLD.
Require Import DenotationalSemSLD.
Require Import OperationalSemSLD.

Inductive in_denotational_sem_nt_state : nt_state -> repr_fun -> Prop :=
| dsnstLeaf : forall g s n f (DSG  : [| g , f |])
                             (DSS  : [ s , f ]),
                             in_denotational_sem_nt_state (Leaf g s n) f
| dsnstSumL : forall m nst1 nst2 f (DSST' : in_denotational_sem_nt_state nst1 f),
                                 in_denotational_sem_nt_state (Sum m nst1 nst2) f
| dsnstSumR : forall m nst1 nst2 f (DSST' : in_denotational_sem_nt_state nst2 f),
                                 in_denotational_sem_nt_state (Sum m nst1 nst2) f
| dsnstProd : forall nst g f (DSG : [| g , f |])
                             (DSST' : in_denotational_sem_nt_state nst f),
                             in_denotational_sem_nt_state (Prod nst g) f.

Hint Constructors in_denotational_sem_nt_state : core.

Inductive in_denotational_sem_state : state -> repr_fun -> Prop :=
| dsstNTState : forall nst f (DSST' : in_denotational_sem_nt_state nst f),
                           in_denotational_sem_state (NTState nst) f.

Hint Constructors in_denotational_sem_state : core.


Lemma answer_correct
      (s : subst)
      (n : nat)
      (f : repr_fun)
      (DSS : [ s , f ])
      (st' : nt_state)
      (cs : cut_signal)
      (st : state)
      (EV : eval_step st' (Answer s n) cs st) :
      in_denotational_sem_nt_state st' f.
Proof.
  remember (Answer s n) as l.
  induction EV; good_inversion Heql; auto.
  { assert (DSS_copy := DSS). apply (denotational_sem_uni _ _ _ _ MGU _) in DSS.
    destruct DSS as [DSS EQ]. constructor; auto. }
Qed.

Lemma next_state_correct
      (f : repr_fun)
      (st : state)
      (DSS : in_denotational_sem_state st f)
      (st' : nt_state)
      (WF : well_formed_nt_state st')
      (h : label)
      (cs : cut_signal)
      (EV : eval_step st' h cs st) :
      in_denotational_sem_nt_state st' f.
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
  { good_inversion WF. good_inversion DSST'; auto. }
  { good_inversion WF. good_inversion DSST'; auto. }
  { good_inversion DSST'. constructor; auto.
    eapply answer_correct; eauto. }
  { good_inversion WF. good_inversion DSST'. auto. }
  { good_inversion WF. good_inversion DSST'.
    { good_inversion DSST'0.
      constructor; auto.
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
  red in HDA. destruct HDA as [s [n [HInStr DSS]]].
  remember (Answer s n) as l. induction HInStr.
  { intros. inversion HOP; clear HOP; subst.
    constructor. eapply answer_correct; eauto. }
  { specialize (IHHInStr Heql). intros.
    inversion HOP; clear HOP; subst.
    inversion WF; clear WF; subst.
    specialize (well_formedness_preservation _ _ _ _ EV wfState).
    intro wf_st0.
    specialize (IHHInStr st0 OP wf_st0).
    constructor. eapply next_state_correct; eauto. }
Qed.

Lemma search_correctness
      (g   : goal)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g)
      (f   : repr_fun)
      (t   : trace)
      (HOP : op_sem (NTState (Leaf g empty_subst k)) t)
      (HDA : {| t , f |}) :
      [| g , f |].
Proof.
  remember (NTState (Leaf g empty_subst k)) as st.
  assert (in_denotational_sem_state st f).
  { eapply search_correctness_generalized; eauto.
    subst. constructor. apply well_formed_initial_state; auto. }
  subst. inversion H. inversion DSST'. auto.
Qed.
