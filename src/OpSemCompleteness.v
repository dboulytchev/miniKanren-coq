Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Omega.

Require Import Stream.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import OperationalSem.
Require Import DenotationalSem.


Module OperationalSemCompletenessAbstr (CS : ConstraintStoreSig).

Import CS.

Module OperationalSemCS := OperationalSemAbstr CS.

Import OperationalSemCS.

Lemma search_completeness_generalized
      (l    : nat)
      (g    : goal)
      (CG   : consistent_goal g)
      (s    : subst)
      (cs   : constraint_store s)
      (n    : nat)
      (WF   : well_formed_state' (Leaf g s cs n))
      (t    : trace)
      (OP   : op_sem (State (Leaf g s cs n)) t)
      (f    : repr_fun)
      (DSG  : [| l | g , f |])
      (DSS  : [ s , f ])
      (DSCS : [| s , cs , f |]) :
      exists (f' : repr_fun), {| t , f' |} /\
                            forall (x : name), x < n -> gt_eq (f x) (f' x).
Proof.
  revert OP. revert t. revert CG DSG DSS DSCS WF. revert cs. revert g f s n. induction l.
  { intros. apply in_denotational_sem_zero_lev in DSG. contradiction. }
  { induction g; intros; good_inversion CG.
    { good_inversion DSG. }
    { exists f. split.
      { econstructor. eexists. eexists. split; eauto.
        good_inversion OP. good_inversion EV. simpl_existT_cs_same. constructor. }
      { intros; red; auto. } }
    { exists f. split.
      2: intros; red; auto.
      good_inversion OP. good_inversion EV; good_inversion DSG; simpl_existT_cs_same.
      { destruct DSS as [fs COMP_s_fs]. red in UNI.
        rewrite <- (repr_fun_eq_apply _ _ t COMP_s_fs) in UNI.
        rewrite <- (repr_fun_eq_apply _ _ t0 COMP_s_fs) in UNI.
        rewrite (repr_fun_apply_compose s fs t) in UNI.
        rewrite (repr_fun_apply_compose s fs t0) in UNI.
        apply unfier_from_gt_unifier in UNI.
        destruct UNI as [sc [SC_UNIFIES _]]. specialize (mgu_non_unifiable _ _ MGU sc).
        contradiction. }
      { specialize (upd_cs_fail_condition _ _ _ UPD_CS f).
        intros C. exfalso. apply C. split; auto.
        apply (denotational_sem_uni _ _ _ _ MGU); auto. }
      { red. exists (compose s d). exists cs'. exists n. split.
        { constructor. }
        { apply and_comm. specialize (upd_cs_success_condition _ _ _ _ UPD_CS f).
          intro EQUI. apply EQUI. split; auto. apply (denotational_sem_uni _ _ _ _ MGU); auto. } } }
    { exists f. split.
      2: intros; red; auto.
      good_inversion DSG. good_inversion OP.
      good_inversion EV; simpl_existT_cs_same.
      { exfalso. eapply add_constraint_fail_condition in ADD_C. eauto. }
      { red. exists s. exists cs'. exists n. split.
        { constructor. }
        { apply and_comm. eapply add_constraint_success_condition in ADD_C.
          apply ADD_C. auto. } } }
    { good_inversion OP. inversion EV; subst.
      apply well_formedness_preservation in EV; auto. good_inversion EV. simpl_existT_cs_same.
      good_inversion wfState.
      specialize (op_sem_exists (State (Leaf g1 s cs n))). intro p1. destruct p1 as [t1 OP1].
      specialize (op_sem_exists (State (Leaf g2 s cs n))). intro p2. destruct p2 as [t2 OP2].
      specialize (sum_op_sem _ _ _ _ _ OP1 OP2 OP0). intro Hinter.
      good_inversion DSG.
      { specialize (IHg1 f s n cs CG_G1 DSG0 DSS DSCS WF_L t1 OP1).
        destruct IHg1 as [f' [HinDA ff'_eq]]. exists f'. split; auto.
        red in HinDA. destruct HinDA as [sr [csr [nr [Hin [DSSr DSCSr]]]]].
        red. exists sr. exists csr. exists nr. split; auto. constructor.
        apply (interleave_in _ _ _ Hinter (Answer sr csr nr)). auto. }
      { specialize (IHg2 f s n cs CG_G2 DSG0 DSS DSCS WF_R t2 OP2).
        destruct IHg2 as [f' [HinDA ff'_eq]]. exists f'. split; auto.
        red in HinDA. destruct HinDA as [sr [csr [nr [Hin [DSSr DSCSr]]]]].
        red. exists sr. exists csr. exists nr. split; auto. constructor.
        apply (interleave_in _ _ _ Hinter (Answer sr csr nr)). auto. } }
    { good_inversion DSG. good_inversion OP. inversion EV; simpl_existT_cs_same; subst.
      specialize (op_sem_exists (State (Leaf g1 s cs n))). intro p1. destruct p1 as [t1 OP1].
      assert (wfst'1 : well_formed_state' (Leaf g1 s cs n)).
      { constructor; good_inversion WF; simpl_existT_cs_same; auto. }
      specialize (IHg1 f s n cs CG_G1 DSG_L DSS DSCS wfst'1 t1 OP1).
      destruct IHg1 as [f' [HinDA ff'_eq]]. red in HinDA.
      destruct HinDA as [s' [cs' [n' [Hinstr' [HDAS' HDACS']]]]].
      specialize (op_sem_exists (State (Leaf g2 s' cs' n'))). intro p2. destruct p2 as [t2 OP2].
      specialize (counter_in_trace _ _ _ _ _ _ _ _ OP1 Hinstr'). intro n_le_n'.
      assert (wfst'2 : well_formed_state' (Leaf g2 s' cs' n')).
      { good_inversion WF. simpl_existT_cs_same.
        destruct (well_formed_subst_in_trace _ (wfNonEmpty _ wfst'1)  _ OP1 _ _ _ Hinstr').
        specialize (well_formed_ds_in_trace _ (wfNonEmpty _ wfst'1)  _ OP1 _ _ _ Hinstr').
        intros. constructor; auto. intros.
        apply lt_le_trans with n; auto. }
      assert (Hg2' : in_denotational_sem_lev_goal (S l) g2 f').
      { apply completeness_condition_lev with f; auto. intros. apply ff'_eq.
        good_inversion WF. auto. }
      specialize (IHg2 f' s' n' cs' CG_G2 Hg2' HDAS' HDACS' wfst'2 t2 OP2).
      destruct IHg2 as [f'' [HinDA f'f''_eq]]. red in HinDA.
      destruct HinDA as [s'' [cs'' [n'' [Hinstr'' [HDAS'' HDACS'']]]]].
      exists f''. split.
      { red. exists s''. exists cs''. exists n''. split; auto.
        constructor. eapply prod_op_sem_in; eauto. }
      { intros. red. apply eq_trans with (proj1_sig (f' x)).
        { apply ff'_eq. auto. }
        { apply f'f''_eq. omega. } } }
    { good_inversion DSG. good_inversion OP. inversion EV; simpl_existT_cs_same; subst.
      apply well_formedness_preservation in EV; auto. good_inversion EV.
      rename fn into fa.
      remember (fun x => if name_eq_dec x n
                         then fa a
                         else f x) as fn.
      assert (Hgn : [| S l | g n , fn |]).
      { good_inversion WF. apply den_sem_another_fresh_var with n a fa; auto.
        { intro C. apply FV_LT_COUNTER in C. omega. }
        {  destruct (name_eq_dec n n); try contradiction. reflexivity. }
        { intros. destruct (name_eq_dec x n); try contradiction. auto. } }
      assert (DSSn_AND_DSCSn : [ s , fn ] /\ [| s , cs , fn |]).
      { good_inversion WF. simpl_existT_cs_same. apply (DS_LT_COUNTER f); auto.
        intros. destruct (name_eq_dec x n); try omega. reflexivity. }
      destruct DSSn_AND_DSCSn as [DSSn DSCSn].
      specialize (H n fn s (S n) cs (CG_BODY n) Hgn DSSn DSCSn wfState t0 OP0).
      destruct H as [f' [HinDA ff'_eq]]. exists f'. split.
      { red. red in HinDA. destruct HinDA as [s' [cs' [n' [Hinstr [HDAS HDACS]]]]].
        exists s'. exists cs'. exists n'. split; auto. constructor; auto. }
      { intros. assert (x < S n). { omega. }
        specialize (ff'_eq x H0). red in ff'_eq. red. rewrite <- ff'_eq.
        rewrite Heqfn. destruct (name_eq_dec x n); try omega. reflexivity. } }
    { good_inversion DSG. good_inversion OP. inversion EV; subst.
      apply well_formedness_preservation in EV; auto. good_inversion EV. simpl_existT_cs_same.
      assert (cg_body : consistent_goal (proj1_sig (MiniKanrenSyntax.Prog n) t)).
      { remember (MiniKanrenSyntax.Prog n) as d. destruct d as [rel [Hcl Hco]].
        red in Hco. destruct (Hco t) as [Hcog Hcof]. auto. }
      specialize (IHl (proj1_sig (MiniKanrenSyntax.Prog n) t) f s n0 cs cg_body DSG0 DSS DSCS wfState t1 OP0).
      destruct IHl as [f' [HinDA ff'_eq]]. exists f'. split; auto.
      red. red in HinDA. destruct HinDA as [s' [cs' [n' [Hinstr [HDAS HDACS]]]]].
      exists s'. exists cs'. exists n'. split; auto. constructor; auto. } }
Qed.

Lemma search_completeness
      (g   : goal)
      (CG  : consistent_goal g)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g)
      (f   : repr_fun)
      (t   : trace)
      (OP : op_sem (State (Leaf g empty_subst init_cs k)) t)
      (HDS : [| g , f |]) :
      exists (f' : repr_fun), {| t , f' |} /\
                            forall (x : name), In x (first_nats k) -> gt_eq (f x) (f' x).
Proof.
  apply in_denotational_sem_some_lev in HDS. destruct HDS as [l HDS].
  assert (WF : well_formed_state' (Leaf g empty_subst init_cs k)).
  { apply well_formed_initial_state; auto. }
  specialize (search_completeness_generalized l g CG empty_subst init_cs k WF t OP f HDS (empty_subst_ds f) (init_condition f)).
  intro. destruct H as [f' [HinDA ff'eq]]. exists f'. split; auto.
  intros. apply ff'eq. apply first_nats_less; auto.
Qed.

End OperationalSemCompletenessAbstr.
