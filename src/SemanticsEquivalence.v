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

Lemma set_empty_union
      (s1 s2 : var_set)
      (eq : var_set_union s1 s2 = var_set_empty) :
      s1 = var_set_empty /\ s2 = var_set_empty.
Proof.
  split.
  { destruct s1; auto.
    assert (In n var_set_empty).
    { rewrite <- eq. apply set_union_intro. left. constructor. auto. }
    inversion H. }
  { destruct s2; auto.
    assert (In n var_set_empty).
    { rewrite <- eq. apply set_union_intro. right. constructor. auto. }
    inversion H. }
Qed.

Lemma unfier_from_gt_unifier
      (t1 t2 : term)
      (f : gt_fun)
      (f_unifies : gt_eq (apply_gt_fun f t1) (apply_gt_fun f t2)) :
      exists s, unifier s t1 t2 /\ in_denotational_sem_subst s f.
Proof.
  remember (map (fun x => (x, proj1_sig (f x))) (var_set_union (fv_term t1) (fv_term t2))) as s.
  exists s. split.
  { red. red in f_unifies.
    assert (apply_subst s t1 = proj1_sig (apply_gt_fun f t1)).
    { clear f_unifies.
      assert (forall x, In x (fv_term t1) -> image s x = Some (proj1_sig (f x))).
      { intros. assert (In x (var_set_union (fv_term t1) (fv_term t2))).
        { apply set_union_intro1. auto. }
        remember (var_set_union (fv_term t1) (fv_term t2)).
        subst. apply map_image. auto. }
      apply subst_of_gt. auto. }
    assert (apply_subst s t2 = proj1_sig (apply_gt_fun f t2)).
    { clear f_unifies.
      assert (forall x, In x (fv_term t2) -> image s x = Some (proj1_sig (f x))).
      { intros. assert (In x (var_set_union (fv_term t1) (fv_term t2))).
        { apply set_union_intro2. auto. }
        remember (var_set_union (fv_term t1) (fv_term t2)).
        subst. apply map_image. auto. }
      apply subst_of_gt. auto. }
    congruence. }
  { red. exists f. red. intros x. unfold subst_gt_fun_compose.
    unfold apply_subst. destruct (image s x) eqn:eq.
    { destruct (f x) eqn:eqfx.
      assert (x0 = t).
      { unfold image in eq.
        remember (var_set_union (fv_term t1) (fv_term t2)). clear Heqv.
        revert Heqs. revert v.
        induction s.
        { inversion eq. }
        { intros. destruct a as [y t0]. destruct v; good_inversion Heqs.
          destruct (Nat.eq_dec n x).
          { good_inversion eq. rewrite eqfx. auto. }
          { apply IHs with v; auto. } } }
      subst. red. simpl. clear eqfx. clear eq. induction t.
      { inversion e. }
      { auto. }
      { simpl in e. apply set_empty_union in e. destruct e.
        apply IHt1 in H. apply IHt2 in H0. simpl.
        destruct (apply_gt_fun f t3). simpl in H.
        destruct (apply_gt_fun f t4). simpl in H0.
        simpl. subst. auto. } }
    { red. auto. } }
Qed.

Inductive in_denotational_sem_state' : state' -> gt_fun -> Prop :=
| dsst'Leaf : forall g s n f (Hgoal : in_denotational_sem_goal g f)
                             (Hsubst : in_denotational_sem_subst s f),
                             in_denotational_sem_state' (Leaf g s n) f
| dsst'SumL : forall st1' st2' f (Hst1' : in_denotational_sem_state' st1' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'SumR : forall st1' st2' f (Hst2' : in_denotational_sem_state' st2' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'Prod : forall st' g f (Hgoal : in_denotational_sem_goal g f)
                             (Hst' : in_denotational_sem_state' st' f),
                             in_denotational_sem_state' (Prod st' g) f.

Hint Constructors in_denotational_sem_state'.

Inductive in_denotational_sem_state : state -> gt_fun -> Prop :=
| dsstState : forall st' f (Hst' : in_denotational_sem_state' st' f),
                           in_denotational_sem_state (State st') f.

Hint Constructors in_denotational_sem_state.

Definition in_denotational_analog (t : trace) (f : gt_fun) : Prop :=
  exists (s : subst) (n : nat), in_stream (Answer s n) t /\ in_denotational_sem_subst s f.

Lemma answer_correct
      (s : subst)
      (n : nat)
      (f : gt_fun)
      (HInDS : in_denotational_sem_subst s f)
      (st' : state')
      (st : state)
      (EV : eval_step st' (Answer s n) st) :
      in_denotational_sem_state' st' f.
Proof.
  remember (Answer s n) as l.
  induction EV; good_inversion Heql.
  2, 3: auto.
  destruct HInDS as [f' ff'_con].
  constructor.
  { constructor. red.
    specialize (gt_fun_eq_apply _ _ t1 ff'_con). intro. rewrite <- H.
    specialize (gt_fun_eq_apply _ _ t2 ff'_con). intro. rewrite <- H0.
    rewrite gt_fun_apply_compose. rewrite gt_fun_apply_compose.
    rewrite compose_correctness. rewrite compose_correctness.
    apply unify_unifies in u. rewrite u. reflexivity. }
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
      (HInDS : in_denotational_sem_state st f)
      (st' : state')
      (wfState : well_formed_state' st')
      (h : label)
      (EV : eval_step st' h st) :
      in_denotational_sem_state' st' f.
Proof.
  induction EV; good_inversion HInDS.
  { good_inversion Hst'.
    { good_inversion Hst1'; constructor; auto. }
    { good_inversion Hst2'; constructor; auto. } }
  { good_inversion Hst'. good_inversion Hst'0. auto. }
  { good_inversion wfState. good_inversion Hst'.
    constructor; auto. econstructor; eauto.
    intros HIn. apply FVLTCounter in HIn.
    { omega. }
    { reflexivity. } }
  { good_inversion Hst'. auto. }
  { auto. }
  { good_inversion wfState. good_inversion Hst'; auto. }
  { good_inversion Hst'. constructor; auto.
    eapply answer_correct; eauto. }
  { good_inversion wfState. good_inversion Hst'. auto. }
  { good_inversion wfState. good_inversion Hst'.
    { good_inversion Hst1'. constructor; auto.
      eapply answer_correct; eauto. }
    { good_inversion Hst2'. auto. } }
Qed.

Lemma search_correctness_generalized
      (st   : state)
      (wfSt : well_formed_state st)
      (f    : gt_fun)
      (t    : trace)
      (HOP  : op_sem st t)
      (HDA  : in_denotational_analog t f) :
      in_denotational_sem_state st f.
Proof.
  revert HOP wfSt. revert st.
  red in HDA. destruct HDA as [s [n [HInStr HInDS]]].
  remember (Answer s n) as l. induction HInStr.
  { intros. inversion HOP; clear HOP; subst.
    constructor. eapply answer_correct; eauto. }
  { specialize (IHHInStr Heql). intros.
    inversion HOP; clear HOP; subst.
    inversion wfSt; clear wfSt; subst.
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

Lemma first_nats_less (n k : nat) (H : In n (first_nats k)) : n < k.
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
    { intros. good_inversion H. good_inversion H0. }
    { intros. good_inversion H. destruct H0 as [t1 [H1 _]]. good_inversion H1. }
    { intros. apply HC in H. apply first_nats_less. auto. } }
  subst. inversion H. inversion Hst'. auto.
Qed.

Lemma search_completeness_generalized
      (l     : nat)
      (g     : goal)
      (Hcg    : consistent_goal g)
      (s     : subst)
      (n     : nat)
      (wfSt' : well_formed_state' (Leaf g s n))
      (t     : trace)
      (HOP   : op_sem (State (Leaf g s n)) t)
      (f     : gt_fun)
      (Hgoal : in_denotational_sem_lev_goal l g f)
      (Hsubst : in_denotational_sem_subst s f) :
      exists (f' : gt_fun), (in_denotational_analog t f') /\
                            forall (x : name), x < n -> gt_eq (f x) (f' x).
Proof.
  revert HOP. revert t. revert Hcg Hgoal Hsubst wfSt'. revert g f s n. induction l.
  { intros. apply in_denotational_sem_zero_lev in Hgoal. contradiction. }
  { induction g; intros; good_inversion Hcg.
    { good_inversion Hgoal. }
    { exists f. split.
      2: intros; red; auto.
      good_inversion Hgoal. red in Hsubst. destruct Hsubst as [fs s_fs_f].
      assert (gt_eq (apply_gt_fun fs (apply_subst s t)) (apply_gt_fun fs (apply_subst s t0))).
      { red. rewrite <- gt_fun_apply_compose. rewrite <- gt_fun_apply_compose.
        apply eq_trans with (proj1_sig (apply_gt_fun f t)).
        { apply gt_fun_eq_apply. auto. }
        { apply eq_trans with (proj1_sig (apply_gt_fun f t0)); auto.
          symmetry. apply gt_fun_eq_apply. auto. } }
      apply unfier_from_gt_unifier in H. destruct H as [u [u_uni u_fs]].
      good_inversion HOP. good_inversion EV.
      { specialize (unify_non_unifiable _ _ H5 u u_uni). contradiction. }
      { rename s' into m. red. exists (compose s m). exists n. split; try constructor.
        specialize (unify_most_general _ _ _ H5 u u_uni). intro Hmg.
        red in Hmg. destruct Hmg as [ds u_ds_m]. red in u_fs.
        destruct u_fs as [fss u_fss_fs]. red. exists (subst_gt_fun_compose ds fss).
        eapply gt_fun_eq_trans. 2: eauto.
        eapply gt_fun_eq_trans. eapply subst_gt_fun_compose_assoc_subst.
        eapply gt_fun_eq_trans. 2: eapply gt_fun_eq_compose; eauto.
        apply gt_fun_eq_compose.
        eapply gt_fun_eq_trans. red; symmetry; eapply subst_gt_fun_compose_assoc_subst.
        apply gt_fun_compose_eq. intros. rewrite u_ds_m. apply compose_correctness. } }
    { good_inversion HOP. inversion EV; subst.
      apply well_formedness_preservation in EV; auto. good_inversion EV.
      good_inversion wfState.
      specialize (op_sem_exists (State (Leaf g1 s n))). intro p1. destruct p1 as [t1 OP1].
      specialize (op_sem_exists (State (Leaf g2 s n))). intro p2. destruct p2 as [t2 OP2].
      specialize (sum_op_sem _ _ _ _ _ OP1 OP2 OP). intro Hinter.
      good_inversion Hgoal.
      { specialize (IHg1 f s n Hcg1 Hg Hsubst wfst'1 t1 OP1).
        destruct IHg1 as [f' [HinDA ff'_eq]]. exists f'. split; auto.
        red in HinDA. destruct HinDA as [sr [nr [Hin Hsubstr]]].
        red. exists sr. exists nr. split; auto. constructor.
        apply (interleave_in _ _ _ Hinter (Answer sr nr)). auto. }
      { specialize (IHg2 f s n Hcg2 Hg Hsubst wfst'2 t2 OP2).
        destruct IHg2 as [f' [HinDA ff'_eq]]. exists f'. split; auto.
        red in HinDA. destruct HinDA as [sr [nr [Hin Hsubstr]]].
        red. exists sr. exists nr. split; auto. constructor.
        apply (interleave_in _ _ _ Hinter (Answer sr nr)). auto. } }
    { good_inversion Hgoal. good_inversion HOP. inversion EV; subst.
      specialize (op_sem_exists (State (Leaf g1 s n))). intro p1. destruct p1 as [t1 OP1].
      assert (wfst'1 : well_formed_state' (Leaf g1 s n)).
      { constructor; good_inversion wfSt'; auto. }
      specialize (IHg1 f s n Hcg1 Hg1 Hsubst wfst'1 t1 OP1).
      destruct IHg1 as [f' [HinDA ff'_eq]]. red in HinDA.
      destruct HinDA as [s' [n' [Hinstr' HDAS']]].
      specialize (op_sem_exists (State (Leaf g2 s' n'))). intro p2. destruct p2 as [t2 OP2].
      specialize (counter_in_trace _ _ _ _ _ _ OP1 Hinstr'). intro n_le_n'.
      assert (wfst'2 : well_formed_state' (Leaf g2 s' n')).
      { good_inversion wfSt'.
        specialize (well_formed_subst_in_trace _ (wfNonEmpty _ wfst'1)  _ OP1 _ _ Hinstr').
        intros. destruct H.
        constructor; auto. intros.
        apply lt_le_trans with n; auto. }
      assert (Hg2' : in_denotational_sem_lev_goal (S l) g2 f').
      { apply den_sem_fv_only with f; auto. intros. apply ff'_eq.
        good_inversion wfSt'. auto. }
      specialize (IHg2 f' s' n' Hcg2 Hg2' HDAS' wfst'2 t2 OP2).
      destruct IHg2 as [f'' [HinDA f'f''_eq]]. red in HinDA.
      destruct HinDA as [s'' [n'' [Hinstr'' HDAS'']]].
      exists f''. split.
      { red. exists s''. exists n''. split; auto.
        constructor. eapply prod_op_sem_in; eauto. }
      { intros. red. apply eq_trans with (proj1_sig (f' x)).
        { apply ff'_eq. auto. }
        { apply f'f''_eq. omega. } } }
    { good_inversion Hgoal. good_inversion HOP. inversion EV; subst.
      apply well_formedness_preservation in EV; auto. good_inversion EV.
      rename fn into fa.
      red in Hsubst. destruct Hsubst as [fs fssf'_eq].
      remember (fun x => if name_eq_dec x n
                         then fa a
                         else fs x) as fs'.
      remember (fun x => if name_eq_dec x n
                         then fa a
                         else if name_eq_dec x a
                              then (subst_gt_fun_compose s fs') a
                              else fa x) as fn.
      assert (H_n_is_fresh : forall x, In n (fv_term (apply_subst s (Var x))) -> x = n).
      { intros. simpl in H0.
        destruct (image s x) eqn:eq.
        { assert (n < n).
          { good_inversion wfSt'. apply vranLTCounter.
            red. eauto. }
          omega. }
        { simpl in H0. destruct H0; try contradiction. auto. } }
      assert (Hgn : in_denotational_sem_lev_goal (S l) (g n) fn).
      { rewrite Heqfn. good_inversion wfSt'.
        apply den_sem_another_fresh_var with n a fa; auto.
        { intro C. apply FVLTCounter in C. omega. }
        { destruct (name_eq_dec n n); try contradiction. reflexivity. }
        { intros. destruct (name_eq_dec x n); try contradiction.
          destruct (name_eq_dec x a); try contradiction. reflexivity. } }
      assert (Hsubstn: in_denotational_sem_subst s fn).
      { red. exists fs'. red. intros. red. unfold subst_gt_fun_compose.
        rewrite Heqfs'. rewrite Heqfn. destruct (name_eq_dec x n).
        { assert (H_n_is_fresh_2 : apply_subst s (Var n) = Var n).
          { simpl. destruct (image s n) eqn:eq; auto.
            good_inversion wfSt'. assert (n < n).
            { apply domLTCounter. red. eauto. }
            omega. }
          rewrite e. rewrite H_n_is_fresh_2. simpl.
          destruct (name_eq_dec n n); try contradiction. auto. }
        { destruct (name_eq_dec x a).
          { rewrite e. rewrite Heqfs'. auto. }
          { specialize (Hease x n1). rewrite Hease.
            red in fssf'_eq. specialize (fssf'_eq x). red in fssf'_eq.
            rewrite <- fssf'_eq. unfold subst_gt_fun_compose.
            apply apply_gt_fun_fv. intros. destruct (name_eq_dec x0 n).
            { rewrite e in H0. apply H_n_is_fresh in H0. contradiction. }
            { reflexivity. } } } }
      specialize (H n fn s (S n) (HcgInner n) Hgn Hsubstn wfState t0 OP).
      destruct H as [f' [HinDA ff'_eq]]. exists f'. split.
      { red. red in HinDA. destruct HinDA as [s' [n' [Hinstr HDAS]]].
        exists s'. exists n'. split; auto. constructor; auto. }
      { intros. assert (x < S n). { omega. }
        specialize (ff'_eq x H0). red in ff'_eq. red. rewrite <- ff'_eq.
        rewrite Heqfn. destruct (name_eq_dec x n); try omega.
        destruct (name_eq_dec x a).
        { rewrite e.
          red in fssf'_eq. specialize (fssf'_eq a). red in fssf'_eq.
          rewrite <- fssf'_eq. unfold subst_gt_fun_compose.
          apply apply_gt_fun_fv. intros. rewrite Heqfs'.
          destruct (name_eq_dec x0 n).
          { auto. rewrite e0 in H1. apply H_n_is_fresh in H1. subst. contradiction. }
          { unfold gt_eq. auto. } }
        { specialize (Hease x n1). rewrite Hease. auto. } } }
    { good_inversion Hgoal. good_inversion HOP. inversion EV; subst.
      apply well_formedness_preservation in EV; auto. good_inversion EV.
      assert (cg_body : consistent_goal (proj1_sig (MiniKanrenSyntax.P n) t)).
      { remember (MiniKanrenSyntax.P n) as d. destruct d as [rel [Hcl Hco]].
        red in Hco. destruct (Hco t) as [Hcog Hcof]. auto. }
      specialize (IHl (proj1_sig (MiniKanrenSyntax.P n) t) f s n0 cg_body Hbody Hsubst wfState t1 OP).
      destruct IHl as [f' [HinDA ff'_eq]]. exists f'. split; auto.
      red. red in HinDA. destruct HinDA as [s' [n' [Hinstr HDAS]]].
      exists s'. exists n'. split; auto. constructor; auto. } }
Qed.


Lemma search_completeness
      (g   : goal)
      (Hcg    : consistent_goal g)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g)
      (f   : gt_fun)
      (t   : trace)
      (HOP : op_sem (State (Leaf g empty_subst k)) t)
      (HDS : in_denotational_sem_goal g f) :
      exists (f' : gt_fun), (in_denotational_analog t f') /\
                            forall (x : name), In x (first_nats k) -> gt_eq (f x) (f' x).
Proof.
  apply in_denotational_sem_some_lev in HDS. destruct HDS as [l HDS].
  assert (wfSt' : well_formed_state' (Leaf g empty_subst k)).
  { constructor.
    { intros. good_inversion H. good_inversion H0. }
    { intros. good_inversion H. destruct H0 as [t1 [H1 _]]. good_inversion H1. }
    { red in HC. intros. apply first_nats_less; auto. } }
  assert (Hsubst : in_denotational_sem_subst empty_subst f).
  { red. exists f. red. intros.
    unfold subst_gt_fun_compose. rewrite apply_empty. reflexivity. }
  specialize (search_completeness_generalized l g Hcg empty_subst k wfSt' t HOP f HDS Hsubst).
  intro. destruct H as [f' [HinDA ff'eq]]. exists f'. split; auto.
  intros. apply ff'eq. apply first_nats_less; auto.
Qed.
