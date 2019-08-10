Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Stream.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Omega.

Definition gt_fun : Set := name -> ground_term.

Definition gt_eq (gt1 : ground_term) (gt2 : ground_term) : Prop :=
  proj1_sig gt1 = proj1_sig gt2.

Definition gt_fun_eq (f1 : gt_fun) (f2 : gt_fun) : Prop :=
  forall x, gt_eq (f1 x) (f2 x).

Fixpoint apply_gt_fun (f : gt_fun) (t : term) : ground_term.
refine (
  match t with
  | Var x => f x
  | Cst n => exist _ (Cst n) eq_refl
  | Con n l r => match apply_gt_fun f l, apply_gt_fun f r with
                 | exist _ lt lg, exist _ rt rg => exist _ (Con n lt rt) _
                 end
  end
).
simpl. rewrite lg. rewrite rg. reflexivity.
Defined.

Lemma gt_fun_eq_apply (f1 f2 : gt_fun) (t : term) (feq : gt_fun_eq f1 f2) :
  gt_eq (apply_gt_fun f1 t) (apply_gt_fun f2 t).
Proof.
  induction t.
  { simpl. auto. }
  { reflexivity. }
  { red. simpl.
    destruct (apply_gt_fun f1 t1). destruct (apply_gt_fun f1 t2).
    destruct (apply_gt_fun f2 t1). destruct (apply_gt_fun f2 t2).
    simpl.
    red in IHt1. simpl in IHt1.
    red in IHt2. simpl in IHt2.
    subst. auto. }
Qed.

Lemma apply_gt_fun_fv
      (f1 f2 : gt_fun)
      (t : term)
      (f_fv_eq : forall x, (In x (fv_term t)) -> gt_eq (f1 x) (f2 x)) :
      gt_eq (apply_gt_fun f1 t) (apply_gt_fun f2 t).
Proof.
  induction t.
  { simpl. apply f_fv_eq. simpl. auto. }
  { unfold gt_eq. auto. }
  { unfold gt_eq. simpl.
    remember (apply_gt_fun f1 t1) as p11. destruct p11.
    remember (apply_gt_fun f1 t2) as p12. destruct p12.
    remember (apply_gt_fun f2 t1) as p21. destruct p21.
    remember (apply_gt_fun f2 t2) as p22. destruct p22.
    simpl.
    assert (x = x1).
    { apply IHt1. intros. apply f_fv_eq. unfold fv_term.
      apply (set_union_intro name_eq_dec). left. auto. }
    assert (x0 = x2).
    { apply IHt2. intros. apply f_fv_eq. unfold fv_term.
      apply (set_union_intro name_eq_dec). right. auto. }
    subst. auto. }
Qed.

Lemma gt_fun_eq_trans
      (f1 f2 f3 : gt_fun)
      (eq12 : gt_fun_eq f1 f2)
      (eq23 : gt_fun_eq f2 f3) :
      gt_fun_eq f1 f3.
Proof.
  revert eq12 eq23. unfold gt_fun_eq. unfold gt_eq. intros.
  rewrite eq12. auto.
Qed.

Lemma subst_of_gt
      (t : term)
      (s : subst)
      (f : gt_fun)
      (H : forall x : name, In x (fv_term t) -> image s x = Some (proj1_sig (f x))) :
      apply_subst s t = proj1_sig (apply_gt_fun f t).
Proof.
  induction t.
  { simpl. replace (image s n) with (Some (proj1_sig (f n))).
    { auto. }
    { symmetry. apply H. constructor. auto. } }
  { auto. }
  { simpl.
    destruct (apply_gt_fun f t1).
    destruct (apply_gt_fun f t2).
    simpl.
    replace x with (apply_subst s t1).
    { replace x0 with (apply_subst s t2).
      { auto. }
      { apply IHt2. intros. apply H.
        apply set_union_intro2. auto. } }
    { apply IHt1. intros. apply H.
      apply set_union_intro1. auto. } }
Qed.

Definition subst_gt_fun_compose (s : subst) (f : gt_fun) : gt_fun :=
  fun x => apply_gt_fun f (apply_subst s (Var x)).

Lemma gt_fun_apply_compose (s : subst) (f : gt_fun) (t : term) :
  gt_eq (apply_gt_fun (subst_gt_fun_compose s f) t) (apply_gt_fun f (apply_subst s t)).
Proof.
  induction t.
  { reflexivity. }
  { reflexivity. }
  { red. simpl.
    destruct (apply_gt_fun (subst_gt_fun_compose s f) t1).
    destruct (apply_gt_fun (subst_gt_fun_compose s f) t2).
    destruct (apply_gt_fun f (apply_subst s t1)).
    destruct (apply_gt_fun f (apply_subst s t2)).
    simpl.
    red in IHt1. simpl in IHt1.
    red in IHt2. simpl in IHt2.
    subst. auto. }
Qed.

Lemma gt_fun_eq_compose
      (f1 f2 : gt_fun)
      (eq : gt_fun_eq f1 f2)
      (s : subst) :
      gt_fun_eq (subst_gt_fun_compose s f1) (subst_gt_fun_compose s f2).
Proof.
  unfold gt_fun_eq. unfold gt_fun_eq in eq. unfold subst_gt_fun_compose.
  intro. induction (apply_subst s (Var x)).
  { simpl. auto. }
  { reflexivity. }
  { unfold gt_eq. simpl.
    remember (apply_gt_fun f1 t1) as p11. destruct p11.
    remember (apply_gt_fun f1 t2) as p12. destruct p12.
    remember (apply_gt_fun f2 t1) as p21. destruct p21.
    remember (apply_gt_fun f2 t2) as p22. destruct p22.
    simpl.
    unfold gt_eq in IHt1. simpl in IHt1. rewrite IHt1.
    unfold gt_eq in IHt2. simpl in IHt2. rewrite IHt2.
    auto. }
Qed.

Lemma gt_fun_compose_eq
      (f : gt_fun)
      (s1 s2 : subst)
      (eq : forall t, apply_subst s1 t = apply_subst s2 t) :
      gt_fun_eq (subst_gt_fun_compose s1 f) (subst_gt_fun_compose s2 f).
Proof.
  unfold gt_fun_eq. unfold subst_gt_fun_compose. unfold gt_eq.
  intro. rewrite eq. auto.
Qed.

Lemma subst_gt_fun_compose_assoc_subst
      (f : gt_fun)
      (s s' : subst) :
      gt_fun_eq (subst_gt_fun_compose (compose s s') f)
                (subst_gt_fun_compose s (subst_gt_fun_compose s' f)).
Proof.
  unfold gt_fun_eq. intros. unfold gt_eq.
  replace (subst_gt_fun_compose (compose s s') f x) with
          (apply_gt_fun (subst_gt_fun_compose (compose s s') f) (Var x)); auto.
  rewrite gt_fun_apply_compose. rewrite compose_correctness.
  replace (subst_gt_fun_compose s (subst_gt_fun_compose s' f) x) with
          (apply_gt_fun (subst_gt_fun_compose s (subst_gt_fun_compose s' f)) (Var x)); auto.
  rewrite gt_fun_apply_compose. rewrite gt_fun_apply_compose. auto.
Qed.

Inductive in_denotational_sem_goal : goal -> gt_fun -> Prop :=
| dsgUnify  : forall f t1 t2 (UnH : gt_eq (apply_gt_fun f t1) (apply_gt_fun f t2)),
                             in_denotational_sem_goal (Unify t1 t2) f
| dsgDisjL  : forall f g1 g2 (Hg : in_denotational_sem_goal g1 f),
                             in_denotational_sem_goal (Disj g1 g2) f
| dsgDisjR  : forall f g1 g2 (Hg : in_denotational_sem_goal g2 f),
                             in_denotational_sem_goal (Disj g1 g2) f
| dsgConj   : forall f g1 g2 (Hg1 : in_denotational_sem_goal g1 f)
                             (Hg2 : in_denotational_sem_goal g2 f),
                             in_denotational_sem_goal (Conj g1 g2) f
| dsgFresh  : forall f fn a fg (fvH : ~ is_fv_of_goal a (Fresh fg))
                               (Hg : in_denotational_sem_goal (fg a) fn)
                               (Hease : forall (x : name) (neq : x <> a), gt_eq (fn x) (f x)),
                               in_denotational_sem_goal (Fresh fg) f
| dsgInvoke : forall r t f (Hbody : in_denotational_sem_goal (proj1_sig (MiniKanrenSyntax.P r) t) f),
                           in_denotational_sem_goal (Invoke r t) f.

Hint Constructors in_denotational_sem_goal.

Inductive in_denotational_sem_lev_goal : nat -> goal -> gt_fun -> Prop :=
| dslgUnify  : forall l f t1 t2 (UnH : gt_eq (apply_gt_fun f t1) (apply_gt_fun f t2)),
                                in_denotational_sem_lev_goal (S l) (Unify t1 t2) f
| dslgDisjL  : forall l f g1 g2 (Hg :in_denotational_sem_lev_goal l g1 f),
                                in_denotational_sem_lev_goal l (Disj g1 g2) f
| dslgDisjR  : forall l f g1 g2 (Hg :in_denotational_sem_lev_goal l g2 f),
                                in_denotational_sem_lev_goal l (Disj g1 g2) f
| dslgConj   : forall l f g1 g2 (Hg1 :in_denotational_sem_lev_goal l g1 f)
                                (Hg2 :in_denotational_sem_lev_goal l g2 f),
                                in_denotational_sem_lev_goal l (Conj g1 g2) f
| dslgFresh  : forall l f fn a fg (fvH : ~ is_fv_of_goal a (Fresh fg))
                                  (Hg :in_denotational_sem_lev_goal l (fg a) fn)
                                  (Hease : forall (x : name) (neq : x <> a), gt_eq (fn x) (f x)),
                                  in_denotational_sem_lev_goal l (Fresh fg) f
| dslgInvoke : forall l r t f (Hbody :in_denotational_sem_lev_goal l (proj1_sig (MiniKanrenSyntax.P r) t) f),
                              in_denotational_sem_lev_goal (S l) (Invoke r t) f.

Hint Constructors in_denotational_sem_lev_goal.

Lemma in_denotational_sem_zero_lev (g : goal)
                                   (f : gt_fun) :
                                   ~ in_denotational_sem_lev_goal 0 g f.
Proof.
  intro. remember 0 as l. induction H; inversion Heql; auto.
Qed.

Lemma in_denotational_sem_lev_monotone (l : nat)
                                       (g : goal)
                                       (f : gt_fun)
                                       (Hdsg : in_denotational_sem_lev_goal l g f)
                                       (l' : nat)
                                       (Hle: l <= l')
                                       : in_denotational_sem_lev_goal l' g f.
Proof.
  revert Hle. revert l'. induction Hdsg; eauto.
  { intros. destruct l'; auto. inversion Hle. }
  { intros. destruct l'.
    { inversion Hle. }
    { apply le_S_n in Hle. auto. } }
Qed.

Lemma in_denotational_sem_some_lev (g : goal)
                                   (f : gt_fun)
                                   (Hdsg : in_denotational_sem_goal g f) :
                                   exists l, in_denotational_sem_lev_goal l g f.
Proof.
  induction Hdsg.
  { exists 1. auto. }
  { destruct IHHdsg. eauto. }
  { destruct IHHdsg. eauto. }
  { destruct IHHdsg1. destruct IHHdsg2.
    exists (max x x0). constructor.
    { eapply in_denotational_sem_lev_monotone; eauto. apply PeanoNat.Nat.le_max_l. }
    { eapply in_denotational_sem_lev_monotone; eauto. apply PeanoNat.Nat.le_max_r. } }
  { destruct IHHdsg. eauto. }
  { destruct IHHdsg. eauto. }
Qed.

Lemma den_sem_fv_only
      (f f' : gt_fun)
      (g : goal)
      (l : nat)
      (ff'_eq : forall x, is_fv_of_goal x g -> gt_eq (f x) (f' x))
      (Hgoal : in_denotational_sem_lev_goal l g f) :
      in_denotational_sem_lev_goal l g f'.
Proof.
  revert ff'_eq. revert f'. induction Hgoal; intros.
  { constructor. assert (gt_eq (apply_gt_fun f t1) (apply_gt_fun f' t1)).
    { apply apply_gt_fun_fv. auto. }
    assert (gt_eq (apply_gt_fun f t2) (apply_gt_fun f' t2)).
    { apply apply_gt_fun_fv. auto. }
    revert UnH H H0. unfold gt_eq. intros. congruence. }
  { constructor. apply IHHgoal. intros.
    apply ff'_eq. auto. }
  { apply dslgDisjR. apply IHHgoal. intros.
    apply ff'_eq. auto. }
  { constructor.
    { apply IHHgoal1; intros; apply ff'_eq; auto. }
    { apply IHHgoal2; intros; apply ff'_eq; auto. } }
  { remember (fun x => if name_eq_dec x a
                         then fn a
                         else f' x) as fn'.
    apply dslgFresh with fn' a; auto.
    { apply IHHgoal. intros. rewrite Heqfn'.
      destruct (name_eq_dec x a).
      { unfold gt_eq. subst. auto. }
      { specialize (Hease _ n). red. rewrite Hease.
        apply ff'_eq. eauto. } }
    { rewrite Heqfn'. intros.
      destruct (name_eq_dec x a); try contradiction.
      reflexivity. } }
  { constructor. apply IHHgoal. intros.
    apply ff'_eq. constructor.
    remember (MiniKanrenSyntax.P r). destruct d as [rel [Hcl Hco]].
    simpl in H. red in Hcl. red in Hcl. auto. }
Qed.


Lemma den_sem_rename_var
      (g1 g2 : goal)
      (cg_g : consistent_goal g1)
      (n : nat)
      (g1Bound : forall x : name, is_fv_of_goal x g1 -> x < n)
      (g2Bound : forall x : name, is_fv_of_goal x g2 -> x < n)
      (a1 a2 : name)
      (a12_neq : a1 <> a2)
      (a2_fresh : ~ is_fv_of_goal a2 g1)
      (sar : semiadequate_renaming a1 a2 g1 g2)
      (fa1 fa2 : gt_fun)
      (l : nat)
      (Hgoal_f1 : in_denotational_sem_lev_goal l g1 fa1)
      (f_switch : gt_eq (fa1 a1) (fa2 a2))
      (f12_eq : forall x, x <> a1 -> x <> a2 -> gt_eq (fa1 x) (fa2 x)) :
      in_denotational_sem_lev_goal l g2 fa2.
Proof.
  revert cg_g g1Bound g2Bound a12_neq a2_fresh sar Hgoal_f1 f_switch f12_eq.
  revert g1 g2 n a1 a2 fa1 fa2.
  induction l.
  { intros. apply in_denotational_sem_zero_lev in Hgoal_f1. contradiction. }
  { induction g1; intros; good_inversion Hgoal_f1; good_inversion sar; good_inversion cg_g.
    { constructor.
      etransitivity.
      2: etransitivity.
      2: apply UnH.
      1-2: etransitivity.
      1, 3: symmetry.
      1, 4: apply gt_fun_apply_compose.
      all: apply apply_gt_fun_fv; intros; unfold subst_gt_fun_compose;
        simpl; destruct (Nat.eq_dec a1 x); subst; symmetry; auto;
        apply f12_eq; auto; intro; subst; auto. }
    { apply dslgDisjL; eauto. eapply IHg1_1; eauto. }
    { apply dslgDisjR; eauto. eapply IHg1_2; eauto. }
    { constructor; eauto.
      { eapply IHg1_1; eauto. }
      { eapply IHg1_2; eauto. } }
    { apply den_sem_fv_only with fa1.
      { intros; apply f12_eq; intro; subst; auto. }
      { econstructor.
        2: eauto.
        all: eauto. } }
    { rename g into fg. rename fn into fn1. rename a into a0. red in HBinding.
      assert (very_fresh_var : exists y, a0 <> y /\ a2 <> y /\
                                         (~ is_fv_of_goal y (Fresh fg)) /\
                                         (~ is_fv_of_goal y (Fresh rfg))).
      { destruct (name_eq_dec a0 n); destruct (name_eq_dec a0 (S n));
        destruct (name_eq_dec a2 n); destruct (name_eq_dec a2 (S n)); subst; try omega.
        5, 6, 8, 9: exists n.
        1, 3, 9: exists (S n).
        4, 5: exists (S (S n)).
        all: repeat split; try omega.
        all: intro CH; try apply g1Bound in CH; try apply g2Bound in CH; omega. }
      destruct very_fresh_var as [a3 [a03_neq [a23_neq [a3_fresh a3_rfresh]]]].
      assert (a13_neq : a1 <> a3).
      { intro; subst; auto. }
      remember (fun x => if name_eq_dec x a3
                           then fn1 a0
                           else if name_eq_dec x a0
                                  then fa2 a0
                                  else fn1 x) as fn0 eqn:fn0_def.
      assert (AH0 : in_denotational_sem_lev_goal (S l) (fg a3) fn0).
      { subst.
        apply H with a0 (max n (max (S a0) (S a3))) a0 a3 fn1; eauto.
        { intros. destruct (name_eq_dec x a0); subst.
          { zify. omega. }
          { assert (x < n); eauto. zify. omega. } }
        { intros. destruct (name_eq_dec x a3); subst.
          { zify. omega. }
          { assert (x < n); eauto. zify. omega. } }
        { destruct (name_eq_dec a3 a3); subst.
          { reflexivity. }
          { contradiction. } }
        { intros. destruct (name_eq_dec x a3).
          { contradiction. }
          { destruct (name_eq_dec x a0).
            { contradiction. }
            { reflexivity. } } } }
      remember (fun x => if name_eq_dec x a2
                           then fn0 a1
                           else if name_eq_dec x a1
                                  then fa2 a1
                                  else fn0 x) as fn2 eqn:fn2_def.
      assert (AH2 : in_denotational_sem_lev_goal (S l) (rfg a3) fn2).
      { apply H with a3 (max n (max (S a0) (S a3))) a1 a2 fn0; subst; eauto.
        { intros. destruct (name_eq_dec x a3); subst.
          { zify. omega. }
          { assert (x < n); eauto. zify. omega. } }
        { intros. destruct (name_eq_dec x a3); subst.
          { zify. omega. }
          { assert (x < n); eauto. zify. omega. } }
        { simpl. destruct (name_eq_dec a2 a2); subst.
          { reflexivity. }
          { contradiction. } }
        { intros. simpl. destruct (name_eq_dec x a2).
          { contradiction. }
          { destruct (name_eq_dec x a1).
            { contradiction. }
            { reflexivity. } } } }
      econstructor; eauto.
      intros. subst. destruct (name_eq_dec x a2); subst.
      { destruct (name_eq_dec a1 a0); subst.
        { contradiction. }
        { destruct (name_eq_dec a1 a3); subst.
          { contradiction. }
          { etransitivity.
            { apply Hease. auto. }
            { auto. } } } }
      { destruct (name_eq_dec x a1); subst.
        { reflexivity. }
        { destruct (name_eq_dec x a3).
          { contradiction. }
          { destruct (name_eq_dec x a0); subst.
            { reflexivity. }
            { etransitivity.
              { apply Hease. auto. }
              { apply f12_eq; auto. } } } } } }
    { rename n into r. rename n0 into n.
      remember (MiniKanrenSyntax.P r) as d. destruct d as [rel [Hcl Hco]].
      red in Hco. destruct (Hco t) as [Hcog Hcof].
      red in Hcl. unfold closed_goal_in_context in Hcl.
      econstructor.
      rewrite <- Heqd. simpl.
      eapply IHl.
      7: eauto.
      all: simpl; eauto. } }
Qed.

Lemma den_sem_another_fresh_var
      (b : name -> goal)
      (cg : consistent_goal (Fresh b))
      (n : nat)
      (freshBound : forall x : name, is_fv_of_goal x (Fresh b) -> x < n)
      (a1 a2 : name)
      (a1_fresh : ~ is_fv_of_goal a1 (Fresh b))
      (a2_fresh : ~ is_fv_of_goal a2 (Fresh b))
      (fa1 fa2 : gt_fun)
      (l : nat)
      (Hgoal_f1 : in_denotational_sem_lev_goal l (b a1) fa1)
      (f_switch : gt_eq (fa1 a1) (fa2 a2))
      (f12_eq : forall x, x <> a1 -> x <> a2 -> gt_eq (fa1 x) (fa2 x)) :
      in_denotational_sem_lev_goal l (b a2) fa2.
Proof.
  destruct (name_eq_dec a1 a2); subst.
  { apply den_sem_fv_only with fa1; auto.
    intros. destruct (name_eq_dec x a2); subst; auto. }
  { good_inversion cg. red in HBinding.
    eapply den_sem_rename_var with (g1 := (b a1)) (n := max n (max (S a1) (S a2))); eauto.
    { intros. destruct (name_eq_dec x a1); subst.
      { zify. omega. }
      { assert (x < n); eauto. zify. omega. } }
    { intros. destruct (name_eq_dec x a2); subst.
      { zify. omega. }
      { assert (x < n); eauto. zify. omega. } } }
Qed.