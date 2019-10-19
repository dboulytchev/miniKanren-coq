
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

Lemma gt_fun_eq_apply
      (f1 f2 : gt_fun)
      (t : term)
      (FEQ : gt_fun_eq f1 f2) :
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
      (F12_FV_EQ : forall x, (In x (fv_term t)) -> gt_eq (f1 x) (f2 x)) :
      gt_eq (apply_gt_fun f1 t) (apply_gt_fun f2 t).
Proof.
  induction t.
  { simpl. apply F12_FV_EQ. simpl. auto. }
  { unfold gt_eq. auto. }
  { unfold gt_eq. simpl.
    remember (apply_gt_fun f1 t1) as p11. destruct p11.
    remember (apply_gt_fun f1 t2) as p12. destruct p12.
    remember (apply_gt_fun f2 t1) as p21. destruct p21.
    remember (apply_gt_fun f2 t2) as p22. destruct p22.
    simpl.
    assert (x = x1).
    { apply IHt1. intros. apply F12_FV_EQ. unfold fv_term.
      apply (set_union_intro name_eq_dec). left. auto. }
    assert (x0 = x2).
    { apply IHt2. intros. apply F12_FV_EQ. unfold fv_term.
      apply (set_union_intro name_eq_dec). right. auto. }
    subst. auto. }
Qed.

Lemma gt_fun_eq_trans
      (f1 f2 f3 : gt_fun)
      (EQ12 : gt_fun_eq f1 f2)
      (EQ23 : gt_fun_eq f2 f3) :
      gt_fun_eq f1 f3.
Proof.
  revert EQ12 EQ23. unfold gt_fun_eq. unfold gt_eq. intros.
  rewrite EQ12. auto.
Qed.

Lemma subst_of_gt
      (t : term)
      (s : subst)
      (f : gt_fun)
      (FV_IMG : forall x : name, In x (fv_term t) -> image s x = Some (proj1_sig (f x))) :
      apply_subst s t = proj1_sig (apply_gt_fun f t).
Proof.
  induction t.
  { simpl. replace (image s n) with (Some (proj1_sig (f n))).
    { auto. }
    { symmetry. apply FV_IMG. constructor. auto. } }
  { auto. }
  { simpl.
    destruct (apply_gt_fun f t1).
    destruct (apply_gt_fun f t2).
    simpl.
    replace x with (apply_subst s t1).
    { replace x0 with (apply_subst s t2).
      { auto. }
      { apply IHt2. intros. apply FV_IMG.
        apply set_union_intro2. auto. } }
    { apply IHt1. intros. apply FV_IMG.
      apply set_union_intro1. auto. } }
Qed.

Definition subst_gt_fun_compose (s : subst) (f : gt_fun) : gt_fun :=
  fun x => apply_gt_fun f (apply_subst s (Var x)).

Lemma gt_fun_apply_compose
      (s : subst)
      (f : gt_fun)
      (t : term) :
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
      (EQ : gt_fun_eq f1 f2)
      (s : subst) :
      gt_fun_eq (subst_gt_fun_compose s f1) (subst_gt_fun_compose s f2).
Proof.
  unfold gt_fun_eq. unfold gt_fun_eq in EQ. unfold subst_gt_fun_compose.
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
      (EQ : forall t, apply_subst s1 t = apply_subst s2 t) :
      gt_fun_eq (subst_gt_fun_compose s1 f) (subst_gt_fun_compose s2 f).
Proof.
  unfold gt_fun_eq. unfold subst_gt_fun_compose. unfold gt_eq.
  intro. rewrite EQ. auto.
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

Reserved Notation "[| g , f |]" (at level 0).

Inductive in_denotational_sem_goal : goal -> gt_fun -> Prop :=
| dsgCut    : forall f,  [| Cut , f |]
| dsgUnify  : forall f t1 t2 (UNI : gt_eq (apply_gt_fun f t1) (apply_gt_fun f t2)),
                             [| Unify t1 t2 , f |]
| dsgDisjL  : forall f g1 g2 (DSG : in_denotational_sem_goal g1 f),
                             [| Disj g1 g2 , f |]
| dsgDisjR  : forall f g1 g2 (DSG : in_denotational_sem_goal g2 f),
                             [| Disj g1 g2 , f |]
| dsgConj   : forall f g1 g2 (DSG_L : [| g1 , f |])
                             (DSG_R : [| g2 , f |]),
                             [| Conj g1 g2 , f |]
| dsgFresh  : forall f fn a fg (A_NOT_FV : ~ is_fv_of_goal a (Fresh fg))
                               (DSG : [| fg a , fn |])
                               (EASE : forall (x : name) (neq : x <> a), gt_eq (fn x) (f x)),
                               [| Fresh fg , f |]
| dsgInvoke : forall r t f (DSG : [| proj1_sig (MiniKanrenSyntax.P r) t , f |]),
                              [| Invoke r t, f |]
where "[| g , f |]" := (in_denotational_sem_goal g f).

Hint Constructors in_denotational_sem_goal.

Reserved Notation "[| n | g , f |]" (at level 0).

Inductive in_denotational_sem_lev_goal : nat -> goal -> gt_fun -> Prop :=
| dslgCut    : forall l f, [| (S l) | Cut , f |]
| dslgUnify  : forall l f t1 t2 (UNI : gt_eq (apply_gt_fun f t1) (apply_gt_fun f t2)),
                                [| S l | Unify t1 t2 , f |]
| dslgDisjL  : forall l f g1 g2 (DSG : [| l | g1 , f |]),
                                [| l | Disj g1 g2 , f |]
| dslgDisjR  : forall l f g1 g2 (DSG : [| l | g2 , f |]),
                                [| l | Disj g1 g2 , f |]
| dslgConj   : forall l f g1 g2 (DSG_L : [| l | g1 , f |])
                                (DSG_R : [| l | g2 , f |]),
                                [| l | Conj g1 g2 , f |]
| dslgFresh  : forall l f fn a fg (A_NOT_FV : ~ is_fv_of_goal a (Fresh fg))
                                  (DSG : [| l | (fg a) , fn |])
                                  (EASE : forall (x : name) (neq : x <> a), gt_eq (fn x) (f x)),
                                  in_denotational_sem_lev_goal l (Fresh fg) f
| dslgInvoke : forall l r t f (DSG : [| l | (proj1_sig (MiniKanrenSyntax.P r) t) , f |]),
                              [| S l | Invoke r t , f |]
where "[| n | g , f |]" := (in_denotational_sem_lev_goal n g f).

Hint Constructors in_denotational_sem_lev_goal.

Lemma in_denotational_sem_zero_lev
      (g : goal)
      (f : gt_fun) :
      ~ [| 0 | g , f |].
Proof.
  intro. remember 0 as l. induction H; inversion Heql; auto.
Qed.

Lemma in_denotational_sem_lev_monotone
      (l : nat)
      (g : goal)
      (f : gt_fun)
      (DSG : [| l | g , f |])
      (l' : nat)
      (LE: l <= l')
      : [| l' | g , f |].
Proof.
  revert LE. revert l'. induction DSG; eauto.
  1-2: intros; destruct l'; auto; inversion LE.
  { intros. destruct l'.
    { inversion LE. }
    { apply le_S_n in LE. auto. } }
Qed.

Lemma in_denotational_sem_some_lev
      (g : goal)
      (f : gt_fun)
      (DSG : [| g , f |]) :
      exists l, [| l | g , f |].
Proof.
  induction DSG.
  1-2: exists 1; auto.
  1-2, 4-5: destruct IHDSG; eauto.
  { destruct IHDSG1. destruct IHDSG2.
    exists (max x x0). constructor.
    { eapply in_denotational_sem_lev_monotone; eauto. apply PeanoNat.Nat.le_max_l. }
    { eapply in_denotational_sem_lev_monotone; eauto. apply PeanoNat.Nat.le_max_r. } }
Qed.

Lemma completeness_condition
      (f f' : gt_fun)
      (g : goal)
      (l : nat)
      (FF'_EQ : forall x, is_fv_of_goal x g -> gt_eq (f x) (f' x))
      (DSG : [| l | g , f |]) :
      [| l | g , f' |].
Proof.
  revert FF'_EQ. revert f'. induction DSG; intros.
  { constructor. }
  { constructor. assert (gt_eq (apply_gt_fun f t1) (apply_gt_fun f' t1)).
    { apply apply_gt_fun_fv. auto. }
    assert (gt_eq (apply_gt_fun f t2) (apply_gt_fun f' t2)).
    { apply apply_gt_fun_fv. auto. }
    revert UNI H H0. unfold gt_eq. intros. congruence. }
  { constructor. apply IHDSG. intros.
    apply FF'_EQ. auto. }
  { apply dslgDisjR. apply IHDSG. intros.
    apply FF'_EQ. auto. }
  { constructor.
    { apply IHDSG1; intros; apply FF'_EQ; auto. }
    { apply IHDSG2; intros; apply FF'_EQ; auto. } }
  { remember (fun x => if name_eq_dec x a
                         then fn a
                         else f' x) as fn'.
    apply dslgFresh with fn' a; auto.
    { apply IHDSG. intros. rewrite Heqfn'.
      destruct (name_eq_dec x a).
      { unfold gt_eq. subst. auto. }
      { specialize (EASE _ n). red. rewrite EASE.
        apply FF'_EQ. eauto. } }
    { rewrite Heqfn'. intros.
      destruct (name_eq_dec x a); try contradiction.
      reflexivity. } }
  { constructor. apply IHDSG. intros.
    apply FF'_EQ. constructor.
    remember (MiniKanrenSyntax.P r). destruct d as [rel [Hcl Hco]].
    simpl in H. red in Hcl. red in Hcl. auto. }
Qed.

Lemma den_sem_rename_var
      (g1 g2 : goal)
      (CG : consistent_goal g1)
      (n : nat)
      (G1_BOUND : forall x : name, is_fv_of_goal x g1 -> x < n)
      (G2_BOUND : forall x : name, is_fv_of_goal x g2 -> x < n)
      (a1 a2 : name)
      (A12_NEQ : a1 <> a2)
      (A2_FRESH : ~ is_fv_of_goal a2 g1)
      (REN : renaming a1 a2 g1 g2)
      (fa1 fa2 : gt_fun)
      (l : nat)
      (DSG1 : [| l | g1 , fa1 |])
      (F_SWITCH : gt_eq (fa1 a1) (fa2 a2))
      (F12_EQ : forall x, x <> a1 -> x <> a2 -> gt_eq (fa1 x) (fa2 x)) :
      [| l | g2 , fa2 |].
Proof.
  revert CG G1_BOUND G2_BOUND A12_NEQ A2_FRESH REN DSG1 F_SWITCH F12_EQ.
  revert g1 g2 n a1 a2 fa1 fa2.
  induction l.
  { intros. apply in_denotational_sem_zero_lev in DSG1. contradiction. }
  { induction g1; intros; good_inversion DSG1; good_inversion REN; good_inversion CG.
    { constructor. }
    { constructor.
      etransitivity.
      2: etransitivity.
      2: apply UNI.
      1-2: etransitivity.
      1, 3: symmetry.
      1, 4: apply gt_fun_apply_compose.
      all: apply apply_gt_fun_fv; intros; unfold subst_gt_fun_compose;
        simpl; destruct (Nat.eq_dec a1 x); subst; symmetry; auto;
        apply F12_EQ; auto; intro; subst; auto. }
    { apply dslgDisjL; eauto. eapply IHg1_1; eauto. }
    { apply dslgDisjR; eauto. eapply IHg1_2; eauto. }
    { constructor; eauto.
      { eapply IHg1_1; eauto. }
      { eapply IHg1_2; eauto. } }
    { apply completeness_condition with fa1.
      { intros; apply F12_EQ; intro; subst; auto. }
      { econstructor.
        2: eauto.
        all: eauto. } }
    { rename g into fg. rename fn into fn1. rename a into a0. red in CB_FG.
      assert (very_fresh_var : exists y, a0 <> y /\ a2 <> y /\
                                         (~ is_fv_of_goal y (Fresh fg)) /\
                                         (~ is_fv_of_goal y (Fresh rfg))).
      { destruct (name_eq_dec a0 n); destruct (name_eq_dec a0 (S n));
        destruct (name_eq_dec a2 n); destruct (name_eq_dec a2 (S n)); subst; try omega.
        5, 6, 8, 9: exists n.
        1, 3, 9: exists (S n).
        4, 5: exists (S (S n)).
        all: repeat split; try omega.
        all: intro CH; try apply G1_BOUND in CH; try apply G2_BOUND in CH; omega. }
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
            { apply EASE. auto. }
            { auto. } } } }
      { destruct (name_eq_dec x a1); subst.
        { reflexivity. }
        { destruct (name_eq_dec x a3).
          { contradiction. }
          { destruct (name_eq_dec x a0); subst.
            { reflexivity. }
            { etransitivity.
              { apply EASE. auto. }
              { apply F12_EQ; auto. } } } } } }
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
      (CG : consistent_goal (Fresh b))
      (n : nat)
      (FRESH_BOUND : forall x : name, is_fv_of_goal x (Fresh b) -> x < n)
      (a1 a2 : name)
      (A1_FRESH : ~ is_fv_of_goal a1 (Fresh b))
      (A2_FRESH : ~ is_fv_of_goal a2 (Fresh b))
      (fa1 fa2 : gt_fun)
      (l : nat)
      (DSG1 : in_denotational_sem_lev_goal l (b a1) fa1)
      (F_SWITCH : gt_eq (fa1 a1) (fa2 a2))
      (F12_EQ : forall x, x <> a1 -> x <> a2 -> gt_eq (fa1 x) (fa2 x)) :
      [| l | b a2 , fa2 |].
Proof.
  destruct (name_eq_dec a1 a2); subst.
  { apply completeness_condition with fa1; auto.
    intros. destruct (name_eq_dec x a2); subst; auto. }
  { good_inversion CG. red in CB_FG.
    eapply den_sem_rename_var with (g1 := (b a1)) (n := max n (max (S a1) (S a2))); eauto.
    { intros. destruct (name_eq_dec x a1); subst.
      { zify. omega. }
      { assert (x < n); eauto. zify. omega. } }
    { intros. destruct (name_eq_dec x a2); subst.
      { zify. omega. }
      { assert (x < n); eauto. zify. omega. } } }
Qed.
