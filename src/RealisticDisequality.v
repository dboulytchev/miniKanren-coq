Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Extraction.

Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Stream.
Require Import DenotationalSem.
Require Import OperationalSem.
Require Import OpSemSoundness.
Require Import OpSemCompleteness.


Module RealisticConstraintStore <: ConstraintStoreSig.

Definition constraint_store : Set := list subst.



Definition in_denotational_sem_cs (s : subst) (cs : constraint_store) (f : repr_fun) :=
  forall w, In w cs -> ~ [compose s w, f].

Notation "[| s , cs , f |]" := (in_denotational_sem_cs s cs f) (at level 0).

Lemma ds_cs_append
      (s : subst)
      (cs : constraint_store)
      (w : subst)
      (f : repr_fun)
      (DSC : ~ [compose s w, f])
      (DSCS : [| s , cs , f |]) :
      [| s , w :: cs , f |].
Proof.
  red. intros. destruct H; subst; auto.
Qed.

Lemma ds_cs_decompose
      (s : subst)
      (cs : constraint_store)
      (w : subst)
      (f : repr_fun)
      (DSCS : [| s , w :: cs , f |]) :
      (~ [compose s w, f]) /\ [| s , cs , f |].
Proof.
  red in DSCS. split.
  { apply DSCS. left. auto. }
  { red. intros. apply DSCS. right. auto. }
Qed.



Definition wf_constraint (s : subst) (w : subst) : Prop := narrowing_subst w /\ extending_subst s w /\ nodup_dom w.

Definition wf_cs (s : subst) (cs : constraint_store) : Prop :=
  forall w, In w cs -> wf_constraint s w.

Lemma wf_cs_head (s : subst)
              (w : subst)
              (cs : constraint_store)
              (WF : wf_cs s (w :: cs)) :
              wf_constraint s w.
Proof. red. intros. apply WF. left. auto. Qed.

Lemma wf_cs_tail (s : subst)
              (w : subst)
              (cs : constraint_store)
              (WF : wf_cs s (w :: cs)) :
              wf_cs s cs.
Proof. red. intros. apply WF. right. auto. Qed.



Definition init_cs : constraint_store := [].

Lemma wf_init_cs : wf_cs empty_subst init_cs.
Proof. red. intros w C. inversion C. Qed.



Inductive add_constraint_ind_def : subst -> constraint_store -> term -> term -> option constraint_store -> Prop :=
| acF : forall s cs t1 t2    (MGU : mgu (apply_subst s t1) (apply_subst s t2) None),
                             add_constraint_ind_def s cs t1 t2 (Some cs)
| acE : forall s cs t1 t2    (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some empty_subst)),
                             add_constraint_ind_def s cs t1 t2 None
| acNE : forall s cs t1 t2 w (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some w))
                             (W_NEMP : w <> empty_subst),
                             add_constraint_ind_def s cs t1 t2 (Some (w :: cs)).

Hint Constructors add_constraint_ind_def : core.

Definition add_constraint := add_constraint_ind_def.

Lemma add_constraint_exists :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term),
    {r : option constraint_store & add_constraint s cs t1 t2 r}.
Proof.
  intros. assert (MGU_E := mgu_exists (apply_subst s t1) (apply_subst s t2)).
  destruct MGU_E as [r MGU_R]. destruct r.
  { destruct s0.
    { exists None. red. auto. }
    { exists (Some ((p :: s0) :: cs)). red. constructor; auto. intro C; inversion C. } }
  { exists (Some cs). red. auto. }
Qed.

Lemma add_constraint_unique :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term) (r r' : option constraint_store),
    add_constraint s cs t1 t2 r -> add_constraint s cs t1 t2 r' -> r = r'.
Proof.
  intros. good_inversion H; good_inversion H0; auto;
  assert (eq := mgu_unique _ _ _ _ MGU MGU0); inversion eq; auto.
  { symmetry in H0. contradiction. }
  { contradiction. }
Qed.

Lemma add_constraint_wf_preservation :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term) (cs' : constraint_store),
    narrowing_subst s ->
    add_constraint s cs t1 t2 (Some cs') ->
    wf_cs s cs ->
    wf_cs s cs'.
Proof.
  intros. good_inversion H0; auto.
  red in H1. red. intros. destruct H0.
  { subst. split; try split.
    { eapply mgu_is_narrowing; eauto. }
    { eapply mgu_is_extending; eauto. }
    { eapply mgu_nodup_dom; eauto. } }
  { apply H1; auto. }
Qed.


Fixpoint list_to_term (ts : list term) : term :=
  match ts with
  | [] => Cst 0
  | t :: ts => Con 1 t (list_to_term ts)
  end.

Definition mgu_lists (tps : list (term * term)) (r : option subst) : Prop :=
  mgu (list_to_term (List.map fst tps)) (list_to_term (List.map snd tps)) r.

Definition upd_constr (s : subst) (w : subst) (d : subst) (r : option subst) : Prop :=
  mgu_lists (List.map (fun p => (apply_subst d (Var (fst p)), apply_subst d (snd p))) w) r.

Lemma upd_constr_exists :
  forall (s : subst) (w : subst) (d : subst),
    {r : option subst & upd_constr s w d r}.
Proof.
  intros.
  assert (MGU_E :=
    mgu_exists
      (list_to_term (map fst (map (fun p => (apply_subst d (Var (fst p)), apply_subst d (snd p))) w)))
      (list_to_term (map snd (map (fun p => (apply_subst d (Var (fst p)), apply_subst d (snd p))) w)))).
  destruct MGU_E as [r MGU_R]. exists r. auto.
Qed.

Lemma upd_constr_unique :
  forall (s : subst) (w : subst) (d : subst) (r r' : option subst),
    upd_constr s w d r -> upd_constr s w d r' -> r = r'.
Proof.
  intros.
  assert (MGU_U :=
    mgu_unique
      (list_to_term (map fst (map (fun p => (apply_subst d (Var (fst p)), apply_subst d (snd p))) w)))
      (list_to_term (map snd (map (fun p => (apply_subst d (Var (fst p)), apply_subst d (snd p))) w)))).
  apply MGU_U; auto.
Qed.

Lemma in_dom_monotone
      (x : name)
      (s : subst)
      (y : name)
      (t : term)
      (IN_DOM : in_subst_dom s x) :
      in_subst_dom ((y, t) :: s) x.
Proof.
  red. simpl. destruct (PeanoNat.Nat.eq_dec y x).
  { eexists; eauto. }
  { auto. }
Qed.

Lemma in_vran_monotone
      (x : name)
      (s : subst)
      (y : name)
      (t : term)
      (NODD : nodup_dom ((y, t) :: s))
      (IN_VRAN : in_subst_vran s x) :
      in_subst_vran ((y, t) :: s) x.
Proof.
  good_inversion NODD. red. red in IN_VRAN. destruct IN_VRAN as [x' [t' [IMG_x' FV_x_t']]].
  exists x'. exists t'. simpl. destruct (PeanoNat.Nat.eq_dec y x').
  { subst. exfalso. apply H1. induction s.
    { good_inversion IMG_x'. }
    { destruct a as [x'' t'']. simpl. simpl in IMG_x'.
      destruct (PeanoNat.Nat.eq_dec x'' x').
      { left. auto. }
      { right. apply IHs; auto.
        { intro IN_x_s. apply H1. simpl. right. auto. }
        { good_inversion H2. auto. } } } }
  { split; auto. }
Qed.

Lemma upd_constr_wf_preservation :
  forall (s : subst) (w : subst) (d : subst) (w' : subst),
    narrowing_subst s ->
    narrowing_subst d ->
    extending_subst s d ->
    upd_constr s w d (Some w') ->
    wf_constraint s w ->
    wf_constraint (compose s d) w'.
Proof.
  intros s w d w' NAR_S NAR_D EXT_SD UPD WF. split; try split.
  { red in UPD. red in UPD. eapply mgu_is_narrowing; eauto. }
  { red. red in UPD. red in UPD.
    remember (list_to_term (map fst (map (fun p => (apply_subst d (Var (fst p)), apply_subst d (snd p))) w))) as lterm1.
    remember (list_to_term (map snd (map (fun p => (apply_subst d (Var (fst p)), apply_subst d (snd p))) w))) as lterm2.
    assert (LTERM1_FV : forall x, In x (fv_term lterm1) -> (in_subst_dom w x /\ image d x = None) \/ in_subst_vran d x).
    { clear WF Heqlterm2 UPD lterm2. revert Heqlterm1. revert lterm1. induction w; intros lterm1 EQ1 x IN_FV.
      { simpl in EQ1. subst. contradiction. }
      { simpl in EQ1. rewrite EQ1 in IN_FV. simpl in IN_FV. apply (set_union_elim name_eq_dec) in IN_FV.
        destruct IN_FV.
        { destruct a as [y t]. simpl in H. destruct (image d y) eqn:IMG_D.
          { right. red. eexists; eexists; eauto. }
          { left. simpl in H. destruct H; try contradiction.
            subst. split; auto. red. exists t. simpl.
            destruct (PeanoNat.Nat.eq_dec x x); try contradiction. auto. } }
        { apply (IHw _ eq_refl) in H. destruct H.
          { left. destruct H. split; auto. destruct a. eapply in_dom_monotone; eauto. }
          { right. auto. } } } }
    assert (LTERM2_FV : forall x, In x (fv_term lterm2) -> (in_subst_vran w x /\ image d x = None) \/ in_subst_vran d x).
    { destruct WF as [_ [_ NODD_w]]. clear LTERM1_FV Heqlterm1 UPD lterm1. revert Heqlterm2. revert lterm2.
      induction w; intros lterm2 EQ2 x IN_FV.
      { simpl in EQ2. subst. contradiction. }
      { simpl in EQ2. rewrite EQ2 in IN_FV. simpl in IN_FV. apply (set_union_elim name_eq_dec) in IN_FV.
        destruct IN_FV.
        { destruct a as [y t]. simpl in H. apply apply_subst_FV_stronger in H.
          destruct H.
          { left. destruct H. split; auto.
            red. exists y. exists t. split; auto.
            simpl. destruct (PeanoNat.Nat.eq_dec y y); try contradiction. auto. }
          { right. auto. } }
        { assert (NODD_w_copy := NODD_w). good_inversion NODD_w. clear H2. rename H3 into NODD_w.
          apply (IHw NODD_w _ eq_refl) in H. destruct H.
          { left. destruct H. split; auto. destruct a. eapply in_vran_monotone; eauto. }
          { right. auto. } } } }
    assert (LTERMS_DOM_C : forall x, (In x (fv_term lterm1) \/ In x (fv_term lterm2)) ->
                                     in_subst_dom (compose s d) x -> False).
    { intros x IN_LTERM12 IN_COMP. apply compose_dom in IN_COMP. red in WF.
      destruct WF as [NAR_W [EXT_SW _]].
      red in EXT_SW. destruct EXT_SW as [EXT_SW_DOM EXT_SW_VRAN].
      red in EXT_SD. destruct EXT_SD as [EXT_SD_DOM EXT_SD_VRAN].
      red in NAR_W. destruct IN_LTERM12.
      { apply LTERM1_FV in H. destruct H.
        { destruct H. destruct IN_COMP.
          { specialize (EXT_SW_DOM _ H). contradiction. }
          { red in H1. destruct H1. rewrite H0 in H1. good_inversion H1. } }
        { destruct IN_COMP.
          { specialize (EXT_SD_VRAN _ H). contradiction. }
          { specialize (NAR_D _ H). contradiction. } } }
      { apply LTERM2_FV in H. destruct H.
        { destruct H. destruct IN_COMP.
          { specialize (EXT_SW_VRAN _ H). contradiction. }
          { red in H1. destruct H1. rewrite H0 in H1. good_inversion H1. } }
        { destruct IN_COMP.
          { specialize (EXT_SD_VRAN _ H). contradiction. }
          { specialize (NAR_D _ H). contradiction. } } } }
    split.
    { intros. intro. eapply LTERMS_DOM_C; eauto. eapply mgu_dom;  eauto. }
    { intros. intro. eapply LTERMS_DOM_C; eauto. eapply mgu_vran; eauto. } }
  { red in UPD. red in UPD. eapply mgu_nodup_dom; eauto. }
Qed.



Inductive upd_cs_ind_def : subst -> constraint_store -> subst -> option constraint_store -> Prop :=
| uN  : forall s      d,       upd_cs_ind_def s [] d (Some [])
| uI  : forall s w cs d        (UPD : upd_cs_ind_def s cs d None), 
                               upd_cs_ind_def s (w :: cs) d None
| uE  : forall s w cs d        (UPD_C : upd_constr s w d (Some empty_subst)),
                               upd_cs_ind_def s (w :: cs) d None
| uF  : forall s w cs d    cs' (UPD_C : upd_constr s w d None)
                               (UPD : upd_cs_ind_def s cs d (Some cs')),
                               upd_cs_ind_def s (w :: cs) d (Some cs')
| uNE : forall s w cs d w' cs' (UPD_C : upd_constr s w d (Some w'))
                               (W_NEMP : w' <> empty_subst)
                               (UPD : upd_cs_ind_def s cs d (Some cs')),
                               upd_cs_ind_def s (w :: cs) d (Some (w' :: cs')).

Hint Constructors upd_cs_ind_def : core.

Definition upd_cs := upd_cs_ind_def.

Lemma upd_cs_exists :
  forall (s : subst) (cs : constraint_store) (d : subst),
    {r : option constraint_store & upd_cs s cs d r}.
Proof.
  intros. induction cs.
  { exists (Some []). red. auto. }
  { destruct IHcs as [rcs' UPD_RCS'].
    assert (UPD_C_E := upd_constr_exists s a d). destruct UPD_C_E as [rw' UPD_C_RW'].
    destruct rcs' as [cs' | ].
    { destruct rw' as [w' | ].
      { destruct w'.
        { exists None. red. auto. }
        { exists (Some ((p :: w') :: cs')). red. apply uNE; auto.
          intro C. inversion C. } }
      { exists (Some cs'). red. auto. } }
    { exists None. red. auto. } }
Qed.


Lemma upd_cs_unique :
  forall (s : subst) (cs : constraint_store) (d : subst) (r r' : option constraint_store),
    upd_cs s cs d r -> upd_cs s cs d r' -> r = r'.
Proof.
  intros. revert H H0. revert r r'. induction cs; intros r r' UPD_R UPD_R'.
  { good_inversion UPD_R. good_inversion UPD_R'. auto. }
  { good_inversion UPD_R; good_inversion UPD_R';
    try (specialize (IHcs _ _ UPD UPD0); good_inversion IHcs);
    try (specialize (upd_constr_unique _ _ _ _ _ UPD_C UPD_C0); intro UPD_C_U; good_inversion UPD_C_U);
    try contradiction; auto. }
Qed.

Lemma upd_cs_wf_preservation :
  forall (s : subst) (cs : constraint_store) (d : subst) (cs' : constraint_store),
    narrowing_subst s ->
    narrowing_subst d ->
    extending_subst s d ->
    upd_cs s cs d (Some cs') ->
    wf_cs s cs ->
    wf_cs (compose s d) cs'.
Proof.
  intros. revert H2. revert cs'. induction cs; intros; good_inversion H2; auto.
  { red. intros. good_inversion H2. }
  { apply IHcs; auto. eapply wf_cs_tail; eauto. }
  { red. intros. destruct H2.
    { subst. eapply upd_constr_wf_preservation; eauto. eapply wf_cs_head; eauto. }
    { eapply IHcs; eauto. eapply wf_cs_tail; eauto. } }
Qed.



Lemma init_condition : forall f, [| empty_subst , init_cs , f |].
Proof. unfold in_denotational_sem_cs. contradiction. Qed.



Lemma compose_with_empty
      (s : subst) :
      compose s empty_subst = s.
Proof.
  induction s.
  { auto. }
  { unfold compose. destruct a. simpl. rewrite apply_empty.
    apply f_equal. auto. }
Qed.

Lemma denotational_sem_uni_fail
      (s : subst)
      (t1 t2 : term)
      (MGU : mgu (apply_subst s t1) (apply_subst s t2) None)
      (f : repr_fun)
      (DSS : [ s , f ])
      (EQ : gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2)) :
      False.
Proof.
  red in DSS. destruct DSS as [f' EQ_f_sf'].
  assert (gt_eq (apply_repr_fun f' (apply_subst s t1)) (apply_repr_fun f' (apply_subst s t2))).
  { red. rewrite <- repr_fun_apply_compose. rewrite <- repr_fun_apply_compose.
    etransitivity.
    1: etransitivity.
    2: eapply EQ.
    2: symmetry.
    all: eapply repr_fun_eq_apply; eapply EQ_f_sf'. }
  apply unfier_from_gt_unifier in H. destruct H as [s' [UNI DSS_s']].
  eapply mgu_non_unifiable; eauto.
Qed.

(**)


Lemma terms_list_apply_subst_proj_swap_1
      (s : subst)
      (ts : list (term * term)) :
      map fst (map (fun p => (apply_subst s (fst p), apply_subst s (snd p))) ts) =
      map (apply_subst s) (map fst ts).
Proof. induction ts; auto. simpl. rewrite IHts. auto. Qed.

Lemma terms_list_apply_subst_proj_swap_2
      (s : subst)
      (ts : list (term * term)) :
      map snd (map (fun p => (apply_subst s (fst p), apply_subst s (snd p))) ts) =
      map (apply_subst s) (map snd ts).
Proof. induction ts; auto. simpl. rewrite IHts. auto. Qed.

Lemma term_list_apply_subst_swap
      (s : subst)
      (ts : list term) :
      list_to_term (map (apply_subst s) ts) = apply_subst s (list_to_term ts).
Proof. induction ts; auto. simpl. rewrite IHts. auto. Qed.

Lemma terms_list_repr_fun_unifier_iff
      (ts : list (term * term))
      (f : repr_fun) : 
      gt_eq (apply_repr_fun f (list_to_term (map fst ts))) (apply_repr_fun f (list_to_term (map snd ts))) <->
      (forall t1 t2, In (t1, t2) ts -> gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2)).
Proof.
  induction ts; auto.
  { split; intros; try contradiction. reflexivity. }
  { split; intros.
    { destruct a. destruct H0.
      { good_inversion H0. simpl in H.
        destruct (apply_repr_fun f t1). destruct (apply_repr_fun f (list_to_term (map fst ts))).
        destruct (apply_repr_fun f t2). destruct (apply_repr_fun f (list_to_term (map snd ts))).
        unfold gt_eq in H. simpl in H. unfold gt_eq. simpl. good_inversion H. auto. }
      { revert H0. revert t1 t2. rewrite <- IHts. simpl in H.
        destruct (apply_repr_fun f t). destruct (apply_repr_fun f (list_to_term (map fst ts))).
        destruct (apply_repr_fun f t0). destruct (apply_repr_fun f (list_to_term (map snd ts))).
        unfold gt_eq in H. simpl in H. unfold gt_eq. simpl. good_inversion H. auto. } }
    { destruct a.
      assert (gt_eq (apply_repr_fun f t) (apply_repr_fun f t0) /\
              gt_eq (apply_repr_fun f (list_to_term (map fst ts)))
                    (apply_repr_fun f (list_to_term (map snd ts)))).
      { rewrite IHts. split.
        { apply H. left. auto. }
        { intros. apply H. right. auto. } }
      destruct H0. simpl.
      destruct (apply_repr_fun f t). destruct (apply_repr_fun f (list_to_term (map fst ts))).
      destruct (apply_repr_fun f t0). destruct (apply_repr_fun f (list_to_term (map snd ts))).
      unfold gt_eq in H0. simpl in H0. unfold gt_eq in H1. simpl in H1. unfold gt_eq. simpl.
      congruence. } }
Qed.

Lemma denotational_sem_uni_fail_lists
      (s : subst)
      (ts : list (term * term))
      (MGU : mgu_lists (map (fun p => (apply_subst s (fst p), apply_subst s (snd p))) ts) None)
      (f : repr_fun)
      (DSS : [ s , f ])
      (EQS : forall t1 t2, In (t1, t2) ts -> gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2)) :
      False.
Proof.
  red in MGU.
  rewrite terms_list_apply_subst_proj_swap_1 in MGU. rewrite terms_list_apply_subst_proj_swap_2 in MGU.
  do 2 (rewrite term_list_apply_subst_swap in MGU). rewrite <- terms_list_repr_fun_unifier_iff in EQS.
  eapply denotational_sem_uni_fail; eauto.
Qed.

Lemma denotational_sem_uni_lists
      (s d : subst)
      (ts : list (term * term))
      (MGU : mgu_lists (map (fun p => (apply_subst s (fst p), apply_subst s (snd p))) ts) (Some d))
      (f : repr_fun) :
      [compose s d , f] <-> [s , f] /\
                            (forall t1 t2, In (t1, t2) ts -> gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2)).
Proof.
  red in MGU.
  rewrite terms_list_apply_subst_proj_swap_1 in MGU. rewrite terms_list_apply_subst_proj_swap_2 in MGU.
  do 2 (rewrite term_list_apply_subst_swap in MGU). rewrite <- terms_list_repr_fun_unifier_iff.
  eapply denotational_sem_uni; eauto.
Qed.


Lemma add_constraint_fail_condition :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term),
    wf_cs s cs ->
    add_constraint s cs t1 t2 None ->
    forall f, ~ ([| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |]).
Proof.
  intros. good_inversion H0.
  apply denotational_sem_uni with (f := f) in MGU. rewrite compose_with_empty in MGU.
  rewrite MGU. intros [_ [[_ UNI] DISUNI]]. good_inversion DISUNI. auto.
Qed.

Lemma add_constraint_success_condition :
  forall (s : subst) (cs cs' : constraint_store) (t1 t2 : term),
    wf_cs s cs ->
    add_constraint s cs t1 t2 (Some cs') ->
    forall f, [| s , cs' , f |] /\ [ s , f ] <->
              [| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |].
Proof.
  intros. good_inversion H0.
  { split.
    { intros [DSCS DSS]. split; try split; auto.
      constructor. intro EQ. eapply denotational_sem_uni_fail; eauto. }
    { intros [DSCS [DSS _]]. split; auto. } }
  { apply denotational_sem_uni with (f := f) in MGU. split.
    { intros [DSCS DSS]. apply ds_cs_decompose in DSCS.
      destruct DSCS as [DSC DSCS]. split; try split; auto.
      constructor. intro EQ. apply DSC. apply MGU. split; auto. }
    { intros [DSCS [DSS DISEQ]]. split; try split; auto.
      apply ds_cs_append; auto. rewrite MGU. intros [_ EQ].
      good_inversion DISEQ. auto. } }
Qed.


Lemma image_var_dom
      (s : subst)
      (x : name)
      (t : term)
      (NODD : nodup_dom s)
      (IN : In (x, t) s) :
      image s x = Some t.
Proof.
  red in NODD. induction s; try contradiction.
  good_inversion NODD. destruct a as [z tz].
  simpl. destruct (PeanoNat.Nat.eq_dec z x); subst.
  { destruct IN.
    { good_inversion H. auto. }
    { exfalso. apply H1. apply (in_map fst) in H. auto. } }
  { apply IHs; auto. destruct IN; auto. good_inversion H. contradiction. }
Qed.

Lemma apply_subst_var_dom
      (s : subst)
      (x : name)
      (t : term)
      (NODD : nodup_dom s)
      (IN : In (x, t) s) :
      apply_subst s (Var x) = t.
Proof. simpl. rewrite (image_var_dom _ _ _ NODD IN). auto. Qed.

Lemma apply_subst_FV_not_dom
      (s : subst)
      (t : term)
      (FV_ND : forall x : name, In x (fv_term t) -> ~ in_subst_dom s x) :
      apply_subst s t = t.
Proof.
  induction t; auto.
  { simpl. destruct (image s n) eqn:EQ; auto.
    exfalso. apply (FV_ND n).
    { left. auto. }
    { red. exists t. auto. } }
  { simpl. rewrite IHt1. 1: rewrite IHt2; auto.
    { intros. apply FV_ND. simpl. apply (set_union_intro name_eq_dec). right. auto. }
    { intros. apply FV_ND. simpl. apply (set_union_intro name_eq_dec). left. auto. } }
Qed.

Lemma ignore_s_for_wf_constraint
      (s w : subst)
      (WF : wf_constraint s w)
      (y : name)
      (t : term)
      (IN_w : In (y, t) w) :
      apply_subst s (Var y) = Var y /\ apply_subst s t = t.
Proof.
  red in WF. destruct WF as [_ [EXT NODD]]. destruct EXT as [NDOM_DOM NDOM_VRAN].
  split.
  { apply apply_subst_FV_not_dom. intros. destruct H; try contradiction. subst. apply NDOM_DOM.
    red. exists t. apply image_var_dom; auto. }
  { apply apply_subst_FV_not_dom. intros. apply NDOM_VRAN.
    red. exists y. exists t. split; auto. apply image_var_dom; auto. }
Qed.

Lemma ignore_w_in_ran_for_wf_constraint
      (s w : subst)
      (WF : wf_constraint s w)
      (y : name)
      (t : term)
      (IN_w : In (y, t) w) :
      apply_subst w t = t.
Proof.
  red in WF. destruct WF as [NAR [_ NODD]]. red in NAR.
  apply apply_subst_FV_not_dom. intros. apply NAR.
  red. exists y. exists t. split; auto.
  apply image_var_dom; auto.
Qed.


Lemma upd_constr_fail
      (s w d : subst)
      (WFC : wf_constraint s w)
      (UPD_C : upd_constr s w d None)
      (f : repr_fun)
      (DSS_sd : [compose s d, f])
      (DSS_sw : [compose s w, f]) :
      False.
Proof.
  red in UPD_C. remember (map (fun p => (Var (fst p), snd p)) w) as w_v.
  assert (IN_wv_w : forall t1 t2, In (t1, t2) w_v -> exists y, t1 = Var y /\ In (y, t2) w).
  { subst. clear WFC DSS_sw UPD_C. induction w; try contradiction.
    intros. destruct a as [y t]. destruct H.
    { good_inversion H. exists y. split; auto. left. auto. }
    { specialize (IHw t1 t2 H). destruct IHw as [y0 [EQ_y0 IN_y0]].
      exists y0. split; auto. right. auto. } }
  assert (IGN_s : forall y t, In (y, t) w -> apply_subst s (Var y) = Var y /\ apply_subst s t = t).
  { intros. eapply ignore_s_for_wf_constraint; eauto. }
  assert (IGN_w_vran : forall y t, In (y, t) w -> apply_subst w t = t).
  { intros. eapply ignore_w_in_ran_for_wf_constraint; eauto. }
  assert (EQ_MAPS : 
    map (fun p => (apply_subst (compose s d)     (fst p) , apply_subst (compose s d) (snd p))) w_v =
    map (fun p => (apply_subst            d (Var (fst p)), apply_subst            d  (snd p))) w).
  { rewrite Heqw_v. clear IGN_w_vran IN_wv_w WFC UPD_C DSS_sw Heqw_v. induction w; auto.
    destruct a as [y t].
    Arguments apply_subst : simpl never. simpl.
    assert (CONJEQ : apply_subst s (Var y) = Var y /\ apply_subst s t = t).
    { apply IGN_s. left. auto. }
    destruct CONJEQ as [EQ1 EQ2]. do 2 (rewrite compose_correctness).
    rewrite EQ1. rewrite EQ2. apply f_equal. apply IHw.
    intros. apply IGN_s. right. auto. }
  rewrite <- EQ_MAPS in UPD_C. apply (denotational_sem_uni_fail_lists _ _ UPD_C f); auto.
  red in DSS_sw. destruct DSS_sw as [f' EQ_swf'_f]. intros t1 t2 IN_wv.
  etransitivity.
  1: etransitivity.
  1: symmetry.
  1,3: eapply repr_fun_eq_apply; eapply EQ_swf'_f.
  apply IN_wv_w in IN_wv. destruct IN_wv as [y [EQ_t1 IN_wv]]. subst. 
  destruct WFC as [_ [_ NODD]]. assert (EQ_n2_t2 := apply_subst_var_dom _ _ _ NODD IN_wv).
  assert (IN_w := IN_wv). apply IGN_s in IN_wv. destruct IN_wv as [EQ1 EQ2].
  do 2 (rewrite repr_fun_apply_compose). do 2 (rewrite compose_correctness).
  rewrite EQ1. rewrite EQ2. simpl. rewrite EQ_n2_t2. apply IGN_w_vran in IN_w.
  rewrite IN_w. auto.
Qed.


Lemma gt_eq_eq_repr_fun
      (t1 t2 : term)
      (f1 f2 : repr_fun)
      (FEQ : repr_fun_eq f1 f2)
      (GTEQ : gt_eq (apply_repr_fun f1 t1) (apply_repr_fun f1 t2)) :
      gt_eq (apply_repr_fun f2 t1) (apply_repr_fun f2 t2).
Proof.
  etransitivity.
  1: etransitivity.
  2: apply GTEQ.
  1: symmetry.
  all: eapply repr_fun_eq_apply; eapply FEQ.
Qed.


Lemma repr_fun_eq_symm
      (f1 f2 : repr_fun)
      (EQ : repr_fun_eq f1 f2) :
      repr_fun_eq f2 f1.
Proof. red. intros. symmetry. apply EQ. Qed.

Lemma upd_constr_success
      (s w d w' : subst)
      (WFC : wf_constraint s w)
      (UPD_C : upd_constr s w d (Some w'))
      (f : repr_fun)
      (DSS_sd : [compose s d, f]) :
      [compose s w, f] <-> [compose (compose s d) w', f].
Proof.
  red in UPD_C. remember (map (fun p => (Var (fst p), snd p)) w) as w_v.
  assert (IN_w_wv : forall y t, In (y, t) w -> In (Var y, t) w_v).
  { intros. subst. clear WFC UPD_C. induction w; try contradiction.
    destruct a as [z tz]. destruct H.
    { good_inversion H. left. auto. }
    { apply IHw in H. right. auto. } }
  assert (IN_wv_w : forall t1 t2, In (t1, t2) w_v -> exists y, t1 = Var y /\ In (y, t2) w).
  { subst. clear IN_w_wv WFC UPD_C. induction w; try contradiction.
    intros. destruct a as [y t]. destruct H.
    { good_inversion H. exists y. split; auto. left. auto. }
    { specialize (IHw t1 t2 H). destruct IHw as [y0 [EQ_y0 IN_y0]].
      exists y0. split; auto. right. auto. } }
  assert (IGN_s : forall y t, In (y, t) w -> apply_subst s (Var y) = Var y /\ apply_subst s t = t).
  { intros. eapply ignore_s_for_wf_constraint; eauto. }
  assert (IGN_w_vran : forall y t, In (y, t) w -> apply_subst w t = t).
  { intros. eapply ignore_w_in_ran_for_wf_constraint; eauto. }
  assert (EQ_MAPS : 
    map (fun p => (apply_subst (compose s d)     (fst p) , apply_subst (compose s d) (snd p))) w_v =
    map (fun p => (apply_subst            d (Var (fst p)), apply_subst            d  (snd p))) w).
  { rewrite Heqw_v. clear IN_w_wv IGN_w_vran IN_wv_w WFC UPD_C Heqw_v. induction w; auto.
    destruct a as [y t].
    Arguments apply_subst : simpl never. simpl.
    assert (CONJEQ : apply_subst s (Var y) = Var y /\ apply_subst s t = t).
    { apply IGN_s. left. auto. }
    destruct CONJEQ as [EQ1 EQ2]. do 2 (rewrite compose_correctness).
    rewrite EQ1. rewrite EQ2. apply f_equal. apply IHw.
    intros. apply IGN_s. right. auto. }
  rewrite <- EQ_MAPS in UPD_C. specialize (denotational_sem_uni_lists _ _ _ UPD_C f). intro EQUI.
  rewrite EQUI. clear EQ_MAPS EQUI UPD_C.
  assert (EQUI_ABUND : forall A, [compose s d, f] /\ A <-> A).
  { intros. split; auto. intros [_ AP]. auto. }
  rewrite EQUI_ABUND. clear EQUI_ABUND.
  split.
  { intros. red in H. destruct H as [f'' EQ_swf''_f].
    apply IN_wv_w in H0. destruct H0 as [y [EQ_t1 IN_wv]]. subst.
    apply (gt_eq_eq_repr_fun _ _ _ _ EQ_swf''_f).
    red. do 2 (rewrite repr_fun_apply_compose). do 2 (rewrite compose_correctness).
    specialize (IGN_s _ _ IN_wv). destruct IGN_s as [IGN_s_y IGN_s_t2]. specialize (IGN_w_vran _ _ IN_wv).
    rewrite IGN_s_y. rewrite IGN_s_t2. rewrite IGN_w_vran.
    destruct WFC as [_ [_ NODD]]. rewrite (apply_subst_var_dom _ _ _ NODD IN_wv). auto. }
  { intros. red in DSS_sd. destruct DSS_sd as [ff EQ_sdff_f].
    eapply repr_fun_eq_trans in EQ_sdff_f.
    2: apply repr_fun_eq_symm; eapply subst_repr_fun_compose_assoc_subst.
    remember (subst_repr_fun_compose d ff) as f'. clear Heqf'.
    red. exists f'.
    eapply repr_fun_eq_trans. 2: eapply EQ_sdff_f.
    eapply repr_fun_eq_trans. 1: eapply subst_repr_fun_compose_assoc_subst.
    apply repr_fun_eq_compose. red. intros. unfold subst_repr_fun_compose.
    assert (CASES := in_dec name_eq_dec x (map fst w)).
    destruct CASES.
    { assert (EX_IMG : exists t, In (x, t) w).
      { clear H IGN_w_vran IGN_s IN_w_wv IN_wv_w Heqw_v WFC. induction w; try contradiction.
        destruct a as [x0 t]. destruct i.
        { exists t. left. rewrite <- H. auto. }
        { apply IHw in H. destruct H as [t1 IN].
          exists t1. right. auto. } }
      destruct EX_IMG as [t IN]. assert (IN_w := IN). apply IN_w_wv in IN.
      apply H in IN. apply repr_fun_eq_symm in EQ_sdff_f.
      apply (gt_eq_eq_repr_fun _ _ _ _ EQ_sdff_f) in IN.
      red in IN. do 2 (rewrite repr_fun_apply_compose in IN).
      destruct WFC as [_ [_ NODD]]. rewrite (apply_subst_var_dom _ _ _ NODD IN_w). symmetry.
      apply IGN_s in IN_w. destruct IN_w as [EQ1 EQ2].
      rewrite EQ1 in IN. rewrite EQ2 in IN. auto. }
    { assert (IGN_w_x : apply_subst w (Var x) = Var x).
      { clear H IN_w_wv IGN_w_vran IGN_s IN_wv_w Heqw_v WFC. induction w; auto.
        destruct a as [y t]. unfold apply_subst. simpl.
        destruct (PeanoNat.Nat.eq_dec y x); subst.
        { exfalso. apply n. left. auto. }
        { apply IHw. intro IN. apply n. right. auto. } }
      rewrite IGN_w_x. reflexivity. } }
Qed.


Lemma upd_cs_fail_condition :
  forall (s : subst) (cs : constraint_store) (d : subst),
    wf_cs s cs ->
    upd_cs s cs d None ->
    forall f, ~ ([| s , cs , f |] /\ [ compose s d , f ]).
Proof.
  intros s cs ds. induction cs.
  { intros. good_inversion H0. }
  { intros. good_inversion H0.
    { intros [DSCS_acs DSS]. eapply IHcs; auto.
      { apply wf_cs_tail in H. auto. }
      { split; eauto. apply ds_cs_decompose in DSCS_acs.
        destruct DSCS_acs as [_ DSCS]. auto. } }
    { rename H into WF. intros [DSCS_acs DSS].
      apply wf_cs_head in WF. specialize (upd_constr_success _ _ _ _ WF UPD_C _ DSS).
      intros EQU. apply ds_cs_decompose in DSCS_acs. destruct DSCS_acs as [NDSS_sa].
      apply NDSS_sa. apply EQU. rewrite compose_with_empty. auto. } }
Qed.

Lemma upd_cs_success_condition :
  forall (s : subst) (cs : constraint_store) (d : subst) (cs' : constraint_store),
    wf_cs s cs ->
    upd_cs s cs d (Some cs') ->
    forall f, [| compose s d , cs' , f |] /\ [ compose s d , f ] <->
              [| s           , cs  , f |] /\ [ compose s d , f ].
Proof.
  intros s cs ds. induction cs.
  { intros. good_inversion H0. split; intros [A B]; split; auto;
    unfold in_denotational_sem_cs; contradiction. }
  { intros. rename H into WF_acs. good_inversion H0.
    { split; intros [DSCS DSS_sd]; split; auto.
      { apply ds_cs_append.
        { apply wf_cs_head in WF_acs. rename a into w.
          intros DSS_sw. eapply upd_constr_fail; eauto.  }
        { apply wf_cs_tail in WF_acs.
          specialize (IHcs _ WF_acs UPD f).
          assert (CONJ := conj DSCS DSS_sd).
          apply IHcs in CONJ. destruct CONJ. auto. } }
      { apply wf_cs_tail in WF_acs.
        specialize (IHcs _ WF_acs UPD f).
        apply ds_cs_decompose in DSCS. destruct DSCS as [_ DSCS].
        assert (CONJ := conj DSCS DSS_sd).
        apply IHcs in CONJ. destruct CONJ. auto. } }
    { split; intros [DSCS DSS_sd]; split; auto.
      { apply ds_cs_append.
        { apply wf_cs_head in WF_acs. rename WF_acs into WF. rename a into w.
          intros DSS_sw. specialize (upd_constr_success _ _ _ _ WF UPD_C _ DSS_sd).
          intros EQU. apply ds_cs_decompose in DSCS. destruct DSCS as [NDSS_sdw' _].
          apply NDSS_sdw'. apply EQU. auto. }
        { apply wf_cs_tail in WF_acs.
          specialize (IHcs _ WF_acs UPD f).
          apply ds_cs_decompose in DSCS. destruct DSCS as [_ DSCS].
          assert (CONJ := conj DSCS DSS_sd).
          apply IHcs in CONJ. destruct CONJ. auto. } }
      { rename a into w. assert (WF_cs := WF_acs). apply wf_cs_tail in WF_cs.
        apply wf_cs_head in WF_acs. rename WF_acs into WF.
        specialize (IHcs _ WF_cs UPD f).
        apply ds_cs_decompose in DSCS. destruct DSCS as [DSC DSCS].
        assert (CONJ := conj DSCS DSS_sd).
        apply IHcs in CONJ. destruct CONJ.
        apply ds_cs_append; auto. intros DSS_sdw'.
        specialize (upd_constr_success _ _ _ _ WF UPD_C _ H0). intros EQU.
        apply DSC. apply EQU. auto. } } }
Qed.

End RealisticConstraintStore.


Module OperationalSemRealisticCS := OperationalSemAbstr RealisticConstraintStore.

Module OperationalSemRealisticCSSoundness := OperationalSemSoundnessAbstr RealisticConstraintStore.

Module OperationalSemRealisticCSCompleteness := OperationalSemCompletenessAbstr RealisticConstraintStore.

Import OperationalSemRealisticCS.

Extraction Language Haskell.

Extraction "extracted/realistic_diseq_interpreter.hs" op_sem_exists initial_state.

