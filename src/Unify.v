Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.ListSet.
Require Export Coq.Structures.OrderedTypeEx.

Ltac good_inversion H := inversion H; clear H; subst.

(************************* Terms *************************)
(* Name of entities *)
Definition name := nat.

Definition name_eq_dec : (forall x y : name, {x = y} + {x <> y}) := eq_nat_dec.

(* Term type *) 
Inductive term : Set :=
(* a variable           *) | Var : name -> term
(* a constant           *) | Cst : name -> term
(* a binary constructor *) | Con : name -> term -> term -> term.

Lemma term_eq_dec : forall t1 t2 : term, {t1 = t2} + {t1 <> t2}.
Proof.
  induction t1; destruct t2.
  2, 3, 4, 6, 7, 8: right; intro H; inversion H.
  1, 2: specialize (eq_nat_dec n n0); intro; destruct H;
        [ left; auto
        | right; intro H; inversion H; auto ].
  specialize (eq_nat_dec n n0); intro; destruct H;
  specialize (IHt1_1 t2_1); destruct IHt1_1;
  specialize (IHt1_2 t2_2); destruct IHt1_2.
  1: left; subst; reflexivity.
  all: right; intro H; inversion H; auto.
Qed.

Definition var_set := set name.

Definition var_set_empty : var_set := empty_set name.
Definition var_set_add : name -> var_set -> var_set := set_add name_eq_dec.
Definition var_set_union : var_set -> var_set -> var_set := set_union name_eq_dec.
Definition var_set_remove : name -> var_set -> var_set := set_remove name_eq_dec.
Definition var_set_size : var_set -> nat := @length name.

Fixpoint fv_term (t : term) : var_set :=
  match t with
  | Var n     => var_set_add n var_set_empty
  | Cst _     => var_set_empty
  | Con _ l r => var_set_union (fv_term l) (fv_term r)
  end.

Definition ground_term : Set := {t : term | fv_term t = var_set_empty}.

Lemma fv_term_nodup
      (t : term) :
      NoDup (fv_term t).
Proof.
  induction t.
  { apply set_add_nodup. constructor. }
  { constructor. }
  { apply set_union_nodup; assumption. }
Qed.

Lemma free_var
      (t : term) :
      exists x, ~ In x (fv_term t).
Proof.
  assert (A : forall t, exists n, forall x, In x (fv_term t) -> S x <= n).
  { clear. induction t.
    { exists (S n). intros. destruct H.
      { omega. }
      { contradiction. } }
    { exists 0. intros. contradiction. }
    { destruct IHt1 as [n1 IHt1]. destruct IHt2 as [n2 IHt2].
      exists (max n1 n2). intros. apply (set_union_elim name_eq_dec) in H.
      destruct H.
      { eapply le_trans.
        { eapply IHt1. assumption. }
        { apply Nat.le_max_l. } }
      { eapply le_trans.
        { eapply IHt2. assumption. }
        { apply Nat.le_max_r. } } } }
  specialize (A t). destruct A. exists x. intro C.
  apply H in C. omega.
Qed.

Fixpoint height (t : term) : nat :=
  match t with
  | Var _     => 1
  | Cst _     => 1
  | Con _ l r => S (max (height l) (height r))
  end.

Fixpoint occurs (n : name) (t : term) : bool :=
  match t with
  | Var x     => Nat.eqb n x
  | Cst _     => false
  | Con _ l r => orb (occurs n l) (occurs n r)
  end.

Lemma occurs_In
      (t : term)
      (n : name) :
      occurs n t = true <-> In n (fv_term t).
Proof.
  induction t.
  { split; intro.
    { left. symmetry. apply Nat.eqb_eq. assumption. }
    { destruct H.
      { apply Nat.eqb_eq. symmetry. assumption. }
      { contradiction. } } }
  { split; intro C; inversion C. }
  { split; intro.
    { apply (set_union_intro name_eq_dec).
      apply Bool.orb_true_elim in H. destruct H.
      { left. apply IHt1. assumption. }
      { right. apply IHt2. assumption. } }
    { apply Bool.orb_true_intro.
      apply (set_union_elim name_eq_dec) in H. destruct H.
      { left. apply IHt1. assumption. }
      { right. apply IHt2. assumption. } } }
Qed.

(******************** Substitutions **********************)
(* Substitution *)
Definition subst : Set := list (name * term).

Definition empty_subst : subst := [].

Definition singleton_subst (n : name) (t : term) := [(n, t)].

(* Substitution image *)
Fixpoint image (s : subst) (n : name) : option term :=
  match s with
  | [] => None
  | (m, t) :: tl => if eq_nat_dec m n then Some t else image tl n
  end.

Lemma map_image
      (f : name -> term)
      (v : var_set)
      (x : name)
      (X_IN : In x v) :
      image (map (fun x0 : name => (x0, f x0)) v) x = Some (f x).
Proof.
  induction v.
  { contradiction. }
  { simpl. destruct (Nat.eq_dec a x).
    { subst. auto. }
    { apply IHv. destruct X_IN; auto. contradiction. } }
Qed.

Definition in_subst_dom (s : subst) (x : name) : Prop := exists t, image s x = Some t.

Definition in_subst_vran (s : subst) (y : name) : Prop := exists x t, image s x = Some t /\ In y (fv_term t).

(* Substitution application *)
Fixpoint apply_subst (s : subst) (t : term) : term :=
  match t with
  | Cst _     => t
  | Var n     => match image s n with None => t | Some t' => t' end
  | Con n l r => Con n (apply_subst s l) (apply_subst s r)
  end.

Lemma apply_empty
      (t : term) :
      apply_subst empty_subst t = t.
Proof.
  induction t; try (simpl; congruence); auto.
Qed.

Lemma apply_subst_FV
      (x : name)
      (t : term)
      (s : subst)
      (X_FV : In x (fv_term (apply_subst s t))) :
      In x (fv_term t) \/ in_subst_vran s x.
Proof.
  induction t.
  { simpl in X_FV. destruct (image s n) eqn:eq.
    { right. red. eauto. }
    { left. auto. } }
  { inversion X_FV. }
  { simpl in X_FV. apply (set_union_elim name_eq_dec) in X_FV. destruct X_FV.
    { apply IHt1 in H. destruct H.
      { left. apply (set_union_intro name_eq_dec). left. auto. }
      { right. auto. } }
    { apply IHt2 in H. destruct H.
      { left. apply (set_union_intro name_eq_dec). right. auto. }
      { right. auto. } } }
Qed.

(* Substitution composition *)
Definition compose (s1 s2 : subst) : subst :=
  List.map (fun p => (fst p, apply_subst s2 (snd p))) s1 ++ s2.

Lemma compose_correctness
      (s1 s2 : subst)
      (t : term) :
      apply_subst (compose s1 s2) t = apply_subst s2 (apply_subst s1 t).
Proof.
  induction t.
  { simpl. destruct (image s1 n) eqn:eq.
    { induction s1.
      { inversion eq. }
      { destruct a. simpl in eq. simpl. destruct (Nat.eq_dec n0 n).
        { congruence. }
        { auto. } } }
    { induction s1.
      { reflexivity. }
      { destruct a. simpl in eq. simpl. destruct (Nat.eq_dec n0 n).
        { inversion eq. }
        { auto. } } } }
  { reflexivity. }
  { simpl. congruence. }
Qed.

Lemma compose_dom
      (x : name)
      (s s' : subst)
      (IN_DOM : in_subst_dom (compose s s') x) :
      in_subst_dom s x \/ in_subst_dom s' x.
Proof.
  induction s.
  { right. auto. }
  { red in IN_DOM. destruct IN_DOM. unfold in_subst_dom.
    simpl. destruct a. simpl in H.
    destruct (Nat.eq_dec n x).
    { left. eauto. }
    { apply IHs. red. eauto. } }
Qed.

Lemma compose_vran
      (y : name)
      (s s' : subst)
      (IN_VRAN : in_subst_vran (compose s s') y) :
      in_subst_vran s y \/ in_subst_vran s' y.
Proof.
  destruct IN_VRAN as [x [t [IN_IMAGE IN_FV]]].
  assert (GEN : (exists t0, image s x = Some t0 /\ In y (fv_term t0)) \/ in_subst_vran s' y).
  { induction s.
    { right. red. eauto. }
    { destruct a. simpl in IN_IMAGE. simpl. destruct (Nat.eq_dec n x).
      { inversion IN_IMAGE. subst. apply apply_subst_FV in IN_FV.
        destruct IN_FV; auto. left. exists t0. split; auto. }
      { apply IHs in IN_IMAGE. destruct IN_IMAGE; auto. } } }
  destruct GEN.
  { left. red. eauto. }
  { right. auto. }
Qed.

(* Generality *)
Definition more_general (m s : subst) : Prop :=
  exists (s' : subst), forall (t : term), apply_subst s t = apply_subst s' (apply_subst m t).

(* Unification property *)
Definition unifier (s : subst) (t1 t2 : term) : Prop := apply_subst s t1 = apply_subst s t2.

Inductive unification_step_outcome : Set :=
| NonUnifiable : unification_step_outcome
| Same : unification_step_outcome
| VarSubst : forall (n: name) (t: term), unification_step_outcome.

Definition create (n: name) (t: term) : unification_step_outcome :=
  if occurs n t then NonUnifiable else VarSubst n t.

Lemma inv_create
      (n0 n1 : name)
      (t0 t1 : term)
      (CR : create n0 t0 = VarSubst n1 t1) :
      t0 = t1.
Proof.
  { intros. unfold create in CR. destruct (occurs n0 t0).
    { inversion CR. }
    { inversion CR. reflexivity. } }
Qed.

(* Find a difference in a couple of terms and try to make a unification step *)
Fixpoint unification_step (t1 t2 : term) : unification_step_outcome :=
  match (t1, t2) with
  | (Cst n1      , Cst n2      ) => if eq_nat_dec n1 n2 then Same else NonUnifiable 
  | (Con n1 l1 r1, Con n2 l2 r2) => if eq_nat_dec n1 n2
                                    then
                                      match unification_step l1 l2 with
                                      | NonUnifiable => NonUnifiable
                                      | Same => unification_step r1 r2
                                      | res  => res
                                      end
                                    else NonUnifiable
  | (Var n1      , Var n2      ) => if eq_nat_dec n1 n2 then Same else create n1 t2
  | (Var n1      , _           ) => create n1 t2
  | (_           , Var n2      ) => create n2 t1
  | (_           , _           ) => NonUnifiable
  end.

Definition unification_step_ok t1 t2 n s := unification_step t1 t2 = VarSubst n s.

Lemma unification_step_fv
     (t1 t2 s : term)
     (n m : name)
     (STEP_OK : unification_step_ok t1 t2 n s)
     (M_FV : In m (fv_term s)) :
     In m (fv_term t1) \/ In m (fv_term t2).
Proof.
  revert M_FV STEP_OK. revert t2 m n. induction t1.
  { intros. unfold unification_step_ok in STEP_OK.
    destruct t2; unfold unification_step in STEP_OK.
    { destruct (Nat.eq_dec n n1).
      { inversion STEP_OK. }
      { apply inv_create in STEP_OK; subst. right. assumption. } }
    { apply inv_create in STEP_OK; subst. right. assumption. }
    { apply inv_create in STEP_OK; subst. right. assumption. } }
  { intros. unfold unification_step_ok in STEP_OK.
    destruct t2; unfold unification_step in STEP_OK.
    { apply inv_create in STEP_OK; subst. left. assumption. }
    { destruct (Nat.eq_dec n n1); inversion STEP_OK. }
    { inversion STEP_OK. } }
  { intros. unfold unification_step_ok in STEP_OK.
    destruct t2; unfold unification_step in STEP_OK.
    { apply inv_create in STEP_OK; subst. left. assumption. }
    { inversion STEP_OK. }
    { fold unification_step in STEP_OK. destruct (Nat.eq_dec n n1).
      { destruct (unification_step t1_1 t2_1) eqn:eq.
        { inversion STEP_OK. }
        { unfold unification_step_ok in IHt1_2. apply IHt1_2 with (m := m) in STEP_OK.
          { destruct STEP_OK.
            { left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption. }
            { right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption. } }
          { assumption. } }
        { inversion STEP_OK; subst. unfold unification_step_ok in IHt1_1.
          apply IHt1_1 with (m := m) in eq.
          { destruct eq.
            { left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption. }
            { right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption. } }
          { assumption. } } }
      { inversion STEP_OK. } } }
Qed.

Lemma unification_step_subst_wf
      (t1 t2 s : term)
      (n : name)
      (STEP_OK : unification_step_ok t1 t2 n s) :
      ~ In n (fv_term s).
Proof.
  intros. assert (CR : exists m t, create m t = VarSubst n s).
  { revert STEP_OK. revert t2. induction t1; intros.
    { destruct t2; unfold unification_step_ok in STEP_OK; unfold unification_step in STEP_OK.
      { destruct (Nat.eq_dec n0 n1).
        { inversion STEP_OK. }
        { eexists. eexists. eapply STEP_OK. } }
      { eexists. eexists. eapply STEP_OK. }
      { eexists. eexists. eapply STEP_OK. } }
    { destruct t2; unfold unification_step_ok in STEP_OK; unfold unification_step in STEP_OK.
      { eexists. eexists. eapply STEP_OK. }
      { destruct (Nat.eq_dec n0 n1); inversion STEP_OK. }
      { inversion STEP_OK. } }
    { destruct t2; unfold unification_step_ok in STEP_OK; unfold unification_step in STEP_OK.
      { eexists. eexists. eapply STEP_OK. }
      { inversion STEP_OK. }
      { destruct (Nat.eq_dec n0 n1).
        { fold unification_step in STEP_OK. destruct (unification_step t1_1 t2_1) eqn:eq.
          { inversion STEP_OK. }
          { eapply IHt1_2. unfold unification_step_ok. eapply STEP_OK. }
          { inversion STEP_OK; subst. eapply IHt1_1. unfold unification_step_ok.
            eapply eq. } }
        { inversion STEP_OK. } } } }
  destruct CR as [m [t CR]]. unfold create in CR. destruct (occurs m t) eqn:eq.
  { inversion CR. }
  { good_inversion CR. intros CH. apply occurs_In in CH. rewrite eq in CH.
    inversion CH. }
Qed.

Lemma unification_step_subst_occurs
      (t1 t2 s : term)
      (n : name)
      (STEP_OK : unification_step_ok t1 t2 n s) :
      In n (fv_term t1) \/ In n (fv_term t2).
Proof.
  assert (INV_CR: forall n0 n1 t0 t1, create n0 t0 = VarSubst n1 t1 -> n0 = n1).
  { intros. unfold create in H. destruct (occurs n0 t0).
    { inversion H. }
    { inversion H. reflexivity. } }
  assert (VAR_IN_FV: forall n, In n (fv_term (Var n))).
  { unfold fv_term. unfold In. left. reflexivity. }
  revert STEP_OK. revert n t2. induction t1.
  { intros. unfold unification_step_ok in STEP_OK.
    destruct t2; unfold unification_step in STEP_OK.
    { destruct (Nat.eq_dec n n1).
      { inversion STEP_OK. }
      { apply INV_CR in STEP_OK; subst. left. apply VAR_IN_FV. } }
    { apply INV_CR in STEP_OK; subst. left. apply VAR_IN_FV. }
    { apply INV_CR in STEP_OK; subst. left. apply VAR_IN_FV. } }
  { intros. unfold unification_step_ok in STEP_OK. destruct t2; unfold unification_step in STEP_OK.
    { apply INV_CR in STEP_OK; subst. right. apply VAR_IN_FV. }
    { destruct (Nat.eq_dec n n1); inversion STEP_OK. }
    { inversion STEP_OK. } }
  { intros. unfold unification_step_ok in STEP_OK. destruct t2; unfold unification_step in STEP_OK.
    { apply INV_CR in STEP_OK; subst. right. apply VAR_IN_FV. }
    { inversion STEP_OK. }
    { fold unification_step in STEP_OK. destruct (unification_step t1_1 t2_1) eqn:eq.
      { destruct (Nat.eq_dec n n1); inversion STEP_OK. }
      { destruct (Nat.eq_dec n n1).
        { unfold unification_step_ok in IHt1_2. apply IHt1_2 in STEP_OK. destruct STEP_OK.
          { left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption. }
          { right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption. } }
        { inversion STEP_OK. } }
      { destruct (Nat.eq_dec n n1); inversion STEP_OK; subst.
        unfold unification_step_ok in IHt1_1. apply IHt1_1 in eq. destruct eq.
        { left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption. }
        { right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption. } } } }
Qed.

Lemma unification_step_subst_elims
      (s t : term)
      (n : name)
      (N_FV : In n (fv_term (apply_subst (singleton_subst n s) t))) :
      In n (fv_term s).
Proof.
  revert N_FV. unfold singleton_subst. induction t.
  { unfold apply_subst. unfold image. destruct (Nat.eq_dec n n0).
    { auto. }
    { unfold fv_term. intros. exfalso. inversion N_FV.
      { apply n1. symmetry. assumption. }
      { inversion H. } } }
  { intros. inversion N_FV. }
  { intros. unfold apply_subst in N_FV. fold apply_subst in N_FV.
    unfold fv_term in N_FV. fold fv_term in N_FV.
    apply (set_union_elim name_eq_dec) in N_FV. destruct N_FV; auto. }
Qed.

Lemma lt_size
      (vs1 vs2 : var_set)
      (NO_DUP_1 : NoDup vs1)
      (NO_DUP_2 : NoDup vs2)
      (INCL : incl vs1 vs2)
      (UNIQ_VAR : exists n, In n vs2 /\ ~ (In n vs1)) :
      var_set_size vs1 < var_set_size vs2.
Proof.
  intros. destruct UNIQ_VAR as [n [IN NOT_IN]].
  apply in_split in IN.
  destruct IN as [l1 [l2 EQ]]. subst.
  unfold var_set_size. rewrite app_length. simpl.
  assert (LE_LEN : length vs1 <= length (l1 ++ l2)).
  { apply NoDup_incl_length.
    { assumption. }
    { unfold incl. intros. assert (H_COPY := H).
      apply INCL in H. apply in_app_or in H. destruct H.
      { apply in_or_app. left. auto. }
      { inversion H.
        { exfalso. subst. auto. }
        { apply in_or_app. right. auto. } } } }
  rewrite app_length in LE_LEN. omega.
Qed.

Lemma unification_step_decreases_fv
      (t1 t2 s : term)
      (n : name)
      (STEP_OK : unification_step_ok t1 t2 n s) :
      var_set_size (var_set_union (fv_term (apply_subst (singleton_subst n s) t1)) (fv_term (apply_subst (singleton_subst n s) t2))) <
      var_set_size (var_set_union (fv_term t1) (fv_term t2)).
Proof.
  apply lt_size; try apply union_NoDup.
  { apply set_union_nodup; apply fv_term_nodup. }
  { apply set_union_nodup; apply fv_term_nodup. }
  { intros n0 InH. apply (set_union_elim name_eq_dec) in InH. inversion_clear InH.
    { apply apply_subst_FV in H. inversion_clear H.
      { apply (set_union_intro name_eq_dec). left. assumption. }
      { apply unification_step_fv with (m:=n0) in STEP_OK.
        { apply (set_union_intro name_eq_dec). assumption. }
        red in H0. destruct H0 as [x [t [xImage inFV]]]. simpl in xImage.
        destruct (Nat.eq_dec n x); good_inversion xImage. auto. } }
    { apply apply_subst_FV in H. inversion_clear H.
      { apply (set_union_intro name_eq_dec). right. assumption. }
      { apply unification_step_fv with (m:=n0) in STEP_OK.
        { apply (set_union_intro name_eq_dec). assumption. }
        red in H0. destruct H0 as [x [t [xImage inFV]]]. simpl in xImage.
        destruct (Nat.eq_dec n x); good_inversion xImage. auto. } } }
  { exists n. split.
    { apply unification_step_subst_occurs in STEP_OK. apply (set_union_intro name_eq_dec). assumption. }
    { unfold not. intro H. apply (set_union_elim name_eq_dec) in H. inversion_clear H as [H0 | H0];
      apply unification_step_subst_elims in H0;
      apply unification_step_subst_wf in STEP_OK; auto. } }
Qed.



Definition terms := (term * term)%type.

Definition fvOrder (t : terms) := length (var_set_union (fv_term (fst t)) (fv_term (snd t))).

Definition fvOrderRel (t p : terms) := fvOrder t < fvOrder p.

(* Hint Constructors Acc. *)

Theorem fvOrder_wf : well_founded fvOrderRel.
Proof.
  assert (fvOrder_wf': forall (size: nat) (t: terms), fvOrder t < size -> Acc fvOrderRel t).
  { unfold fvOrderRel. induction size.
    { intros. inversion H. }
    { intros. constructor. intros. apply IHsize. omega. } }
  red; intro; eapply fvOrder_wf'; eauto.
Defined.

Inductive mgu : term -> term -> option subst -> Set :=
| mguNonUnifiable : forall t1 t2 (STEP_NU : unification_step t1 t2 = NonUnifiable),
                                 mgu t1 t2 None
| mguSame :         forall t1 t2 (STEP_SAME : unification_step t1 t2 = Same),
                                 mgu t1 t2 (Some empty_subst)
| mguVarSubstNone : forall t1 t2 n s
                           (STEP_SUBST : unification_step t1 t2 = VarSubst n s)
                           (THEN_FAIL : mgu (apply_subst (singleton_subst n s) t1) (apply_subst (singleton_subst n s) t2) None),
                           mgu t1 t2 None
| mguVarSubstSome : forall t1 t2 n s r sr
                           (STEP_SUBST : unification_step t1 t2 = VarSubst n s)
                           (THEN_SUCC : mgu (apply_subst (singleton_subst n s) t1) (apply_subst (singleton_subst n s) t2) (Some r))
                           (SR_EQ : sr = compose (singleton_subst n s) r),
                           mgu t1 t2 (Some sr).

Example test1: mgu (Cst 1) (Cst 2) None.
Proof. repeat econstructor. Qed.

Example test2: mgu (Cst 1) (Cst 1) (Some []).
Proof. repeat econstructor. Qed.

Example test3: mgu (Var 1) (Var 2) (Some [(1, Var 2)]).
Proof. repeat econstructor. Qed.

Example test4: mgu (Var 1) (Var 1) (Some []).
Proof. repeat econstructor. Qed.

Example test5: mgu (Con 1 (Var 1) (Var 2)) (Con 2 (Var 1) (Var 2)) None.
Proof. repeat econstructor. Qed.

Example test6: mgu (Con 1 (Var 1) (Var 2)) (Con 1 (Var 1) (Var 2)) (Some []).
Proof. repeat econstructor. Qed.

Example test7: mgu (Con 1 (Var 1) (Var 1)) (Con 1 (Var 1) (Var 2)) (Some [(1, Var 2)]).
Proof. repeat econstructor. Qed.

Example test8: mgu (Con 1 (Cst 1) (Var 2)) (Con 1 (Var 1) (Cst 2)) (Some [(1, Cst 1); (2, Cst 2)]).
Proof.
  econstructor.
  1, 3: econstructor.
  repeat econstructor.
Qed.



Lemma mgu_exists
      (t1 t2 : term) :
      {r & mgu t1 t2 r}.
Proof.
  remember (fun p => {r : option subst & mgu (fst p) (snd p) r}) as P.
  assert (P (t1, t2)).
  { apply well_founded_induction with (R := fvOrderRel).
    { apply fvOrder_wf. }
    { intros. subst. clear t1 t2. destruct x as [t1 t2]. simpl.
      destruct (unification_step t1 t2) eqn:eq.
      { exists None. constructor. assumption. }
      { exists (Some empty_subst). constructor. assumption. }
      { specialize (H (apply_subst (singleton_subst n t) t1, apply_subst (singleton_subst n t) t2)).
        assert (fvOr : fvOrderRel (apply_subst (singleton_subst n t) t1, apply_subst (singleton_subst n t) t2) (t1, t2)).
        { apply unification_step_decreases_fv. assumption. }
        specialize (H fvOr). destruct H. destruct x.
        { eexists. eapply mguVarSubstSome.
          { eassumption. }
          { eassumption. }
          { reflexivity. } }
        { exists None. eapply mguVarSubstNone.
          { eassumption. }
          { eassumption. } } } } }
  subst. assumption.
Qed.

Lemma mgu_unique
      (t1 t2 : term)
      (r r' : option subst)
      (UNI_1 : mgu t1 t2 r)
      (UNI_2 : mgu t1 t2 r') :
      r = r'.
Proof.
  revert UNI_2. revert r'. induction UNI_1.
  { intros. good_inversion UNI_2; try reflexivity; congruence. }
  { intros. good_inversion UNI_2; try reflexivity; congruence. }
  { intros. good_inversion UNI_2; try reflexivity; try congruence.
    rewrite STEP_SUBST0 in STEP_SUBST. good_inversion STEP_SUBST.
    apply IHUNI_1 in THEN_SUCC. inversion THEN_SUCC. }
  { intros. good_inversion UNI_2; try congruence;
    rewrite STEP_SUBST0 in STEP_SUBST; good_inversion STEP_SUBST.
    { apply IHUNI_1 in THEN_FAIL; inversion THEN_FAIL. }
    { apply IHUNI_1 in THEN_SUCC; inversion THEN_SUCC; auto. } }
Qed.

Lemma same_step_equal_terms
      (t1 t2 : term)
      (STEP_SAME : unification_step t1 t2 = Same) :
      t1 = t2.
Proof.
  assert (CREATE_NOT_SAME : forall n t, create n t <> Same).
  { unfold create. intros n t C. destruct (occurs n t); inversion C. }
  revert STEP_SAME. revert t2. induction t1; induction t2; intros; good_inversion STEP_SAME.
  { destruct (Nat.eq_dec n n0).
    { congruence. }
    { apply CREATE_NOT_SAME in H0. contradiction. } }
  { apply CREATE_NOT_SAME in H0. contradiction. }
  { destruct (Nat.eq_dec n n0).
    { congruence. }
    { inversion H0. } }
  { apply CREATE_NOT_SAME in H0. contradiction. }
  { destruct (Nat.eq_dec n n0).
    { subst. destruct (unification_step t1_1 t2_1) eqn:eq; inversion H0.
      apply IHt1_1 in eq. apply IHt1_2 in H0. congruence. }
    { inversion H0. } }
Qed.

Lemma mgu_unifies
      (t1 t2 : term)
      (s : subst)
      (UNI : mgu t1 t2 (Some s)) :
      unifier s t1 t2.
Proof.
  revert UNI. revert s.
  remember (fun p => forall s : subst,
      mgu (fst p) (snd p) (Some s) -> unifier s (fst p) (snd p)).
  assert (P (t1, t2)).
  { apply well_founded_induction with (R := fvOrderRel).
    { apply fvOrder_wf. }
    { intros. subst. clear t1 t2. destruct x as [t1 t2]. simpl.
      intros. inversion H0; subst; clear H0.
      { unfold unifier. rewrite apply_empty. rewrite apply_empty.
        apply same_step_equal_terms. assumption. }
      { assert (fvOr : fvOrderRel (apply_subst (singleton_subst n s0) t1, apply_subst (singleton_subst n s0) t2) (t1, t2)).
        { apply unification_step_decreases_fv. assumption. }
        eapply H in fvOr.
        2: { eassumption. }
        { unfold unifier. rewrite compose_correctness. rewrite compose_correctness.
          assumption. } } } }
  subst. assumption.
Qed.

Lemma unification_step_binds
      (t1 t2 t : term)
      (x : name)
      (s : subst)
      (STEP : unification_step t1 t2 = VarSubst x t)
      (S_UNIFIER : unifier s t1 t2) :
      apply_subst s (Var x) = apply_subst s t.
Proof.
  revert S_UNIFIER STEP. revert s x t t2.
  induction t1; induction t2; intros; simpl in STEP.
  { destruct (Nat.eq_dec n n0).
    { inversion STEP. }
    { unfold create in STEP. destruct (occurs n (Var n0)); inversion STEP.
      subst. assumption. } }
  { unfold create in STEP. destruct (occurs n (Cst n0)); inversion STEP. subst. assumption. }
  { unfold create in STEP. destruct (occurs n (Con n0 t2_1 t2_2)); inversion STEP. subst. assumption. }
  { unfold create in STEP. destruct (occurs n0 (Cst n)); inversion STEP. subst. symmetry. assumption. }
  { destruct (Nat.eq_dec n n0); inversion STEP. }
  { inversion STEP. }
  { unfold create in STEP. destruct (occurs n0 (Con n t1_1 t1_2)); inversion STEP. subst. symmetry. assumption. }
  { inversion STEP. }
  { clear IHt2_1. clear IHt2_2.
    destruct (Nat.eq_dec n n0).
    { subst. destruct (unification_step t1_1 t2_1) eqn:eq.
      { inversion STEP. }
      { inversion S_UNIFIER. apply IHt1_2 with t2_2; assumption. }
      { inversion STEP. subst. inversion S_UNIFIER. apply IHt1_1 with t2_1; assumption. } }
    { inversion STEP. } }
Qed.

Lemma unification_step_binds_2
      (t1 t2 t : term)
      (x : name)
      (s : subst)
      (STEP : unification_step t1 t2 = VarSubst x t)
      (S_UNIFIER : unifier s t1 t2)
      (t' : term) :
      apply_subst s t' = apply_subst s (apply_subst (singleton_subst x t) t').
Proof.
  specialize (unification_step_binds _ _ _ _ _ STEP S_UNIFIER). intro APP_EQ.
  induction t'.
  { simpl. destruct (Nat.eq_dec x n).
    { subst. rewrite <- APP_EQ. reflexivity. }
    { reflexivity. } }
  { reflexivity. }
  { simpl. rewrite IHt'1. rewrite IHt'2. reflexivity. }
Qed.

Lemma mgu_most_general
      (t1 t2 : term)
      (m s : subst)
      (UNI : mgu t1 t2 (Some m))
      (S_UNIFIER : unifier s t1 t2) :
      more_general m s.
Proof.
  revert S_UNIFIER. revert s.
  remember (Some m) as r eqn:eq.
  revert eq. revert m.
  induction UNI; intros m eq; good_inversion eq.
  { intros. unfold more_general. exists s. intros.
    rewrite apply_empty. reflexivity. }
  { subst. specialize (IHUNI r eq_refl).
    rename s into st. intros.
    specialize (unification_step_binds_2 _ _ _ _ _ STEP_SUBST S_UNIFIER). intro APP_EQ.
    assert (MG : more_general r s).
    { apply IHUNI. unfold unifier. congruence. }
    unfold more_general in MG. destruct MG as [d MG]. unfold more_general.
    exists d. intro. rewrite compose_correctness. congruence. }
Qed.

Lemma occurs_subst_height
      (s : subst)
      (n : name)
      (t : term)
      (OCC : occurs n t = true) :
      height (apply_subst s (Var n)) <= height (apply_subst s t).
Proof.
  induction t.
  { simpl in OCC. apply Nat.eqb_eq in OCC. subst. reflexivity. }
  { inversion OCC. }
  { simpl in OCC. apply Bool.orb_true_elim in OCC. destruct OCC.
    { apply IHt1 in e. simpl. apply le_S. eapply le_trans.
      eassumption. apply Nat.le_max_l. }
    { apply IHt2 in e. simpl. apply le_S. eapply le_trans.
      eassumption. apply Nat.le_max_r. } }
Qed.

Lemma occurs_check_ground
      (s : subst)
      (x : name)
      (t : term)
      (OCC : occurs x t = true)
      (APP_EQ : apply_subst s (Var x) = apply_subst s t) :
      Var x = t.
Proof.
  destruct t.
  { simpl in OCC. apply beq_nat_true_iff in OCC. congruence. }
  { inversion OCC. }
  { exfalso. simpl in OCC. apply Bool.orb_true_elim in OCC. destruct OCC.
    { apply occurs_subst_height with (s := s) in e. rewrite APP_EQ in e.
      simpl in e. apply le_lt_n_Sm in e. apply lt_S_n in e.
      apply lt_irrefl with (height (apply_subst s t1)).
      eapply le_lt_trans.
      2: { eapply e. }
      apply Nat.le_max_l. }
    { apply occurs_subst_height with (s := s) in e. rewrite APP_EQ in e.
      simpl in e. apply le_lt_n_Sm in e. apply lt_S_n in e.
      apply lt_irrefl with (height (apply_subst s t2)).
      eapply le_lt_trans.
      2: { eapply e. }
      apply Nat.le_max_r. } }
Qed.

Lemma mgu_non_unifiable
      (t1 t2 : term)
      (UNI : mgu t1 t2 None)
      (s : subst) :
      ~ (unifier s t1 t2).
Proof.
  revert s. remember None as r eqn:eq.
  induction UNI; good_inversion eq.
  { revert STEP_NU. revert t2.
    induction t1; induction t2; intros H s; inversion H.
    { destruct (Nat.eq_dec n n0).
      { inversion H1. }
      { unfold create in H1. destruct (occurs n (Var n0)) eqn:eq; inversion H1.
        intro C. specialize (occurs_check_ground _ _ _ eq C). intro.
        inversion H0. contradiction. } }
    { unfold create in H1. destruct (occurs n (Con n0 t2_1 t2_2)) eqn:eq; inversion H1.
      intro C. specialize (occurs_check_ground _ _ _ eq C). intro.
      inversion H0. }
    { destruct (Nat.eq_dec n n0).
      { inversion H1. }
      { intro C. inversion C. contradiction. } }
    { intro C. inversion C. }
    { unfold create in H1. destruct (occurs n0 (Con n t1_1 t1_2)) eqn:eq; inversion H1.
      intro C. red in C. symmetry in C.
      specialize (occurs_check_ground _ _ _ eq C).
      intro. inversion H0. }
    { intro C. inversion C. }
    { clear IHt2_1 IHt2_2. intro C. inversion C. destruct (Nat.eq_dec n n0).
      { subst. destruct (unification_step t1_1 t2_1) eqn:eq.
        { eapply IHt1_1; eassumption. }
        { eapply IHt1_2; eassumption. }
        { inversion H1. } }
      { contradiction. } } }
  { rename s into st. intros s C.
    specialize (IHUNI eq_refl s).
    specialize (unification_step_binds_2 _ _ _ _ _ STEP_SUBST C). intros eq.
    apply IHUNI. red. rewrite <- eq. rewrite <- eq. assumption. }
Qed.

Lemma mgu_dom
      (t1 t2 : term)
      (s : subst)
      (MGU : mgu t1 t2 (Some s))
      (x : name)
      (inDom : in_subst_dom s x) :
      In x (fv_term t1) \/ In x (fv_term t2).
Proof.
  remember (Some s) as r eqn:eq. revert eq inDom. revert s.
  induction MGU; intros; good_inversion eq.
  { destruct inDom. inversion H. }
  { apply compose_dom in inDom. destruct inDom.
    { red in H. destruct H. simpl in H.
      destruct (Nat.eq_dec n x); good_inversion H.
      eapply unification_step_subst_occurs; eauto. }
     { specialize (IHMGU _ eq_refl H). destruct IHMGU.
       { apply apply_subst_FV in H0. destruct H0.
         { left. auto. }
         { red in H0. destruct H0 as [x0 [t [x0Image inFV]]]. simpl in x0Image.
           destruct (Nat.eq_dec n x0); good_inversion x0Image.
           eapply unification_step_fv; eauto. } }
        { apply apply_subst_FV in H0. destruct H0.
         { right. auto. }
         { red in H0. destruct H0 as [x0 [t [x0Image inFV]]]. simpl in x0Image.
           destruct (Nat.eq_dec n x0); good_inversion x0Image.
           eapply unification_step_fv; eauto. } } } }
Qed.

Lemma mgu_vran
      (t1 t2 : term)
      (s : subst)
      (MGU : mgu t1 t2 (Some s))
      (x : name)
      (inVRan : in_subst_vran s x) :
      In x (fv_term t1) \/ In x (fv_term t2).
Proof.
  remember (Some s) as r eqn:eq. revert eq inVRan. revert s.
  induction MGU; intros; good_inversion eq.
  { destruct inVRan. destruct H as [t [x0Image inFV]]. inversion x0Image. }
  { apply compose_vran in inVRan. destruct inVRan.
    { red in H. destruct H as [x0 [t [x0Image inFV]]]. simpl in x0Image.
      destruct (Nat.eq_dec n x0); good_inversion x0Image.
      eapply unification_step_fv; eauto. }
     { specialize (IHMGU _ eq_refl H). destruct IHMGU.
       { apply apply_subst_FV in H0. destruct H0.
         { left. auto. }
         { red in H0. destruct H0 as [x0 [t [x0Image inFV]]]. simpl in x0Image.
           destruct (Nat.eq_dec n x0); good_inversion x0Image.
           eapply unification_step_fv; eauto. } }
        { apply apply_subst_FV in H0. destruct H0.
         { right. auto. }
         { red in H0. destruct H0 as [x0 [t [x0Image inFV]]]. simpl in x0Image.
           destruct (Nat.eq_dec n x0); good_inversion x0Image.
           eapply unification_step_fv; eauto. } } } }
Qed.
