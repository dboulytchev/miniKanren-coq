Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.ListSet.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Eqdep.
Require Import Program.

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

Lemma term_eq_dec : (forall t1 t2 : term, {t1 = t2} + {t1 <> t2}).
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

Lemma fv_term_nodup : forall t, NoDup (fv_term t).
Proof.
  induction t.
  * apply set_add_nodup. constructor.
  * constructor.
  * apply set_union_nodup; assumption.
Qed.

Definition fv_terms (ts : list term) : var_set :=
  fold_left (fun acc t => var_set_union acc (fv_term t)) ts var_set_empty.

Lemma free_var (t : term) : exists x, ~ In x (fv_term t).
Proof.
  assert (A : forall t, exists n, forall x, In x (fv_term t) -> S x <= n).
  {
    clear. induction t.
    * exists (S n). intros. destruct H.
      + omega.
      + contradiction.
    * exists 0. intros. contradiction.
    * destruct IHt1 as [n1 IHt1]. destruct IHt2 as [n2 IHt2].
      exists (max n1 n2). intros. apply (set_union_elim name_eq_dec) in H.
      destruct H.
      + eapply le_trans.
        - eapply IHt1. assumption.
        - apply Nat.le_max_l.
      + eapply le_trans.
        - eapply IHt2. assumption.
        - apply Nat.le_max_r.
  }
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

Lemma occurs_In: forall t n, occurs n t = true <-> In n (fv_term t).
Proof.
  intros. induction t.
  * split; intro.
    + left. symmetry. apply Nat.eqb_eq. assumption.
    + destruct H.
      - apply Nat.eqb_eq. symmetry. assumption.
      - contradiction.
  * split; intro C; inversion C.
  * split; intro.
    + apply (set_union_intro name_eq_dec).
      apply Bool.orb_true_elim in H. destruct H.
      - left. apply IHt1. assumption.
      - right. apply IHt2. assumption.
    + apply Bool.orb_true_intro.
      apply (set_union_elim name_eq_dec) in H. destruct H.
      - left. apply IHt1. assumption.
      - right. apply IHt2. assumption.
Qed.

(******************** Substitutions **********************)
(* Substitution *)
Definition subst : Set := list (name * term).

Definition empty_subst : subst := [].

Definition singleton_subst (n : name) (t : term) := [(n, t)].

(* Substitution domain *)
(* Definition domain (s : subst) : list name := nodup name_eq_dec (map (@fst name term) s). *)

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
      (HIn : In x v) :
      image (map (fun x0 : name => (x0, f x0)) v) x = Some (f x).
Proof.
  induction v.
  { contradiction. }
  { simpl. destruct (Nat.eq_dec a x).
    { subst. auto. }
    { apply IHv. destruct HIn; auto. contradiction. } }
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

Lemma apply_empty: forall (t : term), apply_subst empty_subst t = t.
Proof.
  induction t; try (simpl; congruence); auto.
Qed.

Lemma apply_subst_FV
      (x : name)
      (t : term)
      (s : subst)
      (xFV : In x (fv_term (apply_subst s t))) :
      In x (fv_term t) \/ in_subst_vran s x.
Proof.
  induction t.
  { simpl in xFV. destruct (image s n) eqn:eq.
    { right. red. eauto. }
    { left. auto. } }
  { inversion xFV. }
  { simpl in xFV. apply (set_union_elim name_eq_dec) in xFV. destruct xFV.
    { apply IHt1 in H. destruct H.
      { left. apply (set_union_intro name_eq_dec). left. auto. }
      { right. auto. } }
    { apply IHt2 in H. destruct H.
      { left. apply (set_union_intro name_eq_dec). right. auto. }
      { right. auto. } } }
Qed.

(* Composition *)
Definition compose (s1 s2 : subst) : subst :=
  List.map (fun p => (fst p, apply_subst s2 (snd p))) s1 ++ s2.

Lemma compose_correctness: forall (s1 s2 : subst) (t : term),
  apply_subst (compose s1 s2) t = apply_subst s2 (apply_subst s1 t).
Proof.
  intros. induction t.
  * simpl. destruct (image s1 n) eqn:eq.
    + induction s1.
      - inversion eq.
      - destruct a. simpl in eq. simpl. destruct (Nat.eq_dec n0 n).
        { congruence. }
        { auto. }
    + induction s1.
      - reflexivity.
      - destruct a. simpl in eq. simpl. destruct (Nat.eq_dec n0 n).
        { inversion eq. }
        { auto. }
  * reflexivity.
  * simpl. congruence.
Qed.

Lemma compose_dom
      (x : name)
      (s s' : subst)
      (inDom : in_subst_dom (compose s s') x) :
      in_subst_dom s x \/ in_subst_dom s' x.
Proof.
  induction s.
  { right. auto. }
  { red in inDom. destruct inDom. unfold in_subst_dom.
    simpl. destruct a. simpl in H.
    destruct (Nat.eq_dec n x).
    { left. eauto. }
    { apply IHs. red. eauto. } }
Qed.

Lemma compose_vran
      (y : name)
      (s s' : subst)
      (inVRan : in_subst_vran (compose s s') y) :
      in_subst_vran s y \/ in_subst_vran s' y.
Proof.
  destruct inVRan as [x [t [inImage inFV]]].
  assert (GenLemma : (exists t0, image s x = Some t0 /\ In y (fv_term t0)) \/ in_subst_vran s' y).
  { induction s.
    { right. red. eauto. }
    { destruct a. simpl in inImage. simpl. destruct (Nat.eq_dec n x).
      { inversion inImage. subst. apply apply_subst_FV in inFV.
        destruct inFV; auto. left. exists t0. split; auto. }
      { apply IHs in inImage. destruct inImage; auto. } } }
  destruct GenLemma.
  { left. red. eauto. }
  { right. auto. }
Qed.

(* Generality *)
Definition more_general (m s : subst) : Prop :=
  exists (s' : subst), forall (t : term), apply_subst s t = apply_subst s' (apply_subst m t).

(* Unification property *)
Definition unifier (s : subst) (t1 t2 : term) : Prop := apply_subst s t1 = apply_subst s t2.

(* MGU *)
(* Definition mgu (m : subst) (t1 t2 : term) : Prop :=
  unifier m t1 t2 /\ forall (s : subst), unifier s t1 t2 -> more_general m s.
*)

Inductive unification_step_outcome : Set :=
| Fail : unification_step_outcome
| Fine : unification_step_outcome
| Subst : forall (n: name) (t: term), unification_step_outcome.

Definition create (n: name) (t: term) : unification_step_outcome :=
  if occurs n t then Fail else Subst n t.

(* Find a difference in a couple of terms and try to make a unification step *)
Fixpoint unification_step (t1 t2 : term) : unification_step_outcome :=
  match (t1, t2) with
  | (Cst n1      , Cst n2      ) => if eq_nat_dec n1 n2 then Fine else Fail 
  | (Con n1 l1 r1, Con n2 l2 r2) => if eq_nat_dec n1 n2
                                    then
                                      match unification_step l1 l2 with
                                      | Fail => Fail
                                      | Fine => unification_step r1 r2
                                      | res  => res
                                      end
                                    else Fail
  | (Var n1      , Var n2      ) => if eq_nat_dec n1 n2 then Fine else create n1 t2
  | (Var n1      , _           ) => create n1 t2
  | (_           , Var n2      ) => create n2 t1
  | (_           , _           ) => Fail
  end.

Definition unification_step_ok t1 t2 n s := unification_step t1 t2 = Subst n s.

Lemma unification_step_fv: forall t1 t2 s n ,
    unification_step_ok t1 t2 n s -> (forall m, In m (fv_term s) -> In m (fv_term t1) \/ In m (fv_term t2)).
Proof.
  assert (invCr: forall n0 n1 t0 t1, create n0 t0 = Subst n1 t1 -> t0 = t1).
  { intros. unfold create in H. destruct (occurs n0 t0).
    - inversion H.
    - inversion H. reflexivity. }
  induction t1.
  * intros. unfold unification_step_ok in H. destruct t2; unfold unification_step in H.
    + destruct (Nat.eq_dec n n1).
      - inversion H.
      - apply invCr in H; subst. right. assumption.
    + apply invCr in H; subst. right. assumption.
    + apply invCr in H; subst. right. assumption.
  * intros. unfold unification_step_ok in H. destruct t2; unfold unification_step in H.
    + apply invCr in H; subst. left. assumption.
    + destruct (Nat.eq_dec n n1); inversion H.
    + inversion H.
  * intros. unfold unification_step_ok in H. destruct t2; unfold unification_step in H.
    + apply invCr in H; subst. left. assumption.
    + inversion H.
    + fold unification_step in H. destruct (Nat.eq_dec n n1).
      - destruct (unification_step t1_1 t2_1) eqn:eq.
        { inversion H. }
        { unfold unification_step_ok in IHt1_2. apply IHt1_2 with (m := m) in H.
          - destruct H.
            + left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption.
            + right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption.
          - assumption. }
        { inversion H; subst. unfold unification_step_ok in IHt1_1.
          apply IHt1_1 with (m := m) in eq.
          - destruct eq.
            + left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption.
            + right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption.
          - assumption. }
      - inversion H.
Qed.

Lemma unification_step_subst_wf:
  forall t1 t2 s n, unification_step_ok t1 t2 n s -> ~ In n (fv_term s).
Proof.
  intros. assert (exists m t, create m t = Subst n s).
  {
    generalize dependent t2. induction t1; intros.
    * destruct t2; unfold unification_step_ok in H; unfold unification_step in H.
      + destruct (Nat.eq_dec n0 n1).
         - inversion H.
         - eexists. eexists. eapply H.
      + eexists. eexists. eapply H.
      + eexists. eexists. eapply H.
    * destruct t2; unfold unification_step_ok in H; unfold unification_step in H.
      + eexists. eexists. eapply H.
      + destruct (Nat.eq_dec n0 n1); inversion H.
      + inversion H.
    * destruct t2; unfold unification_step_ok in H; unfold unification_step in H.
      + eexists. eexists. eapply H.
      + inversion H.
      + destruct (Nat.eq_dec n0 n1).
        - fold unification_step in H. destruct (unification_step t1_1 t2_1) eqn:eq.
          { inversion H. }
          { eapply IHt1_2. unfold unification_step_ok. eapply H. }
          { inversion H; subst. eapply IHt1_1. unfold unification_step_ok.
            eapply eq. }
        - inversion H.
  }
  destruct H0. destruct H0. unfold create in H0. destruct (occurs x x0) eqn:eq.
  - inversion H0.
  - inversion H0; subst. intros CH. apply occurs_In in CH. rewrite eq in CH.
    inversion CH.
Qed.

Lemma unification_step_subst_occurs:
  forall t1 t2 s n, unification_step_ok t1 t2 n s -> In n (fv_term t1) \/ In n (fv_term t2).
Proof.
  assert (invCr: forall n0 n1 t0 t1, create n0 t0 = Subst n1 t1 -> n0 = n1).
  { intros. unfold create in H. destruct (occurs n0 t0).
    - inversion H.
    - inversion H. reflexivity. }
  assert (fvInFv: forall n, In n (fv_term (Var n))).
  { unfold fv_term. unfold In. left. reflexivity. }
  induction t1.
  * intros. unfold unification_step_ok in H. destruct t2; unfold unification_step in H.
    + destruct (Nat.eq_dec n n1).
      - inversion H.
      - apply invCr in H; subst. left. apply fvInFv.
    + apply invCr in H; subst. left. apply fvInFv.
    + apply invCr in H; subst. left. apply fvInFv.
  * intros. unfold unification_step_ok in H. destruct t2; unfold unification_step in H.
    + apply invCr in H; subst. right. apply fvInFv.
    + destruct (Nat.eq_dec n n1); inversion H.
    + inversion H.
  * intros. unfold unification_step_ok in H. destruct t2; unfold unification_step in H.
    + apply invCr in H; subst. right. apply fvInFv.
    + inversion H.
    + fold unification_step in H. destruct (unification_step t1_1 t2_1) eqn:eq.
      - destruct (Nat.eq_dec n n1); inversion H.
      - destruct (Nat.eq_dec n n1).
        { unfold unification_step_ok in IHt1_2. apply IHt1_2 in H. destruct H.
          * left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption.
          * right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). right. assumption. }
        inversion H.
      - destruct (Nat.eq_dec n n1); inversion H; subst.
        unfold unification_step_ok in IHt1_1. apply IHt1_1 in eq. destruct eq.
        { left. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption. }
        right. unfold fv_term. fold fv_term. apply (set_union_intro name_eq_dec). left. assumption.
Qed.

Lemma unification_step_subst_elims: forall s t n, In n (fv_term (apply_subst (singleton_subst n s) t)) -> In n (fv_term s).
Proof.
  intros s t n. unfold singleton_subst. induction t.
  * unfold apply_subst. unfold image. destruct (Nat.eq_dec n n0).
    + auto.
    + unfold fv_term. intros. exfalso. inversion H.
      - apply n1. symmetry. assumption.
      - inversion H0.
  * intros. inversion H.
  * intros. unfold apply_subst in H. fold apply_subst in H. unfold fv_term in H. fold fv_term in H.
    apply (set_union_elim name_eq_dec) in H. destruct H; auto.
Qed.

Lemma lt_size:
  forall (vs1 vs2 : var_set),
    NoDup vs1 -> NoDup vs2 -> incl vs1 vs2 -> (exists n, In n vs2 /\ ~ (In n vs1)) -> var_set_size vs1 < var_set_size vs2.
Proof.
  intros. destruct H2. destruct H2. apply in_split in H2.
  destruct H2. destruct H2. subst.
  unfold var_set_size. rewrite app_length. simpl.
  assert (length vs1 <= length (x0 ++ x1)).
  { apply NoDup_incl_length.
    * assumption.
    * unfold incl. intros. assert (H2_copy := H2).
      apply H1 in H2. apply in_app_or in H2. destruct H2.
      + apply in_or_app. left. assumption.
      + inversion H2.
        - exfalso. apply H3. congruence.
        - apply in_or_app. right. assumption. }
  rewrite app_length in H2. omega.
Qed.

Lemma unification_step_decreases_fv:
  forall t1 t2 s n,
    unification_step_ok t1 t2 n s ->
    var_set_size (var_set_union (fv_term (apply_subst (singleton_subst n s) t1)) (fv_term (apply_subst [(n, s)] t2))) < var_set_size (var_set_union (fv_term t1) (fv_term t2)).
Proof.
  intros t1 t2 s n USok.
  apply lt_size; try apply union_NoDup.
  * apply set_union_nodup; apply fv_term_nodup.
  * apply set_union_nodup; apply fv_term_nodup.
  * intros n0 InH. apply (set_union_elim name_eq_dec) in InH. inversion_clear InH.
    + apply apply_subst_FV in H. inversion_clear H.
      - apply (set_union_intro name_eq_dec). left. assumption.
      - apply unification_step_fv with (m:=n0) in USok.
        { apply (set_union_intro name_eq_dec). assumption. }
        red in H0. destruct H0 as [x [t [xImage inFV]]]. simpl in xImage.
        destruct (Nat.eq_dec n x); good_inversion xImage. auto.
    + apply apply_subst_FV in H. inversion_clear H.
      - apply (set_union_intro name_eq_dec). right. assumption.
      - apply unification_step_fv with (m:=n0) in USok.
        { apply (set_union_intro name_eq_dec). assumption. }
        red in H0. destruct H0 as [x [t [xImage inFV]]]. simpl in xImage.
        destruct (Nat.eq_dec n x); good_inversion xImage. auto.
  * exists n. split.
    + apply unification_step_subst_occurs in USok. apply (set_union_intro name_eq_dec). assumption.
    + unfold not. intro H. apply (set_union_elim name_eq_dec) in H. inversion_clear H as [H0 | H0];
      apply unification_step_subst_elims in H0;
      apply unification_step_subst_wf in USok; auto.
Qed.

Definition terms := (term * term)%type.

Definition fvOrder (t : terms) := length (var_set_union (fv_term (fst t)) (fv_term (snd t))).

Definition fvOrderRel (t p : terms) := fvOrder t < fvOrder p.

Hint Constructors Acc.

Theorem fvOrder_wf: well_founded fvOrderRel.
Proof.
  assert (fvOrder_wf': forall (size: nat) (t: terms), fvOrder t < size -> Acc fvOrderRel t).
    {unfold fvOrderRel. induction size.
     * intros. inversion H.
     * intros. constructor. intros. apply IHsize. omega.
    }
  red; intro; eapply fvOrder_wf'; eauto.
Defined.

Inductive unify : term -> term -> option subst -> Set :=
| unify_Fail : forall t1 t2, unification_step t1 t2 = Fail -> unify t1 t2 None
| unify_Fine : forall t1 t2, unification_step t1 t2 = Fine -> unify t1 t2 (Some empty_subst)
| unify_SubstNone : forall t1 t2 n s, unification_step t1 t2 = Subst n s ->
                                      unify (apply_subst (singleton_subst n s) t1) (apply_subst (singleton_subst n s) t2) None ->
                                      unify t1 t2 None
| unify_SubstSome : forall t1 t2 n s r sr, unification_step t1 t2 = Subst n s ->
                                           unify (apply_subst (singleton_subst n s) t1) (apply_subst (singleton_subst n s) t2) (Some r) ->
                                           sr = compose (singleton_subst n s) r ->
                                           unify t1 t2 (Some sr).

Example test1: unify (Cst 1)                 (Cst 2)                 None.                            Proof. repeat econstructor. Qed.
Example test2: unify (Cst 1)                 (Cst 1)                 (Some []).                       Proof. repeat econstructor. Qed.
Example test3: unify (Var 1)                 (Var 2)                 (Some [(1, Var 2)]).             Proof. repeat econstructor. Qed.
Example test4: unify (Var 1)                 (Var 1)                 (Some []).                       Proof. repeat econstructor. Qed.
Example test5: unify (Con 1 (Var 1) (Var 2)) (Con 2 (Var 1) (Var 2)) None.                            Proof. repeat econstructor. Qed.
Example test6: unify (Con 1 (Var 1) (Var 2)) (Con 1 (Var 1) (Var 2)) (Some []).                       Proof. repeat econstructor. Qed.
Example test7: unify (Con 1 (Var 1) (Var 1)) (Con 1 (Var 1) (Var 2)) (Some [(1, Var 2)]).             Proof. repeat econstructor. Qed.
Example test8: unify (Con 1 (Cst 1) (Var 2)) (Con 1 (Var 1) (Cst 2)) (Some [(1, Cst 1); (2, Cst 2)]). Proof. econstructor. econstructor. eapply unify_SubstSome. econstructor. econstructor. econstructor. econstructor. econstructor. Qed.

Lemma unify_exists : forall t1 t2, {r & unify t1 t2 r}.
Proof.
  intros t1 t2.
  remember (fun p => {r : option subst & unify (fst p) (snd p) r}) as P.
  assert (P (t1, t2)).
  {
    apply well_founded_induction with (R := fvOrderRel).
    * apply fvOrder_wf.
    * intros. subst. clear t1 t2. destruct x as [t1 t2]. simpl.
      destruct (unification_step t1 t2) eqn:eq.
      + exists None. constructor. assumption.
      + exists (Some empty_subst). constructor. assumption.
      + specialize (H (apply_subst (singleton_subst n t) t1, apply_subst (singleton_subst n t) t2)).
        assert (fvOr : fvOrderRel (apply_subst (singleton_subst n t) t1, apply_subst (singleton_subst n t) t2) (t1, t2)).
        { apply unification_step_decreases_fv. assumption. }
        specialize (H fvOr). destruct H. destruct x.
        - eexists. eapply unify_SubstSome.
          { eassumption. }
          { eassumption. }
          { reflexivity. }
        - exists None. eapply unify_SubstNone.
          { eassumption. }
          { eassumption. }
  }
  subst. assumption.
Qed.

Lemma unify_unique : forall t1 t2 r r', unify t1 t2 r -> unify t1 t2 r' -> r = r'.
Proof.
  intros t1 t2 r r' H. revert r'. induction H.
  * intros. inversion H; try reflexivity; rewrite e in H0; inversion H0.
  * intros. inversion H; try reflexivity; rewrite e in H0; inversion H0.
  * intros. inversion H0; try reflexivity.
    + rewrite e in H1; inversion H1.
    + rewrite e in H1; inversion H1. subst. apply IHunify in H2. inversion H2.
  * intros. inversion H0.
    + rewrite e in H1. inversion H1.
    + rewrite e in H1. inversion H1.
    + rewrite e in H1. inversion H1. subst.
      apply IHunify in H2. inversion H2.
    + rewrite e in H1. inversion H1. subst.
      apply IHunify in H2. inversion H2. reflexivity.
Qed.

Lemma fine_step_equal_terms :
  forall t1 t2,
    unification_step t1 t2 = Fine -> t1 = t2.
Proof.
  assert (createFine : forall n t, create n t <> Fine).
  { unfold create. intros n t C. destruct (occurs n t); inversion C. }
  induction t1; induction t2; intro us_eq; inversion us_eq; clear us_eq; subst.
  - destruct (Nat.eq_dec n n0).
    { congruence. }
    { apply createFine in H0. contradiction. }
  - apply createFine in H0. contradiction.
  - destruct (Nat.eq_dec n n0).
    { congruence. }
    { inversion H0. }
  - apply createFine in H0. contradiction.
  - destruct (Nat.eq_dec n n0).
    { subst. destruct (unification_step t1_1 t2_1) eqn:eq; inversion H0.
      apply IHt1_1 in eq. apply IHt1_2 in H0. congruence. }
    { inversion H0. }
Qed.


Lemma unify_unifies:
  forall t1 t2 s,
    unify t1 t2 (Some s) -> unifier s t1 t2.
Proof.
  intros t1 t2. remember (fun p => forall s : subst,
      unify (fst p) (snd p) (Some s) -> unifier s (fst p) (snd p)).
  assert (P (t1, t2)).
  {
    apply well_founded_induction with (R := fvOrderRel).
    * apply fvOrder_wf.
    * intros. subst. clear t1 t2. destruct x as [t1 t2]. simpl.
      intros. inversion H0; subst; clear H0.
      + unfold unifier. rewrite apply_empty. rewrite apply_empty.
        apply fine_step_equal_terms. assumption.
      + assert (fvOr : fvOrderRel (apply_subst (singleton_subst n s0) t1, apply_subst (singleton_subst n s0) t2) (t1, t2)).
        { apply unification_step_decreases_fv. assumption. }
        eapply H in fvOr.
        2: { eassumption. }
        { unfold unifier. rewrite compose_correctness. rewrite compose_correctness.
          assumption. }
  }
  subst. assumption.
Qed.

Lemma unification_step_binds :
  forall t1 t2 x t s,
    unification_step t1 t2 = Subst x t ->
    unifier s t1 t2 ->
    apply_subst s (Var x) = apply_subst s t.
Proof.
  induction t1; induction t2; intros; simpl in H.
  * destruct (Nat.eq_dec n n0).
    + inversion H.
    + unfold create in H. destruct (occurs n (Var n0)); inversion H.
      subst. assumption.
  * unfold create in H. destruct (occurs n (Cst n0)); inversion H. subst. assumption.
  * unfold create in H. destruct (occurs n (Con n0 t2_1 t2_2)); inversion H. subst. assumption.
  * unfold create in H. destruct (occurs n0 (Cst n)); inversion H. subst. symmetry. assumption.
  * destruct (Nat.eq_dec n n0); inversion H.
  * inversion H.
  * unfold create in H. destruct (occurs n0 (Con n t1_1 t1_2)); inversion H. subst. symmetry. assumption.
  * inversion H.
  * clear IHt2_1. clear IHt2_2.
    destruct (Nat.eq_dec n n0).
    + subst. destruct (unification_step t1_1 t2_1) eqn:eq.
      - inversion H.
      - inversion H0. apply IHt1_2 with t2_2; assumption.
      - inversion H. subst. inversion H0. apply IHt1_1 with t2_1; assumption.
    + inversion H.
Qed.

Lemma unification_step_binds_2 :
  forall t1 t2 x t s,
    unification_step t1 t2 = Subst x t ->
    unifier s t1 t2 ->
    forall t', apply_subst s t' = apply_subst s (apply_subst (singleton_subst x t) t').
Proof.
  intros. specialize (unification_step_binds t1 t2 x t s H H0). intro.
  induction t'.
  * simpl. destruct (Nat.eq_dec x n).
    + subst. rewrite <- H1. reflexivity.
    + reflexivity.
  * reflexivity.
  * simpl. rewrite IHt'1. rewrite IHt'2. reflexivity.
Qed.

Lemma unify_most_general :
  forall (t1 t2 : term) (m : subst),
    unify t1 t2 (Some m) ->
    forall (s : subst), unifier s t1 t2 -> more_general m s.
Proof.
  intros t1 t2 m H. remember (Some m) as r eqn:eq.
  generalize dependent eq. revert m.
  induction H; intros m eq; inversion eq; clear eq.
  * intros. unfold more_general. exists s. intros.
    rewrite apply_empty. reflexivity.
  * subst. specialize (IHunify r eq_refl).
    rename s into st. intros.
    specialize (unification_step_binds_2 t1 t2 n st s e H0). intro.
    assert (more_general r s).
    { apply IHunify. unfold unifier. rewrite <- H1. rewrite <- H1. apply H0. }
    unfold more_general in H2. destruct H2 as [d H2]. unfold more_general.
    exists d. intro. rewrite compose_correctness. rewrite <- H2. apply H1.
Qed.

Lemma occurs_subst_height: forall s n t,
  occurs n t = true -> height (apply_subst s (Var n)) <= height (apply_subst s t).
Proof.
  intros. induction t.
  * simpl in H. apply Nat.eqb_eq in H. subst. reflexivity.
  * inversion H.
  * simpl in H. apply Bool.orb_true_elim in H. destruct H.
    + apply IHt1 in e. simpl. apply le_S. eapply le_trans.
      eassumption. apply Nat.le_max_l.
    + apply IHt2 in e. simpl. apply le_S. eapply le_trans.
      eassumption. apply Nat.le_max_r.
Qed.

Lemma occurs_check_ground :
  forall x t s,
    occurs x t = true ->
    apply_subst s (Var x) = apply_subst s t ->
    Var x = t.
Proof.
  intros x t. destruct t.
  * intros. simpl in H. apply beq_nat_true_iff in H. congruence.
  * intros. inversion H.
  * intros. exfalso. simpl in H. apply Bool.orb_true_elim in H. destruct H.
    + apply occurs_subst_height with (s := s) in e. rewrite H0 in e.
      simpl in e. apply le_lt_n_Sm in e. apply lt_S_n in e.
      apply lt_irrefl with (height (apply_subst s t1)).
      eapply le_lt_trans.
      2: { eapply e. }
      apply Nat.le_max_l.
    + apply occurs_subst_height with (s := s) in e. rewrite H0 in e.
      simpl in e. apply le_lt_n_Sm in e. apply lt_S_n in e.
      apply lt_irrefl with (height (apply_subst s t2)).
      eapply le_lt_trans.
      2: { eapply e. }
      apply Nat.le_max_r.
Qed.

Lemma unify_non_unifiable :
  forall (t1 t2 : term),
    unify t1 t2 None -> forall s,  ~ (unifier s t1 t2).
Proof.
  intros t1 t2 H. remember None as r eqn:eq.
  induction H; inversion eq; clear eq.
  * generalize dependent e. revert t2.
    induction t1; induction t2; intros H s; inversion H.
    + destruct (Nat.eq_dec n n0).
      - inversion H1.
      - unfold create in H1. destruct (occurs n (Var n0)) eqn:eq; inversion H1.
        intro C. specialize (occurs_check_ground n (Var n0) s eq C). intro.
        inversion H0. contradiction.
    + unfold create in H1. destruct (occurs n (Con n0 t2_1 t2_2)) eqn:eq; inversion H1.
      intro C. specialize (occurs_check_ground n (Con n0 t2_1 t2_2) s eq C). intro.
      inversion H0.
    + destruct (Nat.eq_dec n n0).
      - inversion H1.
      - intro C. inversion C. contradiction.
    + intro C. inversion C.
    + unfold create in H1. destruct (occurs n0 (Con n t1_1 t1_2)) eqn:eq; inversion H1.
      intro C. red in C. symmetry in C.
      specialize (occurs_check_ground n0 (Con n t1_1 t1_2) s eq C).
      intro. inversion H0.
    + intro C. inversion C.
    + clear IHt2_1 IHt2_2. intro C. inversion C. destruct (Nat.eq_dec n n0).
      - subst. destruct (unification_step t1_1 t2_1) eqn:eq.
        { eapply IHt1_1; eassumption. }
        { eapply IHt1_2; eassumption. }
        { inversion H1. }
      - contradiction.
  * rename s into st. intros s C.
    specialize (IHunify eq_refl s).
    specialize (unification_step_binds_2 t1 t2 n st s e C). intros eq.
    apply IHunify. red. rewrite <- eq. rewrite <- eq. assumption.
Qed.

Lemma MGU_dom
      (t1 t2 : term)
      (s : subst)
      (MGU : unify t1 t2 (Some s))
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

Lemma MGU_vran
      (t1 t2 : term)
      (s : subst)
      (MGU : unify t1 t2 (Some s))
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
