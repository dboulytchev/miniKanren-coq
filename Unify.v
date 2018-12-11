Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Eqdep.
Require Import Program.

(************************* Terms *************************)
(* Name of entities *)
Definition name := nat.

(* Term type *) 
Inductive term : Set :=
(* a variable           *) | Var : name -> term
(* a constant           *) | Cst : name -> term
(* a binary constructor *) | Con : name -> term -> term -> term.

(* Set union on lists *)
Definition union (l1 l2 : list name) : list name := nodup eq_nat_dec (l1 ++ l2).

(* Some lemmas for lists as sets *)
Lemma union_NoDup: forall (l1 l2 : list name), NoDup (union l1 l2).
Proof. intros. unfold union. apply NoDup_nodup. Qed.

Lemma union_In: forall (l1 l2 : list name) (n : name), In n (union l1 l2) <-> In n l1 \/ In n l2.
Proof.
  intros. unfold union. split.
  * intros. apply in_app_or. apply nodup_In in H. assumption.
  * intros. apply nodup_In. apply in_or_app. assumption.
Qed.

Lemma lt_length:
  forall (l1 l2 : list name),
    NoDup l1 -> NoDup l2 -> incl l1 l2 -> (exists n, In n l2 /\ ~ (In n l1)) -> length l1 < length l2.
Proof.
  intros. destruct H2. destruct H2. apply in_split in H2.
  destruct H2. destruct H2. subst.
  rewrite app_length. simpl.
  assert (length l1 <= length (x0 ++ x1)).
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

(* Free variables *)
Fixpoint fv (t : term) : list name :=
  match t with
  | Var x     => [x]
  | Cst _     => []
  | Con _ x y => union (fv x) (fv y)
  end.

(* fv returns NoDup *)
Lemma fv_NoDup: forall t,  NoDup (fv t).
Proof.
  intros. destruct t; unfold fv.
  * constructor.
    + auto.
    + constructor.
  * constructor.
  * apply union_NoDup.
Qed.

Fixpoint occurs (n : name) (t : term) : bool :=
  match t with
  | Var x     => Nat.eqb n x
  | Cst _     => false
  | Con _ l r => orb (occurs n l) (occurs n r)
  end.

(* In follows from occurs *)
Lemma occurs_In: forall t n, occurs n t = true <-> In n (fv t).
Proof.
  intros. split.
  * induction t; simpl.
    + intros H. apply Nat.eqb_eq in H. left. symmetry. assumption.
    + intros H. inversion H.
    + intros H. apply union_In. apply Bool.orb_prop in H. destruct H.
      - apply IHt1 in H. left. assumption.
      - apply IHt2 in H. right. assumption.
  * induction t; simpl.
    + intros H. destruct H.
      - apply Nat.eqb_eq. symmetry. assumption.
      - contradiction.
    + contradiction.
    + intros H. apply Bool.orb_true_intro. apply union_In in H. destruct H.
      - apply IHt1 in H. left. assumption.
      - apply IHt2 in H. right. assumption.
Qed.

(******************** Substitutions **********************)
(* Substitution *)
Definition subst : Type := list (name * term).

Definition empty_subst : subst := [].

Definition singleton_subst (n : name) (t : term) := [(n, t)].

(* Substitution domain *)
Fixpoint domain (s : subst) : list name := map (@fst name term) s.

(* Substitution image *)
Fixpoint image (s : subst) (n : name) : option term :=
  match s with
  | [] => None
  | (m, t) :: tl => if eq_nat_dec m n then Some t else image tl n
  end.

(* Substitution application *)
Fixpoint apply (s : subst) (t : term) : term :=
  match t with
  | Cst _     => t
  | Var n     => match image s n with None => t | Some t' => t' end
  | Con n l r => Con n (apply s l) (apply s r)
  end.

Lemma apply_empty: forall (t : term), apply empty_subst t = t.
Proof.
  induction t.
  * reflexivity.
  * reflexivity.
  * simpl. congruence.
Qed.

(* Free variables in the result of substitution application *)
Lemma apply_fv: forall t s n m,  In m (fv (apply [(n, s)] t)) -> In m (fv s) \/ In m (fv t).
Proof.
  induction t.
  * intros. unfold apply in H. unfold image in H. destruct (Nat.eq_dec n0 n).
    + left. assumption.
    + right. assumption.
  * intros. inversion H.
  * intros. unfold apply in H. fold apply in H.
    unfold fv in H. fold fv in H. apply union_In in H. destruct H.
    + apply IHt1 in H. destruct H.
      - left. assumption.
      - right. unfold fv. fold fv. apply union_In. left. assumption.
    + apply IHt2 in H. destruct H.
      - left. assumption.
      - right. unfold fv. fold fv. apply union_In. right. assumption.
Qed.

(* Composition *)
Definition compose (s1 s2 : subst) : subst :=
  List.map (fun p => (fst p, apply s2 (snd p))) s1 ++ s2.

Lemma compose_correctness: forall (s1 s2 : subst) (t : term),
  apply (compose s1 s2) t = apply s2 (apply s1 t).
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

(* Generality *)
Definition more_general (m s : subst) : Prop :=
  exists (s' : subst), forall (t : term), apply s t = apply s' (apply m t).

(* Unification property *)
Definition unifier (s : subst) (t1 t2 : term) : Prop := apply s t1 = apply s t2.

Inductive MGU : term -> term -> option subst -> Prop :=
| MGU_VVEq        : forall n,
                    MGU (Var n) (Var n) (Some empty_subst)
| MGU_VVNeq       : forall n1 n2,
                    n1 <> n2 ->
                    MGU (Var n1) (Var n2) (Some (singleton_subst n1 (Var n2)))
| MGU_VCst        : forall n c,
                    MGU (Var n) (Cst c) (Some (singleton_subst n (Cst c)))
| MGU_VConOccurs  : forall n c t1 t2,
                    occurs n (Con c t1 t2) = true ->
                    MGU (Var n) (Con c t1 t2) None
| MGU_VConSucc    : forall n c t1 t2,
                    occurs n (Con c t1 t2) = false ->
                    MGU (Var n) (Con c t1 t2) (Some (singleton_subst n (Con c t1 t2)))
| MGU_CstV        : forall n c,
                    MGU (Cst c) (Var n) (Some (singleton_subst n (Cst c)))
| MGU_ConVOccurs  : forall n c t1 t2,
                    occurs n (Con c t1 t2) = true ->
                    MGU (Con c t1 t2) (Var n) None
| MGU_ConVSucc    : forall n c t1 t2,
                    occurs n (Con c t1 t2) = false ->
                    MGU (Con c t1 t2) (Var n) (Some (singleton_subst n (Con c t1 t2)))
| MGU_CstCstNeq   : forall c1 c2,
                    c1 <> c2 ->
                    MGU (Cst c1) (Cst c2) None
| MGU_CstCstEq    : forall c,
                    MGU (Cst c) (Cst c) (Some empty_subst)
| MGU_ConConNeq   : forall c1 l1 r1 c2 l2 r2,
                    c1 <> c2 ->
                    MGU (Con c1 l1 r1) (Con c2 l2 r2) None
| MGU_ConConEqFL  : forall c l1 r1 l2 r2,
                    MGU l1 l2 None ->
                    MGU (Con c l1 r1) (Con c l2 r2) None
| MGU_ConConEqFR  : forall c l1 r1 l2 r2 sl,
                    MGU l1 l2 (Some sl) ->
                    MGU (apply sl r1) (apply sl r2) None ->
                    MGU (Con c l1 r1) (Con c l2 r2) None
| MGU_ConConEqSuc : forall c l1 r1 l2 r2 sl sr s,
                    MGU l1 l2 (Some sl) ->
                    MGU (apply sl r1) (apply sl r2) (Some sr) ->
                    s = compose sl sr ->
                    MGU (Con c l1 r1) (Con c l2 r2) (Some s).

Example test1: MGU (Cst 1)                 (Cst 2)                  None.                           Proof. constructor. intro C. inversion C. Qed.
Example test2: MGU (Cst 1)                 (Cst 1)                 (Some []).                       Proof. constructor. Qed.
Example test3: MGU (Var 1)                 (Var 2)                 (Some [(1, Var 2)]).             Proof. constructor. intro C. inversion C. Qed.
Example test4: MGU (Var 1)                 (Var 1)                 (Some []).                       Proof. constructor. Qed.
Example test5: MGU (Con 1 (Var 1) (Var 2)) (Con 2 (Var 1) (Var 2))  None.                           Proof. constructor. intro C. inversion C. Qed.
Example test6: MGU (Con 1 (Var 1) (Var 2)) (Con 1 (Var 1) (Var 2)) (Some []).                       Proof. econstructor. constructor. constructor. reflexivity. Qed.
Example test7: MGU (Con 1 (Var 1) (Var 1)) (Con 1 (Var 1) (Var 2)) (Some [(1, Var 2)]).             Proof. econstructor. constructor. constructor. intro C. inversion C. reflexivity. Qed.
Example test8: MGU (Con 1 (Cst 1) (Var 2)) (Con 1 (Var 1) (Cst 2)) (Some [(1, Cst 1); (2, Cst 2)]). Proof. econstructor. constructor. constructor. reflexivity. Qed.

Lemma apply_singleton_eq : forall n t, apply (singleton_subst n t) (Var n) = t.
Proof. intros. simpl. destruct (Nat.eq_dec n n). reflexivity. contradiction. Qed.

Lemma apply_singleton_not_occurs :
  forall n tn t,
    occurs n t = false -> apply (singleton_subst n tn) t = t.
Proof.
  intros n tn t. induction t; simpl.
  * intros H. apply Nat.eqb_neq in H. destruct (Nat.eq_dec n0 n).
    + symmetry in e. contradiction.
    + destruct (Nat.eq_dec n n0).
      - symmetry in e. contradiction.
      - reflexivity.
  * intros _. reflexivity.
  * intros H. apply Bool.orb_false_elim in H. destruct H. rewrite IHt1. rewrite IHt2. reflexivity.
    { assumption. }
    { assumption. }
Qed.

Lemma mgu_unifies:
  forall (t1 t2 : term) (s : subst),
    MGU t1 t2 (Some s) -> unifier s t1 t2.
Proof.
  intros. remember (Some s) as r. red. revert s Heqr.
  induction H; intros ss Heqr; inversion Heqr; clear Heqr; subst.
  * reflexivity.
  * rewrite apply_singleton_eq. rewrite apply_singleton_not_occurs.
    + reflexivity.
    + simpl. apply Nat.eqb_neq. assumption.
  * rewrite apply_singleton_eq. reflexivity.
  * rewrite apply_singleton_eq. rewrite apply_singleton_not_occurs. reflexivity.
    { assumption. }
  * rewrite apply_singleton_eq. reflexivity.
  * rewrite apply_singleton_eq. rewrite apply_singleton_not_occurs. reflexivity.
    { assumption. }
  * reflexivity.
  * simpl. assert (Heql: apply (compose sl sr) l1 = apply (compose sl sr) l2).
    { rewrite compose_correctness. rewrite compose_correctness. rewrite IHMGU1; reflexivity. }
    rewrite Heql. assert (Heqr: apply (compose sl sr) r1 = apply (compose sl sr) r2).
    { rewrite compose_correctness. rewrite compose_correctness. rewrite IHMGU2; reflexivity. }
    rewrite Heqr. reflexivity.
Qed.

Lemma mgu_most_general:
  forall (t1 t2 : term) (m : subst),
    MGU t1 t2 (Some m) -> forall (s : subst), unifier s t1 t2 -> more_general m s.
Proof.
  assert (L : forall (n : name) (tn : term) (s : subst),
      apply s (Var n) = apply s tn ->
      forall t : term, apply s t = apply s (apply (singleton_subst n tn) t)).
  {
    intros. induction t.
    * simpl. destruct (Nat.eq_dec n n0).
      + rewrite <- H. rewrite e. reflexivity.
      + reflexivity.
    * reflexivity.
    * simpl. congruence.
  }
  unfold more_general. unfold unifier. intros t1 t2 m H.
  remember (Some m) as r. revert m Heqr.
  induction H; intros m Heqr; inversion Heqr; clear Heqr; subst.
  * intros. exists s. intros. rewrite <- compose_correctness. reflexivity.
  * intros. exists s. induction t.
    + simpl. destruct (Nat.eq_dec n1 n).
      - rewrite <- H0. rewrite e. reflexivity.
      - reflexivity.
    + reflexivity.
    + simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  * intros. exists s. apply L. assumption.
  * intros. exists s. apply L. assumption.
  * intros. exists s. apply L. symmetry. assumption.
  * intros. exists s. apply L. symmetry. assumption.
  * intros. exists s. intros. rewrite apply_empty. reflexivity.
  * intros. inversion H1. clear H1.
    apply (IHMGU1 sl eq_refl s) in H3. destruct H3 as [ds H3].
    rewrite H3 in H4. rewrite H3 in H4.
    apply (IHMGU2 sr eq_refl ds) in H4. destruct H4 as [dds H4].
    exists dds. intros. rewrite H3. rewrite H4. rewrite compose_correctness.
    reflexivity.
Qed.

Fixpoint height (t : term) : nat :=
  match t with
  | Var _     => 1
  | Cst _     => 1
  | Con _ l r => S (max (height l) (height r))
  end.

Lemma occurs_subst_height: forall s n t,
  occurs n t = true -> height (apply s (Var n)) <= height (apply s t).
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

Lemma mgu_non_unifiable:
  forall (t1 t2 : term),
    MGU t1 t2 None -> ~(exists (s : subst), unifier s t1 t2).
Proof.
  assert (occurs_check_H: forall n c l r,
    occurs n (Con c l r) = true -> ~(exists (s : subst), apply s (Var n) = apply s (Con c l r))).
  {
    intros. intro. destruct H0 as [s H0].
    assert (height (apply s (Var n)) < height (apply s (Con c l r))).
    {
      simpl. apply le_lt_n_Sm. simpl in H.
      apply Bool.orb_true_elim in H. destruct H.
      * eapply le_trans.
        + eapply occurs_subst_height. eassumption.
        + apply Nat.le_max_l.
      * eapply le_trans.
        + eapply occurs_subst_height. eassumption.
        + apply Nat.le_max_r.
    }
    rewrite H0 in H1. eapply Nat.lt_irrefl. eassumption.
  }
  intros. remember None as r. unfold unifier.
  induction H; inversion Heqr; clear Heqr; subst.
  * apply occurs_check_H. assumption.
  * intro. destruct H0 as [s H0]. eapply occurs_check_H.
    eassumption. exists s. symmetry. assumption.
  * intro. destruct H0 as [s H0]. inversion H0. contradiction.
  * intro. destruct H0 as [s H0]. inversion H0. contradiction.
  * intro. destruct H0 as [s H0]. apply IHMGU.
    + reflexivity.
    + exists s. inversion H0. reflexivity.
  * intro. destruct H1 as [s H1]. apply IHMGU2.
    + reflexivity.
    + inversion H1. eapply mgu_most_general in H.
      2: { eassumption. }
      { destruct H as [ds H]. exists ds.
        rewrite <- H. rewrite <- H. assumption. }
Qed.
