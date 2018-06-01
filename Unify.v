Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.

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

(* Occurs property *)
Definition occurs (n : name) (t : term) : bool :=
  if find (fun x => if eq_nat_dec x n then true else false) (fv t)
  then true
  else false.

(* In follows from occurs *)
Lemma occurs_In: forall t n, occurs n t = true <-> In n (fv t).
Proof.
  intros. unfold occurs.
  destruct (find (fun x : nat => if Nat.eq_dec x n then true else false)
                 (fv t)) eqn:eq.
  * split.
    + intros. generalize dependent eq. induction (fv t).
      - intros. inversion eq.
      - intros. unfold find in eq. destruct (Nat.eq_dec a n).
        { inversion eq; subst. unfold In. left. reflexivity. }
        { apply IHl in eq. unfold In. right. assumption.  }
    + auto.
  * split.
    + intros. inversion H.
    + intros.
      induction (fv t).
      - inversion H.
      - unfold find in eq. destruct (Nat.eq_dec a n).
        { inversion eq. }
        { apply IHl.
          * assumption.
          * destruct H.
            + contradiction.
            + assumption. }
Qed.


(******************** Substitutions **********************)
(* Substitution *)
Definition subst : Type := list (name * term).

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

(* Generality *)
Definition more_general (m s : subst) : Prop :=
  exists (s' : subst), forall (t : term), apply s t = apply s' (apply m t).

(* Unification property *)
Definition unifier (s : subst) (t1 t2 : term) : Prop := apply s t1 = apply s t2.

(* MGU *)
Definition mgu (m : subst) (t1 t2 : term) : Prop :=
  unifier m t1 t2 /\ forall (s : subst), unifier s t1 t2 -> more_general m s.

(*
(******************** Well-formed Substitutions ***********)
(* Substitution welformedness *)
Definition subst_wf (s : subst) : Prop :=
  forall (m n : name), forall (t : term), In m (domain s) -> image s n = Some t -> occurs m t = false.

(* Well-formed substitution *)
Definition swbst := {s : subst | subst_wf s}.

(* Coercion *)
Definition coerce (T : Type) (P : subst -> T) (s: swbst) : T :=
  match s with exist l _ => P l end.
             
(* Empty well-formed substitution *)
Definition empty : subst := [].
(*
Proof.
  exists []. unfold subst_wf. intros. simpl in H. inversion H.
Qed.
*)
(* Extending a well-fromed substitution *)
Definition extend (b : subst) (n : name) (t : term) := (n, apply b t) :: b.

(* Singleton substitution *)
Definition trivial (n : name) (t : term) : subst := extend empty n t.
(*
(* Singleton well-formed substitution construction *)
Definition trivial (n : name) (t : term) : option swbst.
Proof.
  remember (occurs n t). destruct b.
  * exact None.
  * remember [(n, t)]. assert (A: image l n = Some t). rewrite Heql. simpl.
    destruct (eq_nat_dec n n). auto. exfalso. auto. refine (Some _). exists l.
    rewrite Heql. unfold subst_wf. intros. simpl in H.
    destruct (eq_nat_dec n n0). inversion H. subst. auto. inversion H.
Qed.
 *)
*)
Inductive outcome : Set :=
| Fail
| Fine
| Subst : forall (n: name) (t: term), outcome.  

Definition create (n: name) (t: term) : outcome :=
  if occurs n t then Fail else Subst n t.

(* Find a difference in a couple of terms and try to make a unification step *)
Fixpoint unification_step (t1 t2 : term) : outcome :=
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
    unification_step_ok t1 t2 n s -> (forall m, In m (fv s) -> In m (fv t1) \/ In m (fv t2)).
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
            + left. unfold fv. fold fv. apply union_In. right. assumption.
            + right. unfold fv. fold fv. apply union_In. right. assumption.
          - assumption. }
        { inversion H; subst. unfold unification_step_ok in IHt1_1.
          apply IHt1_1 with (m := m) in eq.
          - destruct eq.
            + left. unfold fv. fold fv. apply union_In. left. assumption.
            + right. unfold fv. fold fv. apply union_In. left. assumption.
          - assumption. }
      - inversion H.
Qed.

Lemma unification_step_subst_wf:
  forall t1 t2 s n, unification_step_ok t1 t2 n s -> ~ In n (fv s).
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
  forall t1 t2 s n, unification_step_ok t1 t2 n s -> In n (fv t1) \/ In n (fv t2).
Proof.
  assert (invCr: forall n0 n1 t0 t1, create n0 t0 = Subst n1 t1 -> n0 = n1).
  { intros. unfold create in H. destruct (occurs n0 t0).
    - inversion H.
    - inversion H. reflexivity. }
  assert (fvInFv: forall n, In n (fv (Var n))).
  { unfold fv. unfold In. left. reflexivity. }
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
          * left. unfold fv. fold fv. apply union_In. right. assumption.
          * right. unfold fv. fold fv. apply union_In. right. assumption. }
        inversion H.
      - destruct (Nat.eq_dec n n1); inversion H; subst.
        unfold unification_step_ok in IHt1_1. apply IHt1_1 in eq. destruct eq.
        { left. unfold fv. fold fv. apply union_In. left. assumption. }
        right. unfold fv. fold fv. apply union_In. left. assumption.
Qed.

Lemma unification_step_subst_elims: forall s t n, In n (fv (apply [(n, s)] t)) -> In n (fv s).
Proof.
  intros s t n. induction t.
  * unfold apply. unfold image. destruct (Nat.eq_dec n n0).
    + auto.
    + unfold fv. intros. exfalso. inversion H.
      - apply n1. symmetry. assumption.
      - inversion H0.
  * intros. inversion H.
  * intros. unfold apply in H. fold apply in H. unfold fv in H. fold fv in H.
    apply union_In in H. destruct H; auto.
Qed.

Lemma unification_step_decreases_fv:
  forall t1 t2 s n,
    unification_step_ok t1 t2 n s ->
    length (union (fv (apply [(n, s)] t1)) (fv (apply [(n, s)] t2))) < length (union (fv t1) (fv t2)).
Proof.
  intros t1 t2 s n USok. 
  apply lt_length; try apply union_NoDup.
  * intros n0 InH. apply union_In in InH. inversion_clear InH.
    + apply apply_fv in H. inversion_clear H.
      - apply unification_step_fv with (m:=n0) in USok.
        { apply union_In. auto. }
        auto.
      - apply union_In. left. auto.
    + apply apply_fv in H. inversion_clear H.
      - apply unification_step_fv with (m:=n0) in USok.
        { apply union_In. auto. }
        auto.
      - apply union_In. right. auto.
  * exists n. split.
    + apply unification_step_subst_occurs in USok. apply union_In. auto.
    + unfold not. intro H. apply union_In in H. inversion_clear H as [H0 | H0];
      apply unification_step_subst_elims in H0;
      apply unification_step_subst_wf in USok; auto.
Qed.
