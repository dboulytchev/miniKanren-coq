Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Omega.
Require Eqdep_dec Arith.
Require Import Unify.

Inductive goal : Set :=
(* unification *) | Unify  : term -> term -> goal
(* disjunction *) | Disj   : goal -> goal -> goal
(* conjunction *) | Conj   : goal -> goal -> goal
(* fresh       *) | Fresh  : (name -> goal) -> goal
(* invoke      *) | Invoke : name -> term -> goal.

(* Free variable monadic enumerator *)
Fixpoint fvm (n : name) (g : goal) : list name * name :=
  match g with
  | Unify t1 t2 => (var_set_union (fv_term t1) (fv_term t2), n)
  | Disj  g1 g2
  | Conj  g1 g2 => let (s1, n1) := fvm n  g1 in
                   let (s2, n2) := fvm n1 g2 in
                   (var_set_union s1 s2, n2)
  | Fresh fg    => let g := fg n in
                   let (ts, n') := fvm (S n) g in
                   (var_set_remove n ts, n')
  | Invoke _ t => (fv_term t, n)
  end.

(* Free variables enumerator *)
Definition fv_goal n g := fst (fvm n g).

(* Closedness of goals *)
Definition closed_goal_in_context (c : list name) (g : goal) : Prop :=
  forall x n, In x (fv_goal n g) -> In x c.

Definition closed_goal : goal -> Prop := closed_goal_in_context [].

(* rel is a body of a relational symbol *)
Definition rel : Set := term -> goal.

(* Closedness of a relational symbol *)
Definition closed_rel (r : rel) : Prop :=
  forall (arg : term), closed_goal_in_context (fv_term arg) (r arg).

(* Some checks *)
Module SmokeTest.

  Definition g0 : goal := Fresh (fun x => Unify (Var x) (Cst 2)).
  Definition g1 : goal := Fresh (fun x => Fresh (fun y => Unify (Var x) (Var y))).

  Lemma g0_closed : closed_goal g0.
  Proof.
    red. red. intros. unfold fv_goal in H. unfold fvm in H.
    simpl in H. destruct (name_eq_dec n n).
    * auto.
    * contradiction.
  Qed.

  Lemma g1_closed : closed_goal g1.
  Proof.
    red. red. intros. unfold fv_goal in H. unfold fvm in H.
    simpl in H. destruct n.
    * auto.
    * destruct (name_eq_dec (S n) n).
      + omega.
      + unfold var_set_remove in H.
        unfold set_remove in H.
        destruct (name_eq_dec (S (S n)) (S n));
        destruct (name_eq_dec (S (S n)) (S (S n)));
        destruct (name_eq_dec (S n) (S n));
        try omega. auto.
  Qed.

  Definition r0 : rel := (fun t => Fresh (fun x => Fresh (fun y =>
      Conj (Unify t (Con 0 (Var x) (Var y))) (Unify (Var x) (Var y))))).
  Definition r1 : rel := (fun t => Fresh (fun x => Unify (Var 0) t)).

  Lemma r0_closed : closed_rel r0.
  Proof.
    red. red. intros. unfold fv_goal in H. unfold fvm in H.
    red in H. red in H. red in H. fold In in H.
    assert (NoDup (var_set_union
               (var_set_union (fv_term arg)
                  (fv_term (Con 0 (Var n) (Var (S n)))))
               (var_set_union (fv_term (Var n))
                  (fv_term (Var (S n)))))).
    { apply set_union_nodup; apply set_union_nodup; apply fv_term_nodup. }
    assert (NoDup
       (var_set_remove (S n)
            (var_set_union
               (var_set_union (fv_term arg)
                  (fv_term (Con 0 (Var n) (Var (S n)))))
               (var_set_union (fv_term (Var n))
                  (fv_term (Var (S n))))))).
    { apply set_remove_nodup. auto. }
    unfold var_set_remove in H.
    apply (set_remove_iff name_eq_dec _ _ H1) in H. destruct H.
    apply (set_remove_iff name_eq_dec _ _ H0) in H. destruct H.
    unfold var_set_union in H. apply set_union_elim in H. destruct H.
    + apply set_union_elim in H. destruct H.
      - auto.
      - simpl in H. destruct n.
        { destruct H; try omega. destruct H; try omega. inversion H. }
        { destruct (name_eq_dec (S n) n); try omega.
          destruct H; try omega. destruct H; try omega. inversion H. }
    + simpl in H. destruct n.
      { destruct H; try omega. destruct H; try omega. inversion H. }
      { destruct (name_eq_dec (S n) n); try omega.
        destruct H; try omega. destruct H; try omega. inversion H. }
  Qed.

  Lemma r1_non_closed : ~ closed_rel r1.
  Proof.
    intro C. red in C. red in C.
    specialize (C (Cst 0) 0 1). apply C.
    simpl. auto.
  Qed.

End SmokeTest.

(* def is a definition of a closed relational symbol *)
Inductive def : Set :=
  Def : forall (r: rel), closed_rel r -> def.

(* spec is a list of definitions *)
Definition spec : Set := list (name * def).
