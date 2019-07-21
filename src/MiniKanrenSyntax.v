Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Omega.
Require Eqdep_dec Arith.
Require Import Unify.

Inductive goal : Set :=
(* failure     *) | Fail   : goal
(* unification *) | Unify  : term -> term -> goal
(* disjunction *) | Disj   : goal -> goal -> goal
(* conjunction *) | Conj   : goal -> goal -> goal
(* fresh       *) | Fresh  : (name -> goal) -> goal
(* invoke      *) | Invoke : name -> term -> goal.

(* rel is a body of a relational symbol *)
Definition rel : Set := term -> goal.

Fixpoint rename_var_in_goal (old_x : name) (new_x : name) (g : goal) : goal :=
  match g with
  | Fail         => Fail
  | Unify t1 t2  => Unify (apply_subst [(old_x, Var new_x)] t1)
                          (apply_subst [(old_x, Var new_x)] t2)
  | Disj g1 g2   => Disj (rename_var_in_goal old_x new_x g1)
                         (rename_var_in_goal old_x new_x g2)
  | Conj g1 g2   => Conj (rename_var_in_goal old_x new_x g1)
                         (rename_var_in_goal old_x new_x g2)
  | Fresh fg     => Fresh (fun n => rename_var_in_goal old_x new_x (fg n))
  | Invoke r arg => Invoke r (apply_subst [(old_x, Var new_x)] arg)
  end.

Definition consistent_binding (b : name -> goal) : Prop :=
  forall x y, b y = rename_var_in_goal x y (b x).

Inductive consistent_goal : goal -> Prop :=
| cgFail   : consistent_goal Fail
| cgUnify  : forall t1 t2, consistent_goal (Unify t1 t2)
| cgDisj   : forall g1 g2 (Hcg1 : consistent_goal g1)
                          (Hcg2 : consistent_goal g2),
                          consistent_goal (Disj g1 g2)
| cgConj   : forall g1 g2 (Hcg1 : consistent_goal g1)
                          (Hcg2 : consistent_goal g2),
                          consistent_goal (Conj g1 g2)
| cgFresh  : forall fg (HBinding : consistent_binding fg)
                       (HcgInner : forall n, consistent_goal (fg n)),
                       consistent_goal (Fresh fg)
| cgInvoke : forall r arg, consistent_goal (Invoke r arg).

Definition consistent_rel (r : rel) : Prop :=
  forall (arg : term), consistent_goal (r arg).

Inductive is_fv_of_goal (n : name) : goal -> Prop :=
| fvUnifyL : forall t1 t2 (HInFv : In n (fv_term t1)),
                          is_fv_of_goal n (Unify t1 t2)
| fvUnifyR : forall t1 t2 (HInFv : In n (fv_term t2)),
                          is_fv_of_goal n (Unify t1 t2)
| fvDisjL  : forall g1 g2 (HisFV : is_fv_of_goal n g1),
                          is_fv_of_goal n (Disj g1 g2)
| fvDisjR  : forall g1 g2 (HisFV : is_fv_of_goal n g2),
                          is_fv_of_goal n (Disj g1 g2)
| fvConjL  : forall g1 g2 (HisFV : is_fv_of_goal n g1),
                          is_fv_of_goal n (Conj g1 g2)
| fvConjR  : forall g1 g2 (HisFV : is_fv_of_goal n g2),
                          is_fv_of_goal n (Conj g1 g2)
| fvFresh  : forall fg n' (neq : n' <> n)
                          (HisFV : is_fv_of_goal n (fg n')),
                          is_fv_of_goal n (Fresh fg)
| fvInvoke : forall r arg (HInFv : In n (fv_term arg)),
                          is_fv_of_goal n (Invoke r arg).

Hint Constructors is_fv_of_goal.

(* Closedness of goals *)
Definition closed_goal_in_context (c : list name) (g : goal) : Prop :=
  forall n, is_fv_of_goal n g -> In n c.

Definition closed_goal : goal -> Prop := closed_goal_in_context [].

(* Closedness of a relational symbol *)
Definition closed_rel (r : rel) : Prop :=
  forall (arg : term), closed_goal_in_context (fv_term arg) (r arg).

(* Some checks *)
Module SmokeTest.

  Definition g0 : goal := Fresh (fun x => Unify (Var x) (Cst 2)).
  Definition g1 : goal := Fresh (fun x => Fresh (fun y => Unify (Var x) (Var y))).

  Lemma g0_closed : closed_goal g0.
  Proof.
    red. red. intros. inversion H. inversion HisFV.
    { simpl in HInFv. destruct HInFv; contradiction. }
    { inversion HInFv. }
  Qed.

  Lemma g1_closed : closed_goal g1.
  Proof.
    red. red. intros. inversion H. inversion HisFV.
    inversion HisFV0; inversion HInFv; contradiction.
  Qed.

  Definition r0 : rel := (fun t => Fresh (fun x => Fresh (fun y =>
      Conj (Unify t (Con 0 (Var x) (Var y))) (Unify (Var x) (Var y))))).
  Definition r1 : rel := (fun t => Fresh (fun x => Unify (Var 0) t)).

  Lemma r0_closed : closed_rel r0.
  Proof.
    red. red. intros. inversion H. inversion HisFV.
    inversion HisFV0.
    { inversion HisFV; auto. inversion HisFV2; inversion HisFV3.
      { auto. }
      { simpl in HInFv. destruct (name_eq_dec n'1 n').
        { inversion HInFv; contradiction. }
        { inversion HInFv; try contradiction. inversion H0; contradiction. } }
      { inversion HInFv; contradiction. }
      { inversion HInFv; contradiction. } }
    { inversion HisFV1; inversion HInFv; contradiction. }
  Qed.

  Lemma r1_non_closed : ~ closed_rel r1.
  Proof.
    intro C. red in C. red in C.
    specialize (C (Cst 0) 0). apply C.
    unfold r1. apply fvFresh with 1.
    { omega. }
    { constructor. left. auto. }
  Qed.

End SmokeTest.

(* def is a definition of a closed relational symbol *)
Definition def : Set := {r : rel | closed_rel r (* /\ consistent_rel r*)}.

(* spec is a list of definitions *)
Definition spec : Set := name -> def.

Variable P : spec.
