Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Omega.
Require Import Unify.

Inductive goal : Set :=
| Fail     : goal
| Cut      : goal                     (* for SLD semantics only, in others is treated as 'success' *)
| Unify    : term -> term -> goal
| Disunify : term -> term -> goal
| Disj     : goal -> goal -> goal
| Conj     : goal -> goal -> goal
| Fresh    : (name -> goal) -> goal
| Invoke   : name -> term -> goal.

(* rel is a body of a relational symbol *)
Definition rel : Set := term -> goal.

Inductive is_fv_of_goal (n : name) : goal -> Prop :=
| fvUnifyL : forall t1 t2 (IN_FV : In n (fv_term t1)),
                          is_fv_of_goal n (Unify t1 t2)
| fvUnifyR : forall t1 t2 (IN_FV : In n (fv_term t2)),
                          is_fv_of_goal n (Unify t1 t2)
| fvDisunifyL : forall t1 t2 (IN_FV : In n (fv_term t1)),
                             is_fv_of_goal n (Disunify t1 t2)
| fvDisunifyR : forall t1 t2 (IN_FV : In n (fv_term t2)),
                             is_fv_of_goal n (Disunify t1 t2)
| fvDisjL  : forall g1 g2 (IS_FV : is_fv_of_goal n g1),
                          is_fv_of_goal n (Disj g1 g2)
| fvDisjR  : forall g1 g2 (IS_FV : is_fv_of_goal n g2),
                          is_fv_of_goal n (Disj g1 g2)
| fvConjL  : forall g1 g2 (IS_FV : is_fv_of_goal n g1),
                          is_fv_of_goal n (Conj g1 g2)
| fvConjR  : forall g1 g2 (IS_FV : is_fv_of_goal n g2),
                          is_fv_of_goal n (Conj g1 g2)
| fvFresh  : forall fg n' (NEQ : n' <> n)
                          (IS_FV : is_fv_of_goal n (fg n')),
                          is_fv_of_goal n (Fresh fg)
| fvInvoke : forall r arg (IN_FV : In n (fv_term arg)),
                          is_fv_of_goal n (Invoke r arg).

Hint Constructors is_fv_of_goal.

Definition closed_goal_in_context (c : list name) (g : goal) : Prop :=
  forall n, is_fv_of_goal n g -> In n c.

Definition closed_goal : goal -> Prop := closed_goal_in_context [].

Definition closed_rel (r : rel) : Prop :=
  forall (arg : term), closed_goal_in_context (fv_term arg) (r arg).

(* Some checks *)
Module SmokeTest.

  Definition g0 : goal := Fresh (fun x => Unify (Var x) (Cst 2)).
  Definition g1 : goal := Fresh (fun x => Fresh (fun y => Unify (Var x) (Var y))).

  Lemma g0_closed : closed_goal g0.
  Proof.
    red. red. intros. inversion H. inversion IS_FV.
    { simpl in IN_FV. destruct IN_FV; contradiction. }
    { inversion IN_FV. }
  Qed.

  Lemma g1_closed : closed_goal g1.
  Proof.
    red. red. intros. inversion H. inversion IS_FV.
    inversion IS_FV0; inversion IN_FV; contradiction.
  Qed.

  Definition r0 : rel := (fun t => Fresh (fun x => Fresh (fun y =>
      Conj (Unify t (Con 0 (Var x) (Var y))) (Unify (Var x) (Var y))))).
  Definition r1 : rel := (fun t => Fresh (fun x => Unify (Var 0) t)).

  Lemma r0_closed : closed_rel r0.
  Proof.
    red. red. intros. inversion H. inversion IS_FV.
    inversion IS_FV0.
    { inversion IS_FV; auto. inversion IS_FV2; inversion IS_FV3.
      { auto. }
      { simpl in IN_FV. destruct (name_eq_dec n'1 n').
        { inversion IN_FV; contradiction. }
        { inversion IN_FV; try contradiction. inversion H0; contradiction. } }
      { inversion IN_FV; contradiction. }
      { inversion IN_FV; contradiction. } }
    { inversion IS_FV1; inversion IN_FV; contradiction. }
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

(* Weak version of a variable renaming *)
Inductive renaming (old_x : name) (new_x : name) : goal -> goal -> Prop :=
| rFail : renaming old_x new_x Fail Fail
| rCut  : renaming old_x new_x Cut Cut
| rUnify : forall t1 t2, renaming old_x new_x (Unify t1 t2)
                                              (Unify (apply_subst [(old_x, Var new_x)] t1)
                                                     (apply_subst [(old_x, Var new_x)] t2))
| rDisunify : forall t1 t2, renaming old_x new_x (Disunify t1 t2)
                                                 (Disunify (apply_subst [(old_x, Var new_x)] t1)
                                                           (apply_subst [(old_x, Var new_x)] t2))
| rDisj : forall g1 g2 rg1 rg2 (R_G1 : renaming old_x new_x g1 rg1)
                               (R_G2 : renaming old_x new_x g2 rg2),
                               renaming old_x new_x (Disj g1 g2) (Disj rg1 rg2)
| rConj : forall g1 g2 rg1 rg2 (R_G1 : renaming old_x new_x g1 rg1)
                               (R_G2 : renaming old_x new_x g2 rg2),
                               renaming old_x new_x (Conj g1 g2) (Conj rg1 rg2)
| rFreshNFV : forall fg (OLD_X_NOT_FV : ~ is_fv_of_goal old_x (Fresh fg)),
                        renaming old_x new_x (Fresh fg) (Fresh fg)
| rFreshFV : forall fg rfg (OLD_X_FV : is_fv_of_goal old_x (Fresh fg))
                           (R_FG : forall y (Y_NOT_FV : ~ is_fv_of_goal y (Fresh fg)),
                                            renaming old_x new_x (fg y) (rfg y)),
                           renaming old_x new_x (Fresh fg) (Fresh rfg)
| rInvoke : forall r arg, renaming old_x new_x (Invoke r arg)
                                               (Invoke r (apply_subst [(old_x, Var new_x)] arg)).

Hint Constructors renaming.

Definition consistent_binding (b : name -> goal) : Prop :=
  forall x y, (~ is_fv_of_goal x (Fresh b)) -> renaming x y (b x) (b y).

Inductive consistent_goal : goal -> Prop :=
| cgFail   : consistent_goal Fail
| cgCut    : consistent_goal Cut
| cgUnify  : forall t1 t2, consistent_goal (Unify t1 t2)
| cgDisunify  : forall t1 t2, consistent_goal (Disunify t1 t2)
| cgDisj   : forall g1 g2 (CG_G1 : consistent_goal g1)
                          (CG_G2 : consistent_goal g2),
                          consistent_goal (Disj g1 g2)
| cgConj   : forall g1 g2 (CG_G1 : consistent_goal g1)
                          (CG_G2 : consistent_goal g2),
                          consistent_goal (Conj g1 g2)
| cgFresh  : forall fg (CB_FG : consistent_binding fg)
                       (CG_BODY : forall n, consistent_goal (fg n)),
                       consistent_goal (Fresh fg)
| cgInvoke : forall r arg, consistent_goal (Invoke r arg).

Hint Constructors consistent_goal.

Definition consistent_function (f : term -> goal) : Prop :=
  forall a1 a2 t, renaming a1 a2 (f t) (f (apply_subst [(a1, Var a2)] t)).

Definition consistent_rel (r : rel) : Prop :=
  forall (arg : term), consistent_goal (r arg) /\ consistent_function r.

Definition def : Set := {r : rel | closed_rel r /\ consistent_rel r}.

Definition spec : Set := name -> def.

Variable Prog : spec.
