Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Omega.

Require Import Unification.

Inductive goal : Set :=
| Fail   : goal
| Unify  : term -> term -> goal
| Disj   : goal -> goal -> goal
| Conj   : goal -> goal -> goal
| Fresh  : (name -> goal) -> goal
| Invoke : name -> term -> goal.

Definition rel : Set := term -> goal.

Inductive is_fv_of_goal (n : name) : goal -> Prop :=
| fvUnifyL : forall t1 t2 (IN_FV : In n (fv_term t1)),
                          is_fv_of_goal n (Unify t1 t2)
| fvUnifyR : forall t1 t2 (IN_FV : In n (fv_term t2)),
                          is_fv_of_goal n (Unify t1 t2)
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

Hint Constructors is_fv_of_goal : core.



(* Weak version of a variable renaming *)
Inductive renaming (old_x : name) (new_x : name) : goal -> goal -> Prop :=
| rFail : renaming old_x new_x Fail Fail
| rUnify : forall t1 t2, renaming old_x new_x (Unify t1 t2)
                                              (Unify (apply_subst [(old_x, Var new_x)] t1)
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

Hint Constructors renaming : core.

Definition consistent_binding (b : name -> goal) : Prop :=
  forall x y, (~ is_fv_of_goal x (Fresh b)) -> renaming x y (b x) (b y).

Inductive consistent_goal : goal -> Prop :=
| cgFail   : consistent_goal Fail
| cgUnify  : forall t1 t2, consistent_goal (Unify t1 t2)
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

Hint Constructors consistent_goal : core.

Definition consistent_function (f : term -> goal) : Prop :=
  forall a1 a2 t, renaming a1 a2 (f t) (f (apply_subst [(a1, Var a2)] t)).

Definition consistent_rel (r : rel) : Prop :=
  forall (arg : term), consistent_goal (r arg) /\ consistent_function r.



Definition closed_goal_in_context (c : list name) (g : goal) : Prop :=
  forall n, is_fv_of_goal n g -> In n c.

Definition closed_rel (r : rel) : Prop :=
  forall (arg : term), closed_goal_in_context (fv_term arg) (r arg).



Definition def : Set := {r : rel | closed_rel r /\ consistent_rel r}.

Definition spec : Set := name -> def.

Axiom Prog : spec.
