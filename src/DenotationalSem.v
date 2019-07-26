Require Import List.
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

Lemma gt_fun_eq_apply (f1 f2 : gt_fun) (t : term) (feq : gt_fun_eq f1 f2) :
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

Definition subst_gt_fun_compose (s : subst) (f : gt_fun) : gt_fun :=
  fun x => apply_gt_fun f (apply_subst s (Var x)).

Lemma gt_fun_apply_compose (s : subst) (f : gt_fun) (t : term) :
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

Inductive in_denotational_sem_goal : goal -> gt_fun -> Prop :=
| dsgUnify  : forall f t1 t2 (UnH : gt_eq (apply_gt_fun f t1) (apply_gt_fun f t2)),
                             in_denotational_sem_goal (Unify t1 t2) f
| dsgDisjL  : forall f g1 g2 (Hg : in_denotational_sem_goal g1 f),
                             in_denotational_sem_goal (Disj g1 g2) f
| dsgDisjR  : forall f g1 g2 (Hg : in_denotational_sem_goal g2 f),
                             in_denotational_sem_goal (Disj g1 g2) f
| dsgConj   : forall f g1 g2 (Hg1 : in_denotational_sem_goal g1 f)
                             (Hg2 : in_denotational_sem_goal g2 f),
                             in_denotational_sem_goal (Conj g1 g2) f
| dsgFresh  : forall f fn a fg (fvH : ~ is_fv_of_goal a (Fresh fg))
                               (Hg : in_denotational_sem_goal (fg a) fn)
                               (Hease : forall (x : name) (neq : x <> a), gt_eq (fn x) (f x)),
                               in_denotational_sem_goal (Fresh fg) f
| dsgInvoke : forall r t f (Hbody : in_denotational_sem_goal (proj1_sig (MiniKanrenSyntax.P r) t) f),
                           in_denotational_sem_goal (Invoke r t) f.

Hint Constructors in_denotational_sem_goal.

Inductive in_denotational_sem_lev_goal : nat -> goal -> gt_fun -> Prop :=
| dslgUnify  : forall l f t1 t2 (UnH : gt_eq (apply_gt_fun f t1) (apply_gt_fun f t2)),
                                in_denotational_sem_lev_goal (S l) (Unify t1 t2) f
| dslgDisjL  : forall l f g1 g2 (Hg :in_denotational_sem_lev_goal l g1 f),
                                in_denotational_sem_lev_goal l (Disj g1 g2) f
| dslgDisjR  : forall l f g1 g2 (Hg :in_denotational_sem_lev_goal l g2 f),
                                in_denotational_sem_lev_goal l (Disj g1 g2) f
| dslgConj   : forall l f g1 g2 (Hg1 :in_denotational_sem_lev_goal l g1 f)
                                (Hg2 :in_denotational_sem_lev_goal l g2 f),
                                in_denotational_sem_lev_goal l (Conj g1 g2) f
| dslgFresh  : forall l f fn a fg (fvH : ~ is_fv_of_goal a (Fresh fg))
                                  (Hg :in_denotational_sem_lev_goal l (fg a) fn)
                                  (Hease : forall (x : name) (neq : x <> a), gt_eq (fn x) (f x)),
                                  in_denotational_sem_lev_goal l (Fresh fg) f
| dslgInvoke : forall l r t f (Hbody :in_denotational_sem_lev_goal l (proj1_sig (MiniKanrenSyntax.P r) t) f),
                              in_denotational_sem_lev_goal (S l) (Invoke r t) f.

Hint Constructors in_denotational_sem_lev_goal.

Lemma in_denotational_sem_zero_lev (g : goal)
                                   (f : gt_fun) :
                                   ~ in_denotational_sem_lev_goal 0 g f.
Proof.
  intro. remember 0 as l. induction H; inversion Heql; auto.
Qed.

Lemma in_denotational_sem_lev_monotone (l : nat)
                                       (g : goal)
                                       (f : gt_fun)
                                       (Hdsg : in_denotational_sem_lev_goal l g f)
                                       (l' : nat)
                                       (Hle: l <= l')
                                       : in_denotational_sem_lev_goal l' g f.
Proof.
  revert Hle. revert l'. induction Hdsg; eauto.
  { intros. destruct l'; auto. inversion Hle. }
  { intros. destruct l'.
    { inversion Hle. }
    { apply le_S_n in Hle. auto. } }
Qed.

Lemma in_denotational_sem_some_lev (g : goal)
                                   (f : gt_fun)
                                   (Hdsg : in_denotational_sem_goal g f) :
                                   exists l, in_denotational_sem_lev_goal l g f.
Proof.
  induction Hdsg.
  { exists 1. auto. }
  { destruct IHHdsg. eauto. }
  { destruct IHHdsg. eauto. }
  { destruct IHHdsg1. destruct IHHdsg2.
    exists (max x x0). constructor.
    { eapply in_denotational_sem_lev_monotone; eauto. apply PeanoNat.Nat.le_max_l. }
    { eapply in_denotational_sem_lev_monotone; eauto. apply PeanoNat.Nat.le_max_r. } }
  { destruct IHHdsg. eauto. }
  { destruct IHHdsg. eauto. }
Qed.