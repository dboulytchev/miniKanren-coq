Require Import List.
Import ListNotations.
Require Import Stream.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import OperationalSem.
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

(* Simple variant *)
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
                               (Hease : forall (x : name) (neq : x <> a), fn x = f x),
                               in_denotational_sem_goal (Fresh fg) f
| dsgInvoke : forall r t f (Hbody : in_denotational_sem_goal (proj1_sig (OperationalSem.P r) t) f),
                           in_denotational_sem_goal (Invoke r t) f.

Hint Constructors in_denotational_sem_goal.

(**)

(* Variant with levels * )

Inductive in_denotational_sem_with_env (env_in : name -> term -> gt_fun -> Prop) : gt_fun ->
                                                                                     goal ->
                                                                                     Prop :=
| dsEnvUnify  : forall f t1 t2 (UnH : apply_gt_fun f t1 = apply_gt_fun f t2),
                               in_denotational_sem_with_env env_in f (Unify t1 t2)
| dsEnvDisjL  : forall f g1 g2 (Hg : in_denotational_sem_with_env env_in f g1),
                               in_denotational_sem_with_env env_in f (Disj g1 g2)
| dsEnvDisjR  : forall f g1 g2 (Hg : in_denotational_sem_with_env env_in f g2),
                               in_denotational_sem_with_env env_in f (Disj g1 g2)
| dsEnvConj   : forall f g1 g2 (Hg1 : in_denotational_sem_with_env env_in f g1)
                               (Hg2 : in_denotational_sem_with_env env_in f g2),
                               in_denotational_sem_with_env env_in f (Conj g1 g2)
| dsEnvFresh  : forall f fn a fg (fvH : forall n, ~ In a (fv_goal n (Fresh fg)))
                                 (Hg : in_denotational_sem_with_env env_in fn (fg a))
                                 (Hease : forall (x : name) (neq : x <> a), fn x = f x),
                                 in_denotational_sem_with_env env_in f (Fresh fg)
| dsEnvInvoke : forall r t f (Henv : env_in r t f),
                             in_denotational_sem_with_env env_in f (Invoke r t).

Inductive in_denotational_sem_lev : nat -> gt_fun -> goal -> Prop :=
| dsLev : forall lev f g (dsEnvH : in_denotational_sem_with_env (fun r t f => in_denotational_sem_lev lev f (proj1_sig (P r) t)) f g),
                         in_denotational_sem_lev (S lev) f g.

Definition in_denotational_sem (f : gt_fun) (g : goal) : Prop := exists lev, in_denotational_sem_lev lev f g.
( **)

Definition in_denotational_sem_subst (s : subst) (f : gt_fun) : Prop :=
  exists (f' : gt_fun), gt_fun_eq (subst_gt_fun_compose s f') f.

Inductive in_denotational_sem_state' : state' -> gt_fun -> Prop :=
| dsst'Leaf : forall g s n f (Hgoal : in_denotational_sem_goal g f)
                             (Hsubst : in_denotational_sem_subst s f),
                             in_denotational_sem_state' (Leaf g s n) f
| dsst'SumL : forall st1' st2' f (Hst1' : in_denotational_sem_state' st1' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'SumR : forall st1' st2' f (Hst2' : in_denotational_sem_state' st2' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'Prod : forall st' g f (Hgoal : in_denotational_sem_goal g f)
                             (Hst' : in_denotational_sem_state' st' f),
                             in_denotational_sem_state' (Prod st' g) f.

Hint Constructors in_denotational_sem_state'.

Inductive in_denotational_sem_state : state -> gt_fun -> Prop :=
| dsstState : forall st' f (Hst' : in_denotational_sem_state' st' f),
                           in_denotational_sem_state (State st') f.

Hint Constructors in_denotational_sem_state.

Definition in_denotational_analog (t : trace) (f : gt_fun) : Prop :=
  exists (s : subst) (n : nat), in_stream (Answer s n) t /\ in_denotational_sem_subst s f.

Lemma answer_correct
      (s : subst)
      (n : nat)
      (f : gt_fun)
      (HInDS : in_denotational_sem_subst s f)
      (st' : state')
      (st : state)
      (EV : eval_step st' (Answer s n) st) :
      in_denotational_sem_state' st' f.
Proof.
  remember (Answer s n) as l.
  induction EV; good_inversion Heql.
  2, 3: auto.
  destruct HInDS as [f' ff'_con].
  constructor.
  { constructor. red.
    specialize (gt_fun_eq_apply _ _ t1 ff'_con). intro. rewrite <- H.
    specialize (gt_fun_eq_apply _ _ t2 ff'_con). intro. rewrite <- H0.
    rewrite gt_fun_apply_compose. rewrite gt_fun_apply_compose.
    rewrite compose_correctness. rewrite compose_correctness.
    apply unify_unifies in u. rewrite u. reflexivity. }
  { red. exists (subst_gt_fun_compose s' f').
    red. intros. red.
    red in ff'_con. specialize (ff'_con x). red in ff'_con.
    rewrite <- ff'_con. unfold subst_gt_fun_compose.
    replace (fun x0 : name => apply_gt_fun f' (apply_subst s' (Var x0)))
      with (subst_gt_fun_compose s' f').
    2: reflexivity.
    rewrite gt_fun_apply_compose. rewrite compose_correctness.
    reflexivity. }
Qed.

Lemma next_state_correct
      (f : gt_fun)
      (st : state)
      (HInDS : in_denotational_sem_state st f)
      (st' : state')
      (wfState : well_formed_state' st')
      (h : label)
      (EV : eval_step st' h st) :
      in_denotational_sem_state' st' f.
Proof.
  induction EV; good_inversion HInDS.
  { good_inversion Hst'.
    { good_inversion Hst1'; constructor; auto. }
    { good_inversion Hst2'; constructor; auto. } }
  { good_inversion Hst'. good_inversion Hst'0. auto. }
  { good_inversion wfState. good_inversion Hst'.
    constructor; auto. econstructor; eauto.
    intros HIn. apply freshCorrect in HIn. omega. }
  { good_inversion Hst'. auto. }
  { auto. }
  { good_inversion wfState. good_inversion Hst'; auto. }
  { good_inversion Hst'. constructor; auto.
    eapply answer_correct; eauto. }
  { good_inversion wfState. good_inversion Hst'. auto. }
  { good_inversion wfState. good_inversion Hst'.
    { good_inversion Hst1'. constructor; auto.
      eapply answer_correct; eauto. }
    { good_inversion Hst2'. auto. } }
Qed.

Lemma search_correctness_generalized
      (st   : state)
      (wfSt : well_formed_state st)
      (f    : gt_fun)
      (t    : trace)
      (HOP  : op_sem st t)
      (HDA  : in_denotational_analog t f) :
      in_denotational_sem_state st f.
Proof.
  revert HOP wfSt. revert st.
  red in HDA. destruct HDA as [s [n [HInStr HInDS]]].
  remember (Answer s n) as l. induction HInStr.
  { intros. inversion HOP; clear HOP; subst.
    constructor. eapply answer_correct; eauto. }
  { specialize (IHHInStr Heql). intros.
    inversion HOP; clear HOP; subst.
    inversion wfSt; clear wfSt; subst.
    specialize (well_formedness_preservation _ _ _ EV wfState).
    intro wf_st0.
    specialize (IHHInStr st0 OP wf_st0).
    constructor. eapply next_state_correct; eauto. }
Qed.

Fixpoint first_nats (k : nat) : list nat :=
  match k with
  | 0   => []
  | S n => n :: first_nats n
  end.

Lemma first_nats_less (n k : nat) (H : In n (first_nats k)) : n < k.
Proof.
  induction k.
  { inversion H. }
  { inversion H. { omega. } { apply IHk in H0. omega. } }
Qed.

Lemma search_correctness
      (g   : goal)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g)
      (f   : gt_fun)
      (t   : trace)
      (HOP : op_sem (State (Leaf g empty_subst k)) t)
      (HDA : in_denotational_analog t f) : in_denotational_sem_goal g f.
Proof.
  remember (State (Leaf g empty_subst k)) as st.
  assert (in_denotational_sem_state st f).
  { eapply search_correctness_generalized; eauto.
    subst. constructor. constructor.
    intros. apply HC in H. apply first_nats_less. auto. }
  subst. inversion H. inversion Hst'. auto.
Qed.