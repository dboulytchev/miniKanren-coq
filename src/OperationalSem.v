Require Import List.
(*Require Import Program.*)
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Stream.

(* Partial state *) 
Inductive state' : Set :=
(* (goal, subst, first free semantic variable) *) | Leaf : goal -> subst -> nat -> state'
(* sum of two states'                          *) | Sum  : state' -> state' -> state'
(* product of two states'                      *) | Prod : state' -> goal   -> state'.

(* Complete state *)
Inductive state : Set :=
(* end of evaluation *) | Stop  : state
(* a partial state   *) | State : state' -> state.

(* Labels *)
Inductive label : Set :=
(* nothing                                       *) | Step   : label
(* answer: (subst, first free semantic variable) *) | Answer : subst -> nat -> label.

Variable P : spec.

(*
Definition well_formed_goal : goal -> Set :=
| wfUnify  : forall t1 t2, well_formed_goal (Unify t1 t2)
| wfDisj   : forall g1 g2, well_formed_goal g1 -> well_formed_goal g2 -> well_formed_goal (Disj g1 g2)
| wfConj   : forall g1 g2, well_formed_goal g1 -> well_formed_goal g2 -> well_formed_goal (Conj g1 g2)
| wfFresh  : forall fg, (forall n, well_formed_goal (fg n)) -> well_formed_goal (Fresh fg)
| wfInvoke : forall f arg, {r & {cl & find (fun x => Nat.eqb (fst x) f) P = Some (f, Def r cl)}} ->
                           well_formed_goal (Invoke f arg).

Hint Constructors well_formed_goal.

Variable P_well_formed : forall f r cl arg, In (f, Def r cl) P -> well_formed_goal (r arg).

Inductive well_formed_state' : state' -> Set :=
| wfLeaf : forall g s n,     well_formed_goal g ->
                             well_formed_state' (Leaf g s n)
| wfSum  : forall st'1 st'2, well_formed_state' st'1 ->
                             well_formed_state' st'2 ->
                             well_formed_state' (Sum st'1 st'2)
| wfProd : forall st' g,     well_formed_state' st' ->
                             well_formed_goal g ->
                             well_formed_state' (Prod st' g).

Hint Constructors well_formed_state'.

Inductive well_formed_state : state -> Set :=
| wfEmpty    : well_formed_state Stop
| wfNonEmpty : forall st', well_formed_state' st' -> well_formed_state (State st').

Hint Constructors well_formed_state.
*)

(* Transitions *)
Inductive eval_step : state' -> label -> state -> Set :=
| FailS        : forall           s    n, eval_step (Leaf Fail s n) Step Stop
| UnifyFail    : forall t1 t2     s    n, unify (apply_subst s t1) (apply_subst s t2) None      -> eval_step (Leaf (Unify t1 t2) s n) Step Stop
| UnifySuccess : forall t1 t2     s s' n, unify (apply_subst s t1) (apply_subst s t2) (Some s') -> eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s' s) n) Stop
| DisjS        : forall g1 g2     s    n, eval_step (Leaf (Disj g1 g2) s n) Step (State (Sum (Leaf g1 s n) (Leaf g2 s n)))
| ConjS        : forall g1 g2     s    n, eval_step (Leaf (Conj g1 g2) s n) Step (State (Prod (Leaf g1 s n) g2))
| FreshS       : forall fg        s    n, eval_step (Leaf (Fresh fg) s n)   Step (State (Leaf (fg n) s (S n)))
| InvokeS      : forall r arg     s    n, eval_step (Leaf (Invoke r arg) s n) Step (State (Leaf (proj1_sig (P r) arg) s n))
| SumE         : forall st1 st2        l (H: eval_step st1 l  Stop), eval_step (Sum st1 st2) l (State st2)
| SumNE        : forall st1 st1' st2   l, eval_step st1 l (State st1')             -> eval_step (Sum st1 st2) l (State (Sum st2 st1'))
| ProdSE       : forall st g            , eval_step st     Step         Stop       -> eval_step (Prod st g) Step Stop
| ProdAE       : forall st g s n        , eval_step st    (Answer s n)  Stop       -> eval_step (Prod st g) Step (State (Leaf g s n))
| ProdSNE      : forall st g     st'    , eval_step st     Step        (State st') -> eval_step (Prod st g) Step (State (Prod st' g))
| ProdANE      : forall st g s n st'    , eval_step st    (Answer s n) (State st') -> eval_step (Prod st g) Step (State (Sum (Leaf g s n) (Prod st' g))).

Hint Constructors eval_step.

(*
Lemma well_formedness_preservation :
  forall (st' : state') (l : label) (st : state),
    eval_step st' l st -> well_formed_state' st' -> well_formed_state st.
Proof.
  intros. induction H.
  1,2,9 : auto.
  1-3: inversion H0; inversion H1; auto.
  * apply find_some in e. destruct e.
    constructor. constructor. eapply P_well_formed. eauto.
  * inversion H0; subst; auto.
  * inversion H0; subst; apply IHeval_step in H3; inversion H3; auto.
  * inversion H0; subst; auto.
  * inversion H0; subst; apply IHeval_step in H3; inversion H3; auto.
  * inversion H0; subst; apply IHeval_step in H3; inversion H3; auto.
Qed.
*)

Lemma eval_step_exists : forall (st' : state'), {l : label & {st : state & eval_step st' l st}}.
Proof.
  induction st'.
  * destruct g.
    1,3-6: repeat eexists; econstructor.
    + assert ({r & unify (apply_subst s t) (apply_subst s t0) r}). { apply unify_exists. }
      destruct H. destruct x.
      all: repeat eexists; eauto.
  * destruct IHst'1 as [l1 [st1 IH1]]. destruct st1.
    all: repeat eexists; eauto.
  * destruct IHst' as [l [st IH]]. destruct st; destruct l.
    all: repeat eexists; eauto.
Qed.

Lemma eval_step_unique :
  forall (st' : state') (l1 l2 : label) (st1 st2 : state),
    eval_step st' l1 st1 -> eval_step st' l2 st2 -> l1 = l2 /\ st1 = st2.
Proof.
  induction st'.
  * intros. destruct g; inversion H; inversion H0; subst; auto.
    + assert (C : None = Some s').
      { eapply unify_unique; eassumption. }
      inversion C.
    + assert (C : None = Some s').
      { eapply unify_unique; eassumption. }
      inversion C.
    + assert (C : Some s' = Some s'0).
      { eapply unify_unique; eassumption. }
      inversion C. auto.
  * intros. inversion H; inversion H0; subst;
    specialize (IHst'1 _ _ _ _ H5 H10); inversion IHst'1;
    inversion H2; subst; auto.
  * intros. inversion H; inversion H0; subst;
    specialize (IHst' _ _ _ _ H5 H10); inversion IHst'; subst;
    inversion H1; inversion H2; auto.
Qed.

(* Traces *)
Definition trace : Set := @stream label.

CoInductive op_sem : state -> trace -> Set :=
| osStop : op_sem Stop Nil
| osState : forall st' l st t (EV: eval_step st' l st)
                              (OP: op_sem st t),
                              op_sem (State st') (Cons l t).

Hint Constructors op_sem.

CoFixpoint trace_from (st : state) : trace :=
  match st with
  | Stop => Nil
  | State st' =>
    match eval_step_exists st' with
    | existT _ l (existT _ st'' ev_st'_st'') =>
      Cons l (trace_from st'')
    end
  end.

Lemma trace_from_correct : forall st, op_sem st (trace_from st).
Proof.
  cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl. destruct (eval_step_exists s).
    destruct s0. econstructor. eauto. eauto. }
Qed.

Lemma op_sem_exists (st : state) : {t : trace & op_sem st t}.
Proof.
  eexists. eapply trace_from_correct.
Qed.

Lemma op_sem_unique :
  forall st t1 t2, op_sem st t1 -> op_sem st t2 -> equal_streams t1 t2.
Proof.
  cofix CIH. intros. inversion H; inversion H0;
  rewrite <- H1 in H3; inversion H3.
  * constructor.
  * subst.
    specialize (eval_step_unique _ _ _ _ _ EV EV0).
    intro. destruct H1. constructor.
    + auto.
    + subst. eapply CIH; eauto.
Qed.

Lemma sum_op_sem : forall st'1 st'2 t1 t2 t, op_sem (State st'1) t1 ->
                                             op_sem (State st'2) t2 ->
                                             op_sem (State (Sum st'1 st'2)) t ->
                                             interleave t1 t2 t.
Proof.
  cofix CIH. intros. inversion H. subst. inversion H1. subst.
  inversion EV0; subst; specialize (eval_step_unique _ _ _ _ _ EV H6);
  intro; destruct H2; subst; constructor.
  * inversion OP. subst. specialize (op_sem_unique _ _ _ H0 OP0).
    intro. inversion H2; subst.
    + constructor. constructor.
    + constructor. constructor. auto.
  * eapply CIH; eassumption.
Qed.

Lemma disjunction_finite_commutativity :
  forall g1 g2 s n t12 t21
    (ops11 : op_sem (State (Leaf (Disj g1 g2) s n)) t12)
    (ops21 : op_sem (State (Leaf (Disj g2 g1) s n)) t21)
    (fin12 : finite t12), finite t21.
Proof.
  intros.
  inversion ops11; subst.
  inversion EV; subst.
  inversion fin12; subst.
  inversion ops21; subst.
  inversion EV0; subst.
  constructor.
  specialize (op_sem_exists (State (Leaf g1 s n))). intro. destruct H as [t1 OP1].
  specialize (op_sem_exists (State (Leaf g2 s n))). intro. destruct H as [t2 OP2].
  specialize (sum_op_sem _ _ _ _ _ OP1 OP2 OP). intro.
  specialize (sum_op_sem _ _ _ _ _ OP2 OP1 OP0). intro.
  specialize (interleave_finite _ _ _ H). intro.
  specialize (interleave_finite _ _ _ H1). intro.
  apply H3. apply and_comm. apply H2. auto.
Qed.
