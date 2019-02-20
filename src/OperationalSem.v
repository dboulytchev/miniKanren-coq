Require Import List.
Require Import Program.
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

Inductive well_formed_goal : goal -> Set :=
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

(* Transitions *)
Inductive eval_step : state' -> label -> state -> Set :=
| UnifyFail    : forall t1 t2     s    n , unify (apply' s t1) (apply' s t2) None      -> eval_step (Leaf (Unify t1 t2) s n) Step Stop
| UnifySuccess : forall t1 t2     s s' n , unify (apply' s t1) (apply' s t2) (Some s') -> eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s' s) n) Stop
| DisjS        : forall g1 g2        s n , eval_step (Leaf (Disj g1 g2) s n) Step (State (Sum (Leaf g1 s n) (Leaf g2 s n)))
| ConjS        : forall g1 g2        s n , eval_step (Leaf (Conj g1 g2) s n) Step (State (Prod (Leaf g1 s n) g2))
| FreshS       : forall fg           s n , eval_step (Leaf (Fresh fg) s n)   Step (State (Leaf (fg n) s (S n)))

| InvokeS      : forall f arg r s n (cl : closed_rel r),
                   find (fun x => Nat.eqb (fst x) f) P = Some (f, Def r cl) ->
                   eval_step (Leaf (Invoke f arg) s n) Step (State (Leaf (r arg) s n))

| SumE         : forall st1 st2        l (H: eval_step st1 l  Stop), eval_step (Sum st1 st2) l (State st2)
| SumNE        : forall st1 st1' st2   l , eval_step st1 l (State st1')             -> eval_step (Sum st1 st2) l (State (Sum st2 st1'))
| ProdSE       : forall st g             , eval_step st     Step         Stop       -> eval_step (Prod st g) Step Stop
| ProdAE       : forall st g s n         , eval_step st    (Answer s n)  Stop       -> eval_step (Prod st g) Step (State (Leaf g s n))
| ProdSNE      : forall st g     st'     , eval_step st     Step        (State st') -> eval_step (Prod st g) Step (State (Prod st' g))
| ProdANE      : forall st g s n st'     , eval_step st    (Answer s n) (State st') -> eval_step (Prod st g) Step (State (Sum (Leaf g s n) (Prod st' g))).

Hint Constructors eval_step.

Lemma well_formedness_preservation :
  forall (st' : state') (l : label) (st : state),
    eval_step st' l st -> well_formed_state' st' -> well_formed_state st.
Proof.
  intros.
  (* generalize dependent Heqs. revert st'_next. *)
  induction H. (*; intros st'_next eq; inversion eq.*)
  1,2,9 : auto.
  1-3: inversion H0; inversion H1; auto.
  (* 2-6: inversion H0; subst; auto. *)
  * apply find_some in e. destruct e.
    constructor. constructor. eapply P_well_formed. eauto.
  * inversion H0; subst; auto.
  * inversion H0; subst; apply IHeval_step in H3; inversion H3; auto.
  * inversion H0; subst; auto.
  * inversion H0; subst; apply IHeval_step in H3; inversion H3; auto.
  * inversion H0; subst; apply IHeval_step in H3; inversion H3; auto.
Qed.

Lemma eval_step_exists : forall (st' : state'),
  well_formed_state' st' ->  {l : label & {st : state & eval_step st' l st}}.
Proof.
  intros st' wf_st'. induction st'.
  * destruct g.
    2-4: repeat eexists; econstructor.
    + assert ({r & unify (apply' s t) (apply' s t0) r}). { apply unify_exists. }
      destruct H. destruct x.
      all: repeat eexists; eauto.
    + inversion wf_st'. inversion H0.
      destruct H4. destruct s1.
      repeat eexists. eauto.
  * inversion wf_st'. specialize (IHst'1 H1).
    destruct IHst'1 as [l1 [st1 IH1]]. destruct st1.
    all: repeat eexists; eauto.
  * inversion wf_st'. specialize (IHst' H1).
    destruct IHst' as [l [st IH]]. destruct st; destruct l.
    all: repeat eexists; eauto.
Qed.

Lemma eval_step_unique :
  forall (st' : state') (l1 l2 : label) (st1 st2 : state),
    eval_step st' l1 st1 -> eval_step st' l2 st2 -> l1 = l2 /\ st1 = st2.
Proof.
  induction st'.
  * intros. destruct g; inversion H; inversion H0; subst.
    + auto.
    + assert (C : None = Some s').
      { eapply unify_unique; eassumption. }
      inversion C.
    + assert (C : None = Some s').
      { eapply unify_unique; eassumption. }
      inversion C.
    + assert (C : Some s' = Some s'0).
      { eapply unify_unique; eassumption. }
      inversion C. auto.
    + auto.
    + auto.
    + auto.
    + rewrite H14 in H7. inversion H7. auto.
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

(*
CoInductive wrapper : state -> Prop :=
| wrap : forall st t, op_sem st t -> wrapper st.

CoInductive coexists (A : Type) (P : A -> Prop) : Prop :=
  coex_intro : forall x : A, P x -> coexists A P.

Lemma coexists_exists (A : Type) (P : A -> Prop) (H : coexists A P) : exists x, P x.
Proof.
  inversion H. exists x. auto.
Qed.
*)

CoFixpoint trace_from (st : state) (Hwf : well_formed_state st) : trace :=
  match Hwf with
  | wfEmpty => Nil
  | wfNonEmpty st' wf' =>
    match eval_step_exists st' wf' with
    | existT _ l (existT _ st'' ev_st'_st'') =>
      Cons l (trace_from st'' (well_formedness_preservation st' l st'' ev_st'_st'' wf'))          
    end
  end.

CoFixpoint test (st : state) (Hwf : well_formed_state st) : op_sem st (trace_from st Hwf).
  refine (
  match Hwf in well_formed_state st'' return (st = st'' -> op_sem st (trace_from st'' Hwf)) with
  | wfEmpty            => fun H => _
  | wfNonEmpty st' wf' => fun H => _
  end eq_refl).
  { rewrite helper_eq. simpl. subst st. constructor. }
  rewrite helper_eq. simpl. destruct (eval_step_exists st' wf'). destruct s.
  subst st. econstructor. eauto.
  exact (test x0 (well_formedness_preservation st' x x0 e wf')).
Defined.

Lemma op_sem_exists (st : state) (wfs: well_formed_state st) : { t : trace & op_sem st t}.
Proof.
  eexists. eapply test. (H st H0).
Qed.

(*
  cofix CIH. 
  intros st H. inversion H.
  * apply coex_intro with (x:=Nil). constructor.
  * apply (eval_step_exists st') in H0. inversion H0. inversion H2.
    destruct x.
    + specialize (CIH Stop wfEmpty). apply coexists_exists in CIH. inversion CIH.  
      eapply coex_intro. inversion CIH. with (x:=Cons x0 x). econstructor; eauto.
    + inversion H.
      - subst st. inversion H4.
      - rewrite <-H5 in H1. inversion H1. subst st'0.
        apply (well_formedness_preservation st' s x0 H3) in H4.
        apply wfNonEmpty in H4. specialize (CIH (State s) H4). inversion CIH.
        apply coex_intro with (x:=Cons x0 x). econstructor; eauto.
Qed. *)

Lemma op_sem_unique :
  forall st t1 t2, op_sem st t1 -> op_sem st t2 -> equal_streams t1 t2.
Proof.
  cofix CIH. intros. inversion H; inversion H0.
  * constructor.
  * rewrite <- H1 in H5. inversion H5.
  * rewrite <- H3 in H5. inversion H5.
  * rewrite <- H3 in H7. inversion H7. rewrite H10 in H5.
    specialize (eval_step_unique st' l l0 st0 st1 H1 H5).
    intro. destruct H9. constructor.
    + assumption.
    + rewrite <- H11 in H6. apply CIH with st0; assumption.
Qed.

Lemma sum_op_sem : forall st'1 st'2 t1 t2 t, op_sem (State st'1) t1 ->
                                             op_sem (State st'2) t2 ->
                                             op_sem (State (Sum st'1 st'2)) t ->
                                             interleave t1 t2 t.
Proof.
  cofix CIH. intros. inversion H. subst. inversion H1. subst.
  inversion H5; subst; specialize (eval_step_unique _ _ _ _ _ H3 H10);
  intro; destruct H2; subst; constructor.
  * inversion H4. subst. specialize (op_sem_unique _ _ _ H0 H6).
    intro. inversion H2; subst.
    + constructor. constructor.
    + constructor. constructor. auto.
  * eapply CIH; eassumption.
Qed.
(*
Lemma disjunction_finite_commutativity :
  forall g1 g2 s n t12 t21,
    op_sem (State (Leaf (Disj g1 g2) s n)) t12 ->
    op_sem (State (Leaf (Disj g2 g1) s n)) t21 ->
    finite t12 -> finite t21.
Proof.
  intros.
  inversion H; subst.
  inversion H3; subst.
  inversion H0; subst.
  inversion H5; subst.
  inversion H1; subst.
  specialize (op_sem_exists (State (Leaf g1 s n))). intro. destruct H2.
  specialize (op_sem_exists (State (Leaf g2 s n))). intro. destruct H8
  specialize (sum_op_sem _ _ _ _ _ H2 H8 H4). intro.
  specialize (sum_op_sem _ _ _ _ _ H8 H2 H6). intro.
  constructor.
  specialize (interleave_finite _ _ _ H9). intro.
  specialize (interleave_finite _ _ _ H10). intro.
  apply H12. apply and_comm. apply H11. auto.
Qed. 
*)