Add LoadPath "~/JB/minikanren-coq/src/".

Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Stream.
Require Import Omega.
Require Import Extraction.

(* Complete state *)
Inductive cutting_mark : Set :=
| StopCutting : cutting_mark
| KeepCutting : cutting_mark.

(* Partial state *) 
Inductive state' : Set :=
(* (goal, subst, first free semantic variable)   *) | Leaf : goal -> subst -> nat -> state'
(* sum of two states' with a 'stop cutting' flag *) | Sum  : cutting_mark -> state' -> state' -> state'
(* product of two states'                        *) | Prod : state' -> goal   -> state'.

(* Complete state *)
Inductive state : Set :=
(* end of evaluation *) | Stop  : state
(* a partial state   *) | State : state' -> state.

Inductive is_fv_of_state' : name -> state' -> Prop :=
| isfvst'Leaf  : forall x g s n       (X_FV_G : is_fv_of_goal x g),
                                      is_fv_of_state' x (Leaf g s n)
| isfvst'SumL  : forall x m st'1 st'2 (X_FV : is_fv_of_state' x st'1),
                                      is_fv_of_state' x (Sum m st'1 st'2)
| isfvst'SumR  : forall x m st'1 st'2 (X_FV : is_fv_of_state' x st'2),
                                      is_fv_of_state' x (Sum m st'1 st'2)
| isfvst'ProdL : forall x st' g       (X_FV : is_fv_of_state' x st'),
                                      is_fv_of_state' x (Prod st' g)
| isfvst'ProdR : forall x st' g       (X_FV : is_fv_of_goal x g),
                                      is_fv_of_state' x (Prod st' g).

Hint Constructors is_fv_of_state'.

Inductive is_fv_of_state : name -> state -> Prop :=
| isfvstC : forall x st' (X_FV_ST' : is_fv_of_state' x st'),
                         is_fv_of_state x (State st').

Hint Constructors is_fv_of_state.

Inductive is_counter_of_state' : nat -> state' -> Prop :=
| iscst'Leaf  : forall g s n,        is_counter_of_state' n (Leaf g s n)
| iscst'SumL  : forall n m st'1 st'2 (ISC : is_counter_of_state' n st'1),
                                     is_counter_of_state' n (Sum m st'1 st'2)
| iscst'SumR  : forall n m st'1 st'2 (ISC : is_counter_of_state' n st'2),
                                     is_counter_of_state' n (Sum m st'1 st'2)
| iscst'Prod  : forall n st' g       (ISC : is_counter_of_state' n st'),
                                     is_counter_of_state' n (Prod st' g).

Hint Constructors is_counter_of_state'.

Inductive well_formed_state' : state' -> Set :=
| wfLeaf : forall g s frn   (DOM_LT_COUNTER :  forall x (X_IN_DOM : in_subst_dom s x),
                                                        x < frn)
                            (VRAN_LT_COUNTER : forall x (X_IN_VRAN : in_subst_vran s x),
                                                        x < frn)
                            (FV_LT_COUNTER :   forall x (X_FV : is_fv_of_goal x g),
                                                        x < frn),
                            well_formed_state' (Leaf g s frn)
| wfSum  : forall m st'1 st'2 (WF_L : well_formed_state' st'1)
                              (WF_R : well_formed_state' st'2),
                              well_formed_state' (Sum m st'1 st'2)
| wfProd : forall st' g (WF_L : well_formed_state' st')
                        (FV_LT_COUNTER : forall x frn (FRN_COUNTER : is_counter_of_state' frn st')
                                                      (X_FV : is_fv_of_goal x g),
                                                      x < frn),
                        well_formed_state' (Prod st' g).

Hint Constructors well_formed_state'.

Inductive well_formed_state : state -> Set :=
| wfEmpty    : well_formed_state Stop
| wfNonEmpty : forall st' (wfState : well_formed_state' st'),
                          well_formed_state (State st').

Hint Constructors well_formed_state.

(* Labels *)
Inductive label : Set :=
(* nothing                                       *) | Step   : label
(* answer: (subst, first free semantic variable) *) | Answer : subst -> nat -> label.

Inductive cut_signal : Set :=
| NoCutting  : cut_signal
| YesCutting : cut_signal.

(* Transitions *)
Inductive eval_step_SLD : state' -> label -> cut_signal -> state -> Set :=
| esFail         : forall           s    n, eval_step_SLD (Leaf Fail s n) Step NoCutting Stop
| esCut          : forall           s    n, eval_step_SLD (Leaf Cut s n)  (Answer s n) YesCutting Stop
| esUnifyFail    : forall t1 t2     s    n  (MGU : mgu (apply_subst s t1) (apply_subst s t2) None),
                                            eval_step_SLD (Leaf (Unify t1 t2) s n) Step NoCutting Stop
| esUnifySuccess : forall t1 t2     s s' n  (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some s')),
                                            eval_step_SLD (Leaf (Unify t1 t2) s n) (Answer (compose s s') n) NoCutting Stop
| esDisj         : forall g1 g2     s    n, eval_step_SLD (Leaf (Disj g1 g2) s n) Step NoCutting (State (Sum StopCutting (Leaf g1 s n) (Leaf g2 s n)))
| esConj         : forall g1 g2     s    n, eval_step_SLD (Leaf (Conj g1 g2) s n) Step NoCutting (State (Prod (Leaf g1 s n) g2))
| esFresh        : forall fg        s    n, eval_step_SLD (Leaf (Fresh fg) s n)   Step NoCutting (State (Leaf (fg n) s (S n)))
| esInvoke       : forall r arg     s    n, eval_step_SLD (Leaf (Invoke r arg) s n) Step NoCutting (State (Leaf (proj1_sig (MiniKanrenSyntax.P r) arg) s n))
| esSumE         : forall st1 m      st2 l  (STEP_L : eval_step_SLD st1 l NoCutting Stop),
                                            eval_step_SLD (Sum m st1 st2) l NoCutting (State st2)
| esSumECS       : forall st1        st2 l  (STEP_L : eval_step_SLD st1 l YesCutting Stop),
                                            eval_step_SLD (Sum StopCutting st1 st2) l NoCutting Stop
| esSumECK       : forall st1        st2 l  (STEP_L : eval_step_SLD st1 l YesCutting Stop),
                                            eval_step_SLD (Sum KeepCutting st1 st2) l YesCutting Stop
| esSumNE        : forall st1 m st1' st2 l  (STEP_L : eval_step_SLD st1 l NoCutting (State st1')),
                                            eval_step_SLD (Sum m st1 st2) l NoCutting (State (Sum m st1' st2))
| esSumNEC       : forall st1   st1' st2 l  (STEP_L : eval_step_SLD st1 l YesCutting (State st1')),
                                            eval_step_SLD (Sum StopCutting st1 st2) l NoCutting (State st1')
| esSumNEK       : forall st1   st1' st2 l  (STEP_L : eval_step_SLD st1 l YesCutting (State st1')),
                                            eval_step_SLD (Sum KeepCutting st1 st2) l YesCutting (State st1')
| esProdSE       : forall st g     cs       (STEP_L : eval_step_SLD st Step cs Stop),
                                            eval_step_SLD (Prod st g) Step cs Stop
| esProdAE       : forall st g s n cs       (STEP_L : eval_step_SLD st (Answer s n) cs Stop),
                                            eval_step_SLD (Prod st g) Step cs (State (Leaf g s n))
| esProdSNE      : forall st g     cs st'   (STEP_L : eval_step_SLD st Step cs (State st')),
                                            eval_step_SLD (Prod st g) Step cs (State (Prod st' g))
| esProdANE      : forall st g s n cs st'   (STEP_L : eval_step_SLD st (Answer s n) cs (State st')),
                                            eval_step_SLD (Prod st g) Step cs (State (Sum KeepCutting (Leaf g s n) (Prod st' g))).

Hint Constructors eval_step_SLD.

Lemma counter_in_answer
      (st' : state')
      (s : subst)
      (n : nat)
      (cs : cut_signal)
      (st : state)
      (EV : eval_step_SLD st' (Answer s n) cs st) :
      is_counter_of_state' n st'.
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; auto.
Qed.

Lemma counter_in_next_state
      (n : nat)
      (st' st'_next : state')
      (l : label)
      (cs : cut_signal)
      (EV : eval_step_SLD st' l cs (State st'_next))
      (ISC_NEXT :  is_counter_of_state' n st'_next) :
      exists n', n' <= n /\ is_counter_of_state' n' st'.
Proof.
  remember (State st'_next) as st.
  revert Heqst ISC_NEXT. revert st'_next.
  induction EV; intros; good_inversion Heqst.
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { good_inversion ISC_NEXT. exists n0. split.
    { repeat constructor. }
    { auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; auto. } }
  { exists n. split.
    { constructor. }
    { auto. } }
  { specialize (IHEV st1' eq_refl). good_inversion ISC_NEXT.
    { apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
      exists n'; auto. }
    { exists n. split.
      { constructor. }
      { auto. } } }
  { destruct (IHEV st'_next eq_refl ISC_NEXT) as [n' [LE ISC]].
    exists n'; auto. }
  { destruct (IHEV st'_next eq_refl ISC_NEXT) as [n' [LE ISC]].
    exists n'; auto. }
  { good_inversion ISC_NEXT. exists n0.
    eapply counter_in_answer in EV. split; auto. }
  { specialize (IHEV st' eq_refl). good_inversion ISC_NEXT.
    apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
    exists n'; auto. }
  { specialize (IHEV st' eq_refl). good_inversion ISC_NEXT.
    { good_inversion ISC. exists n0.
      eapply counter_in_answer in EV. split; auto. }
    { good_inversion ISC. apply IHEV in ISC0.
      destruct ISC0 as [n' [LE ISC]]. exists n'; auto. } }
Qed.

Lemma well_formed_subst_in_answer
      (st' : state')
      (s : subst)
      (n : nat)
      (cs : cut_signal)
      (st : state)
      (EV : eval_step_SLD st' (Answer s n) cs st)
      (WF : well_formed_state' st') :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; good_inversion WF; auto.
  assert (FV_LT_N_1 : forall x, In x (fv_term (apply_subst s0 t1)) -> x < n).
  { clear MGU s'. intros. induction t1.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt1_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt1_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. right. auto. } } }
  assert (FV_LT_N_2 : forall x, In x (fv_term (apply_subst s0 t2)) -> x < n).
  { clear MGU s'. intros. induction t2.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt2_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt2_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. right. auto. } } }
  specialize (mgu_dom _ _ _ MGU). intro S'_DOM.
  specialize (mgu_vran _ _ _ MGU). intro S'_VRAN.
  split.
  { intros. apply compose_dom in H. destruct H; auto.
    apply S'_DOM in H. destruct H; auto. }
  { intros. apply compose_vran in H. destruct H; auto.
    apply S'_VRAN in H. destruct H; auto. }
Qed.

Lemma well_formedness_preservation
      (st' : state')
      (l : label)
      (cs : cut_signal)
      (st : state)
      (EV : eval_step_SLD st' l cs st)
      (WF : well_formed_state' st') :
      well_formed_state st.
Proof.
  intros. induction EV; good_inversion WF; auto.
  { constructor. auto. }
  { constructor. constructor; auto.
    intros. good_inversion FRN_COUNTER. subst. auto. }
  { constructor. constructor.
    1-2: intros; eapply lt_trans; eauto.
    intros. destruct (eq_nat_dec n x).
    { omega. }
    { apply Nat.lt_lt_succ_r. apply FV_LT_COUNTER. econstructor; eauto. } }
  { constructor. constructor; auto.
    specialize (proj2_sig (MiniKanrenSyntax.P r)). intro CC.
    simpl in CC. destruct CC as [CL _]. red in CL. red in CL. auto. }
  { specialize (IHEV WF_L).
    good_inversion IHEV. auto. }
  { constructor. constructor.
    1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
    intros. apply FV_LT_COUNTER; auto. eapply counter_in_answer; eauto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor; auto. intros.
    eapply counter_in_next_state in EV; eauto.
    destruct EV as [frn' [LE ISC]]. eapply lt_le_trans.
    2: eauto.
    auto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor.
    { constructor.
      1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
      intros. apply FV_LT_COUNTER; auto.
      eapply counter_in_answer; eauto. }
    { constructor; auto. intros.
      eapply counter_in_next_state in EV; eauto.
      destruct EV as [frn' [Le ISC]]. eapply lt_le_trans.
      2: eauto.
      auto. } }
Qed.

Lemma eval_step_SLD_exists
      (st' : state') :
      {l : label & {cs : cut_signal & {st : state & eval_step_SLD st' l cs st}}}.
Proof.
  induction st'.
  { destruct g.
    1-2,4-7: repeat eexists; econstructor.
    { assert ({r & mgu (apply_subst s t) (apply_subst s t0) r}).
      { apply mgu_exists. }
      destruct H. destruct x.
      all: repeat eexists; eauto. } }
  { destruct IHst'1 as [l1 [cs [st1 IH1]]].
    destruct st1; destruct cs; destruct c.
    all: repeat eexists; eauto. }
  { destruct IHst' as [l [cs [st IH]]].
    destruct st; destruct l.
    all: repeat eexists; eauto. }
Qed.

Lemma eval_step_unique
      (st' : state')
      (l1 l2 : label)
      (cs1 cs2 : cut_signal)
      (st1 st2 : state)
      (STEP_1 : eval_step_SLD st' l1 cs1 st1)
      (STEP_2 : eval_step_SLD st' l2 cs2 st2) :
      l1 = l2 /\ cs1 = cs2 /\ st1 = st2.
Proof.
  revert STEP_1 STEP_2. revert l1 l2 cs1 cs2 st1 st2. induction st'.
  { intros. destruct g; good_inversion STEP_1; good_inversion STEP_2; auto.
    { assert (C : None = Some s').
      { eapply mgu_unique; eassumption. }
      inversion C. }
    { assert (C : None = Some s').
      { eapply mgu_unique; eassumption. }
      inversion C. }
    { assert (C : Some s' = Some s'0).
      { eapply mgu_unique; eassumption. }
      inversion C. auto. } }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    destruct (IHst'1 _ _ _ _ _ _ STEP_L STEP_L0) as [EQL [EQCS EQST]];
    inversion EQCS; inversion EQST; subst; auto. }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    destruct (IHst' _ _ _ _ _ _ STEP_L STEP_L0) as [EQL [EQCS EQST]];
    inversion EQL; inversion EQCS; inversion EQST; auto. }
Qed.

(* Traces *)
Definition trace : Set := @stream label.

CoInductive op_sem_SLD : state -> trace -> Set :=
| osStop : op_sem_SLD Stop Nil
| osState : forall st' l cs st t (EV: eval_step_SLD st' l cs st)
                                 (OP: op_sem_SLD st t),
                                 op_sem_SLD (State st') (Cons l t).

Hint Constructors op_sem_SLD.

CoFixpoint trace_from (st : state) : trace :=
  match st with
  | Stop => Nil
  | State st' =>
    match eval_step_SLD_exists st' with
    | existT _ l (existT _ _ (existT _ st'' ev_st'_st'')) =>
      Cons l (trace_from st'')
    end
  end.

Lemma trace_from_correct
      (st : state) :
      op_sem_SLD st (trace_from st).
Proof.
  revert st. cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl.
    destruct (eval_step_SLD_exists s) as [l [cs [st EV]]].
    econstructor; eauto. }
Qed.

Lemma op_sem_SLD_exists
      (st : state) :
      {t : trace & op_sem_SLD st t}.
Proof.
  eexists. eapply trace_from_correct.
Qed.

Extraction Language Haskell.

Extraction "Users/rozplokhas/JB/minikanren-coq/extracted/sld_interpreter.hs" op_sem_SLD_exists.

Lemma op_sem_unique
      (st : state)
      (t1 t2 : trace)
      (OP_1 : op_sem_SLD st t1)
      (OP_2 : op_sem_SLD st t2) :
      equal_streams t1 t2.
Proof.
  revert OP_1 OP_2. revert t1 t2 st.
  cofix CIH. intros. inversion OP_1; inversion OP_2;
  rewrite <- H1 in H; inversion H.
  { constructor. }
  { subst.
    destruct (eval_step_unique _ _ _ _ _ _ _ EV EV0) as [EQL [EQCS EQST]].
    constructor.
    { auto. }
    { subst. eapply CIH; eauto. } }
Qed.
