Section Stream.

  Variable A : Set.

  CoInductive stream : Set :=
  | Nil : stream
  | Cons : A -> stream -> stream.

  Definition helper (s : stream) : stream :=
    match s with
    | Nil => Nil
    | Cons h t => Cons h t
    end.

  Lemma helper_eq : forall s, s = helper s.
  Proof. destruct s; reflexivity. Qed.

  CoInductive equal_streams : stream -> stream -> Prop :=
  | eqNil : equal_streams Nil Nil
  | eqCons : forall h1 h2 t1 t2, h1 = h2 ->
                                 equal_streams t1 t2 ->
                                 equal_streams (Cons h1 t1) (Cons h2 t2).

  Lemma equal_streams_symmetry : forall s1 s2, equal_streams s1 s2 -> equal_streams s2 s1.
  Proof.
    cofix CIH. intros. inversion H; subst.
    * constructor.
    * constructor. reflexivity. auto.
  Qed.

  Inductive in_stream : A -> stream -> Prop :=
  | inHead : forall x t, in_stream x (Cons x t)
  | inTail : forall x h t, in_stream x t -> in_stream x (Cons h t).

  Hint Constructors in_stream.

  Lemma in_equal_streams : forall s1 s2, equal_streams s1 s2 -> forall x, in_stream x s1 -> in_stream x s2.
  Proof.
    intros. revert H. revert s2. induction H0; intros; inversion_clear H; subst.
    * constructor.
    * constructor. eapply IHin_stream. assumption.
  Qed.

  Inductive finite : stream -> Prop :=
  | fNil : finite Nil
  | fCons : forall h t, finite t -> finite (Cons h t).

  Hint Constructors finite.

  CoInductive interleave : stream -> stream -> stream -> Prop :=
  | interNil : forall s s', equal_streams s s' -> interleave Nil s s'
  | interCons : forall h t s rs, interleave s t rs ->
                                  interleave (Cons h t) s (Cons h rs).

  Lemma interleave_in_1 : forall s1 s2 s, interleave s1 s2 s ->
                                         forall x, in_stream x s -> in_stream x s1 \/ in_stream x s2.
  Proof.
    intros. revert H. revert s1 s2. induction H0; intros.
    * inversion H.
      + right. inversion H0. subst. constructor.
      + left. constructor.
    * inversion H; subst.
      + right. inversion H1; subst. constructor. apply equal_streams_symmetry in H6. eapply in_equal_streams; eauto.
      + specialize (IHin_stream s2 t0 H4). destruct IHin_stream. { auto. } left. constructor. auto.
  Qed.

  Lemma interleave_in_2 : forall s1 s2 s, interleave s1 s2 s ->
                                         forall x, in_stream x s1 \/ in_stream x s2 -> in_stream x s.
  Proof.
    intros. destruct H0.
    * revert H. revert s2 s. induction H0.
      + intros. inversion_clear H; subst. constructor.
      + intros. inversion_clear H; subst. constructor. inversion_clear H1; subst.
        - eapply in_equal_streams; eauto.
        - constructor. eauto.
    * revert H. revert s1 s. induction H0.
      + intros. inversion H; subst.
        - eapply in_equal_streams; eauto.
        - constructor. inversion H0; subst. auto.
      + intros. inversion H; subst.
        - eapply in_equal_streams; eauto.
        - inversion H1; subst. constructor. constructor. eapply IHin_stream. eauto.
  Qed.

  Lemma interleave_in : forall s1 s2 s, interleave s1 s2 s ->
                                         forall x, in_stream x s <-> in_stream x s1 \/ in_stream x s2.
  Proof.
    intros. split.
    * apply interleave_in_1. auto.
    * apply interleave_in_2. auto.
  Qed.

  Lemma equal_streams_finite : forall s1 s2, equal_streams s1 s2 -> finite s1 -> finite s2.
  Proof.
    intros. revert H. revert s2. induction H0; intros; inversion H; subst; auto.
  Qed.

  Lemma interleave_finite_1 :
    forall s, finite s -> forall s1 s2, interleave s1 s2 s -> finite s1 /\ finite s2.
  Proof.
    intros s H. induction H.
    * intros. inversion H; subst. inversion H0. auto.
    * intros. inversion H0; subst.
      + inversion H1; subst. split; auto. constructor.
        apply equal_streams_symmetry in H6. eapply equal_streams_finite; eauto.
      + apply IHfinite in H4. destruct H4. auto.
  Qed.

  Lemma interleave_finite_2 :
    forall s1, finite s1 -> forall s2, finite s2 -> forall s, interleave s1 s2 s -> finite s.
  Proof.
    intros s1 H. induction H.
    * intros. inversion H0. eapply equal_streams_finite; eauto.
    * intros. inversion H1; subst. constructor. inversion H6; subst.
      + eapply equal_streams_finite; eauto.
      + inversion H0; subst. constructor. eapply IHfinite; eauto.
  Qed.

  Lemma interleave_finite : forall s1 s2 s, interleave s1 s2 s ->
                                             (finite s <-> finite s1 /\ finite s2).
  Proof.
    intros. split.
    * intro. eapply interleave_finite_1; eauto.
    * intro. destruct H0. apply interleave_finite_2 with (s1 := s1) (s2 := s2); auto.
  Qed.

End Stream.

Section Test.

  CoFixpoint nats (n : nat) : stream nat := Cons nat n (nats (S n)).
  Definition true_false : stream bool := Cons bool true (Cons bool false (Nil bool)).

  Lemma true_false_fin : finite bool true_false.
  Proof.
    constructor. constructor. constructor.
  Qed.

  Lemma nats_not_fin : forall n, ~ finite nat (nats n).
  Proof.
    intro. intro. remember (nats n). generalize dependent Heqs.
    revert n.
    induction H.
    - intros. rewrite helper_eq in Heqs. simpl in Heqs. inversion Heqs.
    - intros. apply IHfinite with (S n). rewrite helper_eq in Heqs. simpl in Heqs.
      inversion Heqs. reflexivity.
  Qed.

  Lemma nats_contain_all_nats : forall n, in_stream nat n (nats 0).
  Proof.
    induction n.
    * rewrite helper_eq. constructor.
    * remember (nats 0). remember 0. clear Heqn0.
      revert Heqs. revert n0. induction IHn.
      + intros. rewrite helper_eq in Heqs. inversion Heqs.
        constructor. rewrite helper_eq. constructor.
      + intros. constructor. rewrite helper_eq in Heqs.
        inversion Heqs; subst. eapply IHIHn. reflexivity.
  Qed.

End Test.