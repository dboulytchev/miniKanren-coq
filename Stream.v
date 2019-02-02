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

  CoInductive in_stream : A -> stream -> Prop :=
  | inHead : forall x t, in_stream x (Cons x t)
  | inTail : forall x h t, in_stream x t -> in_stream x (Cons h t).

  Inductive finite : stream -> Prop :=
  | fNil : finite Nil
  | fCons : forall h t, finite t -> finite (Cons h t).

  Hint Constructors finite.

  CoInductive mix : stream -> stream -> stream -> Prop :=
  | mixNN : mix Nil Nil Nil
  | mixNC : forall h t, mix Nil (Cons h t) (Cons h t)
  | mixCN : forall h t, mix (Cons h t) Nil (Cons h t)
  | mixCCLeft  : forall h1 h2 t1 t2 s, mix t1 (Cons h2 t2) s ->
                                         mix (Cons h1 t1) (Cons h2 t2) (Cons h1 s)
  | mixCCRight : forall h1 h2 t1 t2 s, mix (Cons h1 t1) t2 s ->
                                         mix (Cons h1 t1) (Cons h2 t2) (Cons h2 s).

  Lemma mix_finite : forall s1 s2 s, mix s1 s2 s ->
                                             (finite s <-> finite s1 /\ finite s2).
  Proof.
    intros. split.
    * intros. generalize dependent H. revert s1 s2. induction H0.
      + intros. inversion H. split; auto.
      + intros. inversion H.
        - split; auto.
        - split; auto.
        - apply IHfinite in H4. destruct H4. split; auto.
        - apply IHfinite in H4. destruct H4. split; auto.
    * intros. destruct H0. generalize dependent H. revert s. induction H0.
      + intros. inversion H; subst; auto.
      + induction H1.
        - intros. inversion H. auto.
        - intros. inversion H; subst.
          { auto. }
          {
            constructor. apply IHfinite0.
            * intros.
              assert (finite (Cons h0 s)).
              { apply IHfinite. destruct t.
                * inversion H2; apply mixNC.
                * apply mixCCRight. assumption. }
              inversion H3. auto.
            * auto.
          }
  Qed.

  CoInductive interleave : stream -> stream -> stream -> Prop :=
  | interNil : forall s, interleave Nil s s
  | interCons : forall h t s rs, interleave s t rs ->
                                  interleave (Cons h t) s (Cons h rs).

  Lemma interleave_mix : forall s1 s2 s, interleave s1 s2 s -> mix s1 s2 s.
  Proof.
    assert (Gen: forall s1 s2 s : stream, interleave s1 s2 s \/ interleave s2 s1 s -> mix s1 s2 s).
    {
      cofix CIH. intros. destruct H.
      * inversion H.
        + destruct s; constructor.
        + destruct s2.
          - inversion H0. constructor.
          - apply mixCCLeft. apply CIH. auto.
      * inversion H.
        + destruct s; constructor.
        + destruct s1.
          - inversion H0. constructor.
          - apply mixCCRight. apply CIH. auto.
    }
    auto.
  Qed.

  Lemma interleave_in_1 : forall s1 s2 s, interleave s1 s2 s ->
                                         forall x, in_stream x s -> in_stream x s1 \/ in_stream x s2.
  Proof. admit. Admitted.

  Lemma interleave_in_2 : forall s1 s2 s, interleave s1 s2 s ->
                                         forall x, in_stream x s1 \/ in_stream x s2 -> in_stream x s.
  Proof.
    cofix CIH. intros. destruct H0.
    * inversion H0; subst.
      + inversion H. subst. constructor.
      + inversion H. subst. constructor. eapply CIH; eauto.
    * inversion H; subst.
      + auto.
      + constructor. eapply CIH; eauto.
  Qed.

  Lemma interleave_in : forall s1 s2 s, interleave s1 s2 s ->
                                         forall x, in_stream x s <-> in_stream x s1 \/ in_stream x s2.
  Proof.
    intros. split.
    * apply interleave_in_1. auto.
    * apply interleave_in_2. auto.
  Qed.

  Lemma interleave_finite : forall s1 s2 s, interleave s1 s2 s ->
                                             (finite s <-> finite s1 /\ finite s2).
  Proof. intros. apply mix_finite. apply interleave_mix. auto. Qed.

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

End Test.