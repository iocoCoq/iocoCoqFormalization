Require Import BE_semantics.
Require Import BE_syntax.
Require Import BE_trans_set.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Lists.ListSet.
Require Import list_helper.
Require Import String.

Fixpoint computeAllOutgoingTransitions_parallel
  (B1 B2 : ProcessBehaviour)
  (G G' : set EventName)
  (B1Trans B2Trans : BehaviourTransSet)
  : BehaviourTransSet :=
  match G' with
    | nil =>
        set_union
          BehaviourTransDec
          (map
            (fun t => (Parallel B1 G B2, transLabel t, Parallel (to t) G B2))
            B1Trans)
          (map
            (fun t => (Parallel B1 G B2, transLabel t, Parallel B1 G (to t)))
            B2Trans)
    | l :: tl =>
        let filter_label := fun t => match transLabel t with
                                       | InternalEvent => false
                                       | ExternalEvent e => eqb l e
                                     end in
        let (B1Trans', B1Trans'') := partition filter_label B1Trans in
        let (B2Trans', B2Trans'') := partition filter_label B2Trans in
        set_union
         BehaviourTransDec
         (computeAllOutgoingTransitions_parallel B1 B2 G tl B1Trans'' B2Trans'')
         (flat_map
           (fun t1 =>
             map
               (fun t2 =>
                 (Parallel B1 G B2, transLabel t1, Parallel (to t1) G (to t2)))
                 B2Trans')
           B1Trans')
  end.

Fixpoint computeAllOutgoingTransitions
  (B : ProcessBehaviour) (ctx : BehaviourExpressions) : BehaviourTransSet :=
    match B with
      | Prefix e B' => [(B, e, B')]
      | Choice (Values Bs) =>
          let convert_trans := fun t => (B, transLabel t, to t) in
          (fix expand_choice (l : list ProcessBehaviour) :=
            match l with
              | nil => nil
              | B' :: tl =>
                set_union
                  BehaviourTransDec
                  (map convert_trans
                    (computeAllOutgoingTransitions B' ctx))
                  (expand_choice tl)
            end) Bs
      | Parallel B1 G B2 =>
        let B1Trans := computeAllOutgoingTransitions B1 ctx in
        let B2Trans := computeAllOutgoingTransitions B2 ctx in
          computeAllOutgoingTransitions_parallel B1 B2 G G B1Trans B2Trans
      | Hide B' G =>
        let B'Trans := computeAllOutgoingTransitions B' ctx in
        let convertTrans := fun t =>
          match transLabel t with
            | InternalEvent => (B, InternalEvent, Hide (to t) G)
            | ExternalEvent e => if In_dec string_dec e G
                                 then (B, InternalEvent, Hide (to t) G)
                                 else (B, ExternalEvent e, Hide (to t) G)
          end in
          (fix expand_hide (trans : BehaviourTransSet) :=
            match trans with
              | nil => nil
              | t :: trans' => set_add
                                 BehaviourTransDec
                                 (convertTrans t)
                                 (expand_hide trans')
            end) B'Trans
      | ProcessInstantiation P =>
        match getProcessBehaviour P ctx with
          | Some B' => [(B, InternalEvent, B')]
          | None    => []
        end
    end.

Notation "'LETOPT' value <== expr 'IN' pattern"
   := (match expr with
         | Some value => pattern
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint createBehaviourTransSet'
  (ctx : BehaviourExpressions)
  (to_visit visited : set ProcessBehaviour)
  (i : nat) : option BehaviourTransSet :=
  match i with
   | 0 => None
   | S i' =>
      match to_visit with
        | nil => Some nil
        | B :: to_visit' =>
          let visited' := B :: visited in
          let from_B := computeAllOutgoingTransitions B ctx in
          let targets :=
            set_diff' ProcessBehaviourDec (targetBehaviours from_B) visited' in
          let to_visit'' := set_union ProcessBehaviourDec to_visit' targets in
          LETOPT result <== createBehaviourTransSet' ctx to_visit'' visited' i' IN
            Some (result ++ from_B)
      end
  end.

Definition createBehaviourTransSet
  (ctx : BehaviourExpressions)
  (startProcess : ProcessName)
  (i : nat)
  : option BehaviourTransSet :=
    LETOPT B <== getProcessBehaviour startProcess ctx IN
      createBehaviourTransSet' ctx [B] [] i.

Lemma changeInductionSet :
  forall (B1 B2 : ProcessBehaviour)
         (G G' : set EventName)
         (B1Trans B2Trans : BehaviourTransSet),
    G = G' ->
    computeAllOutgoingTransitions_parallel B1 B2 G G B1Trans B2Trans =
    computeAllOutgoingTransitions_parallel B1 B2 G G' B1Trans B2Trans.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma computeAllOutgoingTransitions_onlyTransFromB :
forall (B : ProcessBehaviour) (ctx : BehaviourExpressions) (t : BehaviourTrans),
  In t (computeAllOutgoingTransitions B ctx) -> from t = B.
Proof.
  intros.
  destruct B.
  - simpl in H. destruct H; inversion H. reflexivity.
  - simpl in H. destruct c. remember s as s'. assert (Values s' = Values s).
      { rewrite Heqs'. reflexivity. }
      rewrite H0 in H. rewrite H0. clear H0 Heqs'. induction s'.
    + inversion H.
    + apply set_union_elim in H. destruct H.
      * unfold set_In in H. apply in_map_iff in H. destruct H. destruct H.
        rewrite <- H. reflexivity.
      * apply IHs'. apply H.
  - simpl in H.
    remember s as s'. rewrite changeInductionSet with (G' := s) in H; auto.
    clear Heqs'.
    remember (computeAllOutgoingTransitions B1 ctx) as l1.
    remember (computeAllOutgoingTransitions B2 ctx) as l2.
    clear Heql1 Heql2. generalize dependent l2. generalize dependent l1.
    induction s; intros.
    + simpl in H. apply set_union_iff in H. destruct H;
      apply in_map_iff in H; destruct H as [x [H H']]; rewrite <- H;
      unfold from; reflexivity.
    + simpl in H.
      destruct (partition
                 (fun t : BehaviourTrans =>
                  match transLabel t with
                  | InternalEvent => false
                  | ExternalEvent e => (a =? e)%string
                  end) l1).
      destruct (partition
                 (fun t : BehaviourTrans =>
                  match transLabel t with
                  | InternalEvent => false
                  | ExternalEvent e => (a =? e)%string
                  end) l2).
      apply set_union_iff in H. destruct H.
      * apply IHs with (l1 := l0) (l2 := l4); auto.
      * apply in_flat_map in H. destruct H as [x [_ H]].
        apply in_map_iff in H. destruct H as [x' [H _]]. rewrite <- H.
        unfold from. reflexivity.
  - simpl in H.
    induction (computeAllOutgoingTransitions B ctx).
    + inversion H.
    + apply set_add_elim in H. destruct H.
      * destruct (transLabel a); [| destruct (in_dec string_dec e s)];
        rewrite H; unfold from; reflexivity.
      * apply IHb; auto.
  - simpl in H. destruct (getProcessBehaviour p ctx); destruct H; inversion H.
    unfold from. reflexivity.
Qed.

Lemma computeAllOutgoingTransitions_parallel_elim:
  forall (B1 B2 B' : ProcessBehaviour) (e : Event) (G G' : set EventName)
    (l1 l2 : list BehaviourTrans),
    In (Parallel B1 G' B2, e, B')
      (computeAllOutgoingTransitions_parallel B1 B2 G' G l1 l2) ->
    exists t, (In t l1 \/ In t l2) /\ transLabel t = e.
Proof.
  intros B1 B2 B' e G G'. induction G.
  - intros l1 l2 H. simpl in H. apply set_union_iff in H. destruct H;
    apply in_map_iff in H; destruct H as [x [H H']]; exists x;
    inversion H; split; auto.
  - intros. simpl in H.
    destruct (partition
               (fun t : BehaviourTrans =>
                match transLabel t with
                | InternalEvent => false
                | ExternalEvent e => (a =? e)%string
                end) l1) eqn:H'.
    destruct (partition
               (fun t : BehaviourTrans =>
                match transLabel t with
                | InternalEvent => false
                | ExternalEvent e => (a =? e)%string
                end) l2) eqn:H''.
    apply set_union_iff in H. destruct H.
    + apply IHG in H. destruct H as [x [H]]. exists x. split; auto.
      destruct H.
      * assert (Hp : snd (l, l0) = l0). { reflexivity. }
        rewrite <- H' in Hp. rewrite <- Hp in H. apply partition_elim1 in H.
        destruct H. left. apply H.
      * assert (Hp : snd (l3, l4) = l4). { reflexivity. }
        rewrite <- H'' in Hp. rewrite <- Hp in H. apply partition_elim1 in H.
        destruct H. right. apply H.
    + apply in_flat_map in H. destruct H as [x [H]].
      apply in_map_iff in H0. destruct H0 as [x0 [H0]].
      inversion H0. exists x. split; auto.
      assert (Hp : fst (l, l0) = l). { reflexivity. }
      rewrite <- H' in Hp. rewrite <- Hp in H. apply partition_elim2 in H.
      destruct H. left. apply H.
Qed.

Lemma computeAllOutgoingTransitions_parallel_correct:
  forall (B1 B2 B' : ProcessBehaviour) (e : Event) (G : set EventName)
         (l1 l2 : BehaviourTransSet) (ctx : BehaviourExpressions),
    (forall (B' : ProcessBehaviour) (e' : Event),
      In (B1, e', B') (computeAllOutgoingTransitions B1 ctx) ->
      ctx # B1 // e' --> B') ->
    (forall (B' : ProcessBehaviour) (e' : Event),
      In (B2, e', B') (computeAllOutgoingTransitions B2 ctx) ->
      ctx # B2 // e' --> B') ->
    (forall x, In x l1 -> In x (computeAllOutgoingTransitions B1 ctx)) ->
    (forall x, In x l2 -> In x (computeAllOutgoingTransitions B2 ctx)) ->
    In (Parallel B1 G B2, e, B')
       (computeAllOutgoingTransitions_parallel B1 B2 G G l1 l2) ->
    ctx # Parallel B1 G B2 // e --> B'.
Proof.
  intros B1 B2 B' e G l1 l2 ctx IHB1 IHB2 Hl1 Hl2 H.
  remember G as G'. rewrite changeInductionSet with (G' := G) in H; auto.
  destruct e.
  - clear HeqG'. generalize dependent l1. generalize dependent l2.
    induction G; intros.
    + simpl in H. apply set_union_iff in H. destruct H as [H | H];
      apply in_map_iff in H; destruct H; destruct x, p; destruct H;
      unfold transLabel in H; simpl in H; inversion H;
      [apply Hl1 in H0 | apply Hl2 in H0]; remember H0 as H'; clear HeqH';
      apply computeAllOutgoingTransitions_onlyTransFromB in H0;
      unfold from in H0; simpl in H0; subst;
      [ apply sos_parallel_internal_left_rule; apply IHB1 |
        apply sos_parallel_internal_right_rule; apply IHB2 ]; apply H'.
    + simpl in H.
      destruct (
       partition
         (fun t : BehaviourTrans =>
          match transLabel t with
          | InternalEvent => false
          | ExternalEvent e => (a =? e)%string
          end) l1) eqn:H'.
      destruct (
       partition
         (fun t : BehaviourTrans =>
          match transLabel t with
          | InternalEvent => false
          | ExternalEvent e => (a =? e)%string
          end) l2) eqn:H''.
      apply set_union_iff in H. destruct H as [H | H].
      * apply IHG with (l1 := l0) (l2 := l4); auto; intros;
        [ assert (Hp : snd (l3, l4) = l4);
          [reflexivity | rewrite <- H'' in Hp] |
          assert (Hp : snd (l, l0) = l0);
          [ reflexivity | rewrite <- H' in Hp] ];
          rewrite <- Hp in H0; apply partition_elim1 in H0; destruct H0; auto.
      * assert (Hp : fst (l, l0) = l). { reflexivity. } rewrite <- H' in Hp.
        apply in_flat_map in H. destruct H as [x [H H0]].
        apply in_map_iff in H0. destruct H0 as [x' [H0 H1]]. inversion H0.
        rewrite <- Hp in H. apply partition_elim2 in H. destruct H.
        rewrite H3 in H2. inversion H2.
  - assert (forall x, In x G -> In x G'). { subst. trivial. }
    generalize dependent l1. generalize dependent l2.
    destruct (in_dec string_dec e G').
    + rewrite HeqG' in i. clear HeqG'. induction G; intros; [inversion i | ].
      simpl in H.
      destruct (
         partition
           (fun t : BehaviourTrans =>
            match transLabel t with
            | InternalEvent => false
            | ExternalEvent e => (a =? e)%string
            end) l1) eqn:H'.
        destruct (
         partition
           (fun t : BehaviourTrans =>
            match transLabel t with
            | InternalEvent => false
            | ExternalEvent e => (a =? e)%string
            end) l2) eqn:H''.
        apply set_union_iff in H. destruct H as [H | H].
        * destruct i.
          { apply computeAllOutgoingTransitions_parallel_elim in H as Hl.
            destruct Hl as [t [Hl Hl']]. subst. destruct Hl as [Hl | Hl];
            [ assert (Hp : snd (l, l0) = l0); trivial; rewrite <- H' in Hp |
              assert (Hp : snd (l3, l4) = l4); trivial; rewrite <- H'' in Hp ];
              rewrite <- Hp in Hl; apply partition_elim1 in Hl; destruct Hl;
              rewrite Hl' in H2; rewrite eqb_refl in H2; inversion H2. }
        { apply IHG with (l1 := l0) (l2 := l4); auto.
          - intros. apply H0. right. apply H2.
          - intros. apply Hl2; assert (Hp : snd (l3, l4) = l4); trivial;
            rewrite <- H'' in Hp. rewrite <- Hp in H2.
            apply partition_elim1 in H2. destruct H2. apply H2.
          - intros. apply Hl1; assert (Hp : snd (l, l0) = l0); trivial;
            rewrite <- H' in Hp. rewrite <- Hp in H2.
            apply partition_elim1 in H2. destruct H2. apply H2. }
      * subst. simpl in H.
        apply in_flat_map in H. destruct H as [x [H ?]].
        apply in_map_iff in H1. destruct H1 as [x0 [H1 ?]]. destruct x, p.
        destruct x0, p1. unfold transLabel in H1. inversion H1. subst.
        assert (Hp2 : fst (l3, l4) = l3). { reflexivity. }
        rewrite <- H'' in Hp2. rewrite <- Hp2 in H2.
        apply partition_elim2 in H2.
        clear Hp2. destruct H2. unfold transLabel in H3. simpl in H3.
        destruct e1 eqn:He1; [inversion H3 |]. apply eqb_eq in H3.

        assert (Hp1 : fst (l, l0) = l). { reflexivity. } rewrite <- H' in Hp1.
        rewrite <- Hp1 in H. apply partition_elim2 in H. clear Hp1. destruct H.
        unfold transLabel in H4. simpl in H4. apply eqb_eq in H4. subst.
        apply Hl1 in H. apply Hl2 in H2.
        remember H as HB1. clear HeqHB1.
        apply computeAllOutgoingTransitions_onlyTransFromB in H.
        unfold from in H. simpl in H. subst.
        remember H2 as HB2. clear HeqHB2.
        apply computeAllOutgoingTransitions_onlyTransFromB in H2.
        unfold from in H2. simpl in H2. subst.
        apply IHB1 in HB1. apply IHB2 in HB2.
        apply sos_parallel_sync_rule; auto.
    + clear HeqG'. induction G; intros.
      * simpl in H. apply set_union_iff in H. destruct H;
        apply in_map_iff in H; destruct H; destruct x, p; destruct H;
        unfold transLabel in H; simpl in H; inversion H;
        [ apply Hl1 in H1 | apply Hl2 in H1 ];
        remember H1 as H'; clear HeqH';
        apply computeAllOutgoingTransitions_onlyTransFromB in H1;
        unfold from in H1; simpl in H1; subst;
        [ apply sos_parallel_async_left_rule |
          apply sos_parallel_async_right_rule]; auto.
      * simpl in H. destruct (
         partition
           (fun t : BehaviourTrans =>
            match transLabel t with
            | InternalEvent => false
            | ExternalEvent e => (a =? e)%string
            end) l1) eqn:H'.
        destruct (
         partition
           (fun t : BehaviourTrans =>
            match transLabel t with
            | InternalEvent => false
            | ExternalEvent e => (a =? e)%string
            end) l2) eqn:H''.
       apply set_union_iff in H. destruct H as [H | H].
        { apply IHG with (l1 := l0) (l2 := l4); auto;
          [ intros x' H'''; apply H0; right; apply H''' | | ];
          intros ? H''';
          [ assert (Hp : snd (l3, l4) = l4);
            [reflexivity | rewrite <- H'' in Hp] |
            assert (Hp : snd (l, l0) = l0);
            [ reflexivity | rewrite <- H' in Hp] ];
            rewrite <- Hp in H'''; apply partition_elim1 in H''';
            destruct H'''; auto. }
        { assert (Hp : fst (l, l0) = l). { reflexivity. } rewrite <- H' in Hp.
          apply in_flat_map in H. destruct H. destruct H.
          apply in_map_iff in H1. destruct H1. destruct H1. inversion H1.
          rewrite <- Hp in H. apply partition_elim2 in H. destruct H.
          rewrite H4 in H3. apply eqb_eq in H3. subst. elim n. apply H0. left.
          reflexivity. }
Qed.

Definition computeAllOutgoingTransitions_correctness (B : ProcessBehaviour) :=
  forall (B' : ProcessBehaviour) (ctx : BehaviourExpressions) (e : Event),
  In (B, e, B') (computeAllOutgoingTransitions B ctx) -> (ctx # B // e --> B').

Definition computeAllOutgoingTransitions_completeness (B : ProcessBehaviour) :=
  forall (B' : ProcessBehaviour) (ctx : BehaviourExpressions) (e : Event),
  (ctx # B // e --> B') -> In (B, e, B') (computeAllOutgoingTransitions B ctx).

Theorem computeAllOutgoingTransitions_correct :
  forall (B : ProcessBehaviour), computeAllOutgoingTransitions_correctness B
with computeAllOutgoingTransitions_correct' :
  forall (Bs : ChoiceSet),
    Forall computeAllOutgoingTransitions_correctness
           (match Bs with | Values Bs' => Bs' end).
Proof.
  - intros B B' ctx. generalize dependent B'. induction B; intros.
    + simpl in H. destruct H as [H | H]; inversion H. apply sos_prefix_rule.
    + destruct c eqn:H''. simpl in H. remember s as s'.
      assert (Values s' = Values s).
      { rewrite Heqs'. reflexivity. }
      rewrite H0 in H. rewrite H0. clear H0.
      assert (exists B, In B s' /\
        In (B, e, B') (computeAllOutgoingTransitions B ctx)).
      { clear H''. clear Heqs'. induction s'.
        - inversion H.
        - apply set_union_elim in H. destruct H as [H | H].
          + unfold set_In in H. clear IHs'. apply in_map_iff in H. destruct H.
            destruct x, p. destruct H. simpl in H. inversion H.
            assert (H' : In (p, e0, p0) (computeAllOutgoingTransitions a ctx)).
            { apply H0. }
            apply computeAllOutgoingTransitions_onlyTransFromB in H'.
            unfold from in H'. simpl in H'. subst.
            exists a. split; auto. left. reflexivity.
          + apply IHs' in H. destruct H. exists x. destruct H. split; auto.
            right. apply H. }
      destruct H0. destruct H0. rewrite Heqs' in H0.
      apply sos_choice_rule with (B := x).
      * apply H0.
      * pose proof computeAllOutgoingTransitions_correct' c. rewrite H'' in H2.
        simpl in H2. subst. rewrite Forall_forall in H2. apply H2.
        { apply H0. }
        { apply H1. }
  + apply computeAllOutgoingTransitions_parallel_correct
      with (l1 := (computeAllOutgoingTransitions B1 ctx))
           (l2 := (computeAllOutgoingTransitions B2 ctx)); trivial.
  + simpl in H. remember (computeAllOutgoingTransitions B ctx) as l'.
    remember l' as l. rewrite Heql in H.
    assert (H': forall x ,In x l -> In x (computeAllOutgoingTransitions B ctx)).
    { rewrite Heql'. trivial. }
    assert (H'' : forall x, In x l' -> In x l). { rewrite Heql. trivial. }
    clear Heql' Heql. induction l'.
    * inversion H.
    * apply set_add_elim in H. destruct H.
      { destruct a, p, e0.
        - unfold transLabel in H. simpl in H. inversion H.
          apply sos_hide_internal_rule. apply IHB. apply H''.
          assert (In (p, InternalEvent, p0) l).
          { apply H''. left. reflexivity. }
          apply H' in H0.
          apply computeAllOutgoingTransitions_onlyTransFromB in H0.
          unfold from in H0. simpl in H0.
          subst. left. reflexivity.
        - unfold transLabel in H. simpl in H. destruct (in_dec string_dec e0 s).
          + inversion H. apply sos_hide_in_rule with (a := e0); trivial.
            apply IHB. apply H''.
            assert (In (p, ExternalEvent e0, p0) l).
            { apply H''. left. reflexivity. }
            apply H' in H0.
            apply computeAllOutgoingTransitions_onlyTransFromB in H0.
            unfold from in H0. simpl in H0.
            subst. left. reflexivity.
          + inversion H. apply sos_hide_not_in_rule. trivial. apply IHB.
            apply H''.
            assert (In (p, ExternalEvent e0, p0) l).
            { apply H''. left. reflexivity. }
            apply H' in H0.
            apply computeAllOutgoingTransitions_onlyTransFromB in H0.
            unfold from in H0. simpl in H0.
            subst. left. reflexivity. }
      { apply IHl'. apply H. intros. apply H''. right. apply H0. }
    + simpl in H. destruct (getProcessBehaviour p ctx) eqn:H'.
      * symmetry in H'. apply getProcessBehaviour_in in H'.
        destruct H; inversion H. subst. apply sos_process_instantiation_rule.
        apply H'.
      * inversion H.
  - intros. destruct Bs. induction s.
    + apply Forall_nil.
    + apply Forall_cons.
      * apply computeAllOutgoingTransitions_correct.
      * apply IHs.
Qed.

Theorem computeAllOutgoingTransitions_complete :
  forall (B : ProcessBehaviour), computeAllOutgoingTransitions_completeness B.
Proof.
  intros B B' ctx e H. induction H.
  - simpl. left. reflexivity.
  - simpl. apply in_split in H. destruct H as [p [s]]. rewrite H.
    assert (Values (p ++ B :: s) = Values Bs). { rewrite H. reflexivity. }
    rewrite H1. clear H H1.
    induction p.
    + simpl. apply set_union_intro1.
      eapply in_map
        with  (f := (fun t => (Choice (Values (Bs)), snd (fst t), snd t)))
        in IHsosR.
      simpl in IHsosR. apply IHsosR.
    + simpl. apply set_union_intro2. apply IHp.
  - simpl. remember (computeAllOutgoingTransitions B1 ctx) as l.
    remember (computeAllOutgoingTransitions B2 ctx) as l'. clear Heql' Heql.
    remember G as G'. rewrite changeInductionSet with (G' := G); auto.
    rewrite HeqG' in H. clear HeqG'. generalize dependent l'.
    generalize dependent l. induction G; intros.
    + simpl. apply set_union_iff. left. apply in_split in IHsosR.
      destruct IHsosR as [p [s]]. rewrite H1. rewrite map_app.
      apply in_or_app. right. left. unfold transLabel. simpl. reflexivity.
    + simpl. apply not_in_cons in H. destruct H as [H' H].
      apply eqb_neq in H'. rewrite eqb_sym in H'.
      apply partition_intro1
               with (f := fun t => match transLabel t with
                                    | InternalEvent => false
                                    | ExternalEvent e => (a =? e)%string
                                    end)
               in IHsosR; auto.
      destruct (partition (fun t : BehaviourTrans =>
                              match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end) l).
      destruct (partition
                         (fun t : BehaviourTrans =>
                          match transLabel t with
                          | InternalEvent => false
                          | ExternalEvent e => (a =? e)%string
                          end) l').
    apply set_union_iff. left. simpl in IHsosR. apply IHG; auto.
  - simpl. remember (computeAllOutgoingTransitions B1 ctx) as l.
    remember (computeAllOutgoingTransitions B2 ctx) as l'. clear Heql' Heql.
    remember G as G'. rewrite changeInductionSet with (G' := G); auto.
    rewrite HeqG' in H.
    clear HeqG'. generalize dependent l'. generalize dependent l.
    induction G; intros.
    + simpl. apply set_union_iff. right. apply in_split in IHsosR.
      destruct IHsosR as [p [s]]. rewrite H1. rewrite map_app.
      apply in_or_app. right. left. unfold transLabel. simpl. reflexivity.
    + simpl. apply not_in_cons in H. destruct H as [H' H].
      apply eqb_neq in H'. rewrite eqb_sym in H'.
      apply partition_intro1
               with (f := fun t => match transLabel t with
                                    | InternalEvent => false
                                    | ExternalEvent e => (a =? e)%string
                                    end)
               in IHsosR; auto.
      destruct (partition (fun t : BehaviourTrans =>
                              match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end) l).
      destruct (partition
                         (fun t : BehaviourTrans =>
                          match transLabel t with
                          | InternalEvent => false
                          | ExternalEvent e => (a =? e)%string
                          end) l').
    apply set_union_iff. left. simpl in IHsosR. apply IHG; auto.
  - simpl. remember (computeAllOutgoingTransitions B1 ctx) as l.
    remember (computeAllOutgoingTransitions B2 ctx) as l'.
    clear Heql' Heql. remember G as G'.
    rewrite changeInductionSet with (G' := G); auto.
    clear HeqG'. generalize dependent l'. generalize dependent l.
    induction G; intros.
    + simpl. apply set_union_iff. left. apply in_split in IHsosR.
      destruct IHsosR as [p [s]]. rewrite H0. rewrite map_app.
      apply in_or_app. right. left. unfold transLabel. simpl. reflexivity.
    + simpl. apply partition_intro1
               with (f := fun t => match transLabel t with
                                    | InternalEvent => false
                                    | ExternalEvent e => (a =? e)%string
                                    end)
               in IHsosR; auto.
      destruct (partition (fun t : BehaviourTrans =>
                              match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end) l).
      destruct (partition
                         (fun t : BehaviourTrans =>
                          match transLabel t with
                          | InternalEvent => false
                          | ExternalEvent e => (a =? e)%string
                          end) l').
      apply set_union_iff. left. simpl in IHsosR. apply IHG. apply IHsosR.
  - simpl. remember (computeAllOutgoingTransitions B1 ctx) as l.
    remember (computeAllOutgoingTransitions B2 ctx) as l'.
    clear Heql' Heql. remember G as G'.
    rewrite changeInductionSet with (G' := G); auto.
    clear HeqG'. generalize dependent l'. generalize dependent l.
    induction G; intros.
    + simpl. apply set_union_iff. right. apply in_split in IHsosR.
      destruct IHsosR as [p [s]]. rewrite H0. rewrite map_app.
      apply in_or_app. right. left. unfold transLabel. simpl. reflexivity.
    + simpl. apply partition_intro1
               with (f := fun t => match transLabel t with
                                    | InternalEvent => false
                                    | ExternalEvent e => (a =? e)%string
                                    end)
               in IHsosR; trivial.
      destruct (partition (fun t : BehaviourTrans =>
                              match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end) l).
      destruct (partition
                         (fun t : BehaviourTrans =>
                          match transLabel t with
                          | InternalEvent => false
                          | ExternalEvent e => (a =? e)%string
                          end) l').
      apply set_union_iff. left. simpl in IHsosR. apply IHG. apply IHsosR.
  - simpl. remember (computeAllOutgoingTransitions B1 ctx) as l.
    remember (computeAllOutgoingTransitions B2 ctx) as l'. clear Heql' Heql.
    remember G as G'. rewrite changeInductionSet with (G' := G);
    auto. rewrite HeqG' in H.
    clear HeqG'. generalize dependent l'. generalize dependent l.
    induction G; intros; [inversion H | ]. destruct (eqb a mi) eqn:H'.
    + simpl.
      apply partition_intro2
         with (f := fun t => match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end)
         in IHsosR1; auto.
      apply partition_intro2
         with (f := fun t => match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end)
         in IHsosR2; auto.
      destruct (partition (fun t : BehaviourTrans =>
                              match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end) l).
      destruct (partition
                         (fun t : BehaviourTrans =>
                          match transLabel t with
                          | InternalEvent => false
                          | ExternalEvent e => (a =? e)%string
                          end) l').
      apply set_union_iff. right. simpl in IHsosR1. simpl in IHsosR2.
      apply in_flat_map. exists (B1, ExternalEvent mi, B1'). split; auto.
      unfold transLabel. simpl.
      apply in_map
        with (f := fun t =>
                (Parallel B1 G' B2, ExternalEvent mi, Parallel B1' G' (to t)))
        in IHsosR2.
      simpl in IHsosR2. apply IHsosR2.
    + simpl.
      apply partition_intro1
         with (f := fun t => match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end)
         in IHsosR1; auto.
      apply partition_intro1
         with (f := fun t => match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end)
         in IHsosR2; auto.
      destruct (partition (fun t : BehaviourTrans =>
                              match transLabel t with
                              | InternalEvent => false
                              | ExternalEvent e => (a =? e)%string
                              end) l).
      destruct (partition
                         (fun t : BehaviourTrans =>
                          match transLabel t with
                          | InternalEvent => false
                          | ExternalEvent e => (a =? e)%string
                          end) l').
      apply set_union_iff. left. apply IHG; auto. apply eqb_neq in H'.
      inversion H; easy.
  - simpl. apply in_split in IHsosR. destruct IHsosR as [p [s]]. rewrite H1.
    clear H1. induction p.
    + simpl. destruct (in_dec string_dec a G); try easy. apply set_add_intro2.
      reflexivity.
    + simpl. apply set_add_intro1. apply IHp.
  - simpl. apply in_split in IHsosR. destruct IHsosR as [p [s]]. rewrite H1.
    clear H1. induction p.
    + simpl. destruct (in_dec string_dec mi G); try easy.
      apply set_add_intro2. reflexivity.
    + simpl. apply set_add_intro1. apply IHp.
  - simpl. apply in_split in IHsosR. destruct IHsosR as [p [s]]. rewrite H0.
    clear H0. induction p.
    + simpl. apply set_add_intro2. reflexivity.
    + simpl. apply set_add_intro1. apply IHp.
  - simpl. apply getProcessBehaviour_in in H. rewrite <- H. left. reflexivity.
Qed.

Theorem computeAllOutgoingTransitions_iff :
  forall (B B' : ProcessBehaviour) (ctx : BehaviourExpressions) (e : Event),
  (ctx # B // e --> B') <-> In (B, e, B') (computeAllOutgoingTransitions B ctx).
Proof.
  intros. split.
  - apply computeAllOutgoingTransitions_complete.
  - apply computeAllOutgoingTransitions_correct.
Qed.

Definition P (B : ProcessBehaviour): Prop :=
  forall (ctx : BehaviourExpressions),
    NoDup (computeAllOutgoingTransitions B ctx).

Ltac rename_choice_ind s :=
  let H' := fresh "H'" in
  let s' := fresh "s'" in
  let Hs := fresh "Hs" in
    remember s as s' eqn:Hs;
    assert (H' : Values s' = Values s);
    [ rewrite Hs; reflexivity | replace (Values s'); clear H' ].

Theorem computeAllOutgoingTransitions_NoDup :
  forall (B : ProcessBehaviour), P B
with computeAllOutgoingTransitions_NoDup' :
  forall (Bs : ChoiceSet), Forall P (match Bs with | Values Bs' => Bs' end).
Proof.
  - intros B ctx. induction B.
    + simpl. apply NoDup_cons; [easy | apply NoDup_nil].
    + pose proof (computeAllOutgoingTransitions_NoDup' c).
      destruct c. simpl. rename_choice_ind s. clear Hs.
      induction s'; [apply NoDup_nil |].
      apply set_union_nodup.
      * inversion H. unfold P in H2. pose proof (H2 ctx) as Nodup_a.
        clear H0 H1 H2 H3 l.
        remember (computeAllOutgoingTransitions a ctx) as l eqn:l_eq.
        assert (H' :
          forall x, In x l -> In x (computeAllOutgoingTransitions a ctx)).
        { subst. trivial. }
        clear IHs' l_eq H x. induction l; [apply NoDup_nil |].
        simpl. inversion Nodup_a. subst. apply NoDup_cons.
        { unfold not. intros H. apply in_map_iff in H.
          destruct H as [x [H'' H''']].
          assert (from x = a).
          { apply computeAllOutgoingTransitions_onlyTransFromB
              with (ctx := ctx).
            apply H'. right. apply H'''. }
          assert (from a0 = a).
          { apply computeAllOutgoingTransitions_onlyTransFromB
              with (ctx := ctx).
            apply H'. left. trivial. }
          assert (a0_eq : a0 = x).
          { inversion H''. destruct x, p. destruct a0, p1. unfold to in H5.
            unfold transLabel in H4. unfold from in H0. unfold from in H.
            simpl in *. subst. reflexivity. }
          clear H H0. subst. easy. }
        { apply IHl. apply H2. intros x H''. apply H'. right. apply H''. }
      * apply IHs'. inversion H. apply H3.
    + simpl. remember s as G eqn:HG.
      rewrite changeInductionSet with (G' := s); auto.
      clear HG. remember (computeAllOutgoingTransitions B1 ctx) as l1 eqn:l1_eq.
      remember (computeAllOutgoingTransitions B2 ctx) as l2 eqn:l2_eq.
      assert (Hl1 :
        forall x, In x l1 -> In x (computeAllOutgoingTransitions B1 ctx)).
      { subst. trivial. }
      assert (Hl2 :
        forall x, In x l2 -> In x (computeAllOutgoingTransitions B2 ctx)).
      { subst. trivial. }
      clear l1_eq l2_eq. generalize dependent l2. generalize dependent l1.
      induction s; intros l1 NoDup_l1 Hl1 l2 NoDup_l2 Hl2.
      * simpl. apply set_union_nodup; [induction l1 | induction l2 ]; simpl;
        try (apply NoDup_nil); [inversion NoDup_l1 | inversion NoDup_l2];
        subst; apply NoDup_cons.
        { unfold not. intros H. apply in_map_iff in H.
          destruct H as [x [H'' H''']].
          assert (from x = B1).
          { apply computeAllOutgoingTransitions_onlyTransFromB
              with (ctx := ctx).
            apply Hl1. right. apply H'''. }
          assert (from a =  B1).
          { apply computeAllOutgoingTransitions_onlyTransFromB
              with (ctx := ctx).
            apply Hl1. left. trivial. }
          assert (a_eq : a = x).
          { inversion H''. destruct x, p. destruct a, p1. unfold to in H5.
            unfold transLabel in H4. unfold from in *. simpl in *. subst.
            reflexivity. } subst. easy. }
        { apply IHl1. apply H2. intros x H''. apply Hl1. right. apply H''. }
        { unfold not. intros H. apply in_map_iff in H.
          destruct H as [x [H'' H''']].
          assert (from x = B2).
          { apply computeAllOutgoingTransitions_onlyTransFromB
              with (ctx := ctx).
            apply Hl2. right. apply H'''. }
          assert (from a =  B2).
          { apply computeAllOutgoingTransitions_onlyTransFromB
              with (ctx := ctx).
            apply Hl2. left. trivial. }
          assert (a_eq : a = x).
          { inversion H''. destruct x, p. destruct a, p1. unfold to in H5.
            unfold transLabel in H4. unfold from in *. simpl in *. subst.
            reflexivity. } subst. easy. }
        { apply IHl2. apply H2. intros x H''. apply Hl2. right. apply H''. }
      * simpl.
        destruct (partition
         (fun t : BehaviourTrans =>
          match transLabel t with
          | InternalEvent => false
          | ExternalEvent e => (a =? e)%string
          end) l1) eqn:Hpl1.
        destruct (partition
         (fun t : BehaviourTrans =>
          match transLabel t with
          | InternalEvent => false
          | ExternalEvent e => (a =? e)%string
          end) l2) eqn:Hpl2.
        apply set_union_nodup.
        { assert (l0_eq : l0 = snd (l, l0)). { trivial. }
          rewrite <- Hpl1 in l0_eq.
          assert (l4_eq : l4 = snd (l3, l4)). { trivial. }
          rewrite <- Hpl2 in l4_eq.
          apply IHs.
          { eapply NoDup_partition in NoDup_l1.
            destruct NoDup_l1 as [_ NoDup_l0]. rewrite l0_eq. eauto. }
          { intros x H. rewrite l0_eq in H. apply partition_elim1 in H.
            destruct H as [H _]. apply Hl1; auto. }
          { eapply NoDup_partition in NoDup_l2.
            destruct NoDup_l2 as [_ NoDup_l4]. rewrite l4_eq. eauto. }
          { intros x H. rewrite l4_eq in H. apply partition_elim1 in H.
            destruct H as [H _]. apply Hl2; auto. } }
        { assert (eq_l3 : l3 = fst (l3, l4)). { trivial. }
          assert (eq_l : l = fst (l, l0)). { trivial. }
          rewrite <- Hpl2 in eq_l3. rewrite <- Hpl1 in eq_l.
          assert (Hl3 :
            forall t, In t l3 ->
              transLabel t = ExternalEvent a /\
              In t (computeAllOutgoingTransitions B2 ctx)).
          { rewrite eq_l3. intros t H. apply partition_elim2 in H.
            destruct H as [H H']. destruct (transLabel t); [inversion H'|].
            apply eqb_eq in H'. rewrite H'. split; [|apply Hl2]; trivial. }
          assert (Hl : forall t, In t l ->
              transLabel t = ExternalEvent a /\
              In t (computeAllOutgoingTransitions B1 ctx)).
          { rewrite eq_l. intros t H. apply partition_elim2 in H.
            destruct H as [H H']. destruct (transLabel t); [inversion H'|].
            apply eqb_eq in H'. rewrite H'. split; [|apply Hl1]; trivial. }
          eapply NoDup_partition in NoDup_l1. destruct NoDup_l1 as [NoDup_l _].
          rewrite <- eq_l in NoDup_l.
          eapply NoDup_partition in NoDup_l2. destruct NoDup_l2 as [NoDup_l3 _].
          rewrite <- eq_l3 in NoDup_l3.
          clear IHs Hl1 Hl2 Hpl1 Hpl2 l0 l4 eq_l eq_l3 l1 l2 s.
          remember l3 as l2 eqn:l2_eq. remember l as l1 eqn:l1_eq.
          assert (Hl1 : forall t, In t l1 -> In t l). { subst. trivial. }
          assert (Hl2 : forall t, In t l2 -> In t l3). { subst. trivial. }
          rewrite l1_eq in Hl. rewrite l2_eq in Hl3.
          clear l1_eq l2_eq. generalize dependent l2.
          induction l1; intros l2 NoDup_l2 Hl2; [ apply NoDup_nil | ].
          simpl. apply NoDup_app. repeat split.
          { induction l2; [apply NoDup_nil|]. simpl. apply NoDup_cons.
            { unfold not. intros H. apply in_map_iff in H.
              destruct H as [x [H H']]. inversion H.
              assert (Ha1 : In a1 l3). { apply Hl2. left. trivial. }
              apply Hl3 in Ha1. destruct Ha1 as [trans_a1 from_a1].
              apply computeAllOutgoingTransitions_onlyTransFromB in from_a1.
              assert (Hx : In x l3). { apply Hl2. right. trivial. }
              apply Hl3 in Hx. destruct Hx as [trans_x from_x].
              apply computeAllOutgoingTransitions_onlyTransFromB in from_x.
              inversion NoDup_l2.
              assert (x = a1).
              { unfold from in *. unfold to in *. unfold transLabel in *.
                 destruct x, p. destruct a1, p1. simpl in *. subst. trivial. }
              subst. easy. }
            { apply IHl2. inversion NoDup_l2. apply H2. intros t H. apply Hl2.
              right. apply H. } }
          { inversion NoDup_l. apply IHl1; auto. intros t H'. apply Hl1. right.
            apply H'. }
          { intros t H. unfold not. intros H'. apply in_flat_map in H'.
            destruct H' as [t' [Hl1' H']]. apply in_map_iff in H.
            destruct H as [x [t_eq H]]. apply in_map_iff in H'.
            destruct H' as [x' [t'_eq H']]. inversion NoDup_l.
            rewrite <- t'_eq in t_eq. inversion t_eq. clear H0 H3 H1 t'_eq.
            assert(Ha0 : In a0 l). { apply Hl1. left. trivial. }
            apply Hl in Ha0. destruct Ha0 as [trans_ao from_a0].
            apply computeAllOutgoingTransitions_onlyTransFromB in from_a0.
            assert (Ht' : In t' l). { apply Hl1. right. apply Hl1'. }
            apply Hl in Ht'. destruct Ht' as [trans_t' from_t'].
            apply computeAllOutgoingTransitions_onlyTransFromB in from_t'.
            assert (a0 = t').
            { destruct a0, p. destruct t', p1. unfold from in *. unfold to in *.
              unfold transLabel in *. simpl in *. subst. trivial. }
           subst. easy. } }
    + simpl. remember (computeAllOutgoingTransitions B ctx) as l.
      clear Heql. induction l.
      * apply NoDup_nil.
      * apply set_add_nodup. apply IHl. inversion IHB; auto.
    + simpl. destruct (getProcessBehaviour p ctx).
      * apply NoDup_cons; try easy. apply NoDup_nil.
      * apply NoDup_nil.
  - destruct Bs. induction s.
    + apply Forall_nil.
    + apply Forall_cons.
      * apply computeAllOutgoingTransitions_NoDup.
      * apply IHs.
Qed.

Lemma createBehaviourTransSet'_fromT :
  forall (i : nat) (visited to_visit : list ProcessBehaviour)
    (ctx : BehaviourExpressions) (T : BehaviourTransSet) (B : ProcessBehaviour),
    createBehaviourTransSet' ctx to_visit visited i = Some T ->
    In B visited ->
    ~ In B to_visit ->
    (forall t, In t T -> from t <> B).
Proof.
  induction i.
  - intros visited to_visit ctx T B H _ _. inversion H.
  - intros visited to_visit ctx T B H B_vis B_to_vis.
    simpl in H. destruct to_visit.
    + intros t H'. inversion H. subst. inversion H'.
    + destruct (createBehaviourTransSet' ctx
        (set_union ProcessBehaviourDec to_visit
           (set_diff' ProcessBehaviourDec
              (targetBehaviours (computeAllOutgoingTransitions p ctx))
              (p :: visited))) (p :: visited) i) eqn:H'; [| inversion H].
      inversion H. intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht | Ht].
      * generalize dependent t. eapply IHi.
        { apply H'. }
        { right. apply B_vis. }
        { unfold not. intros H''. apply set_union_iff in H''.
          destruct H'' as [H'' | H''].
          { elim B_to_vis. right. apply H''. }
          { apply set_diff'_elim2 in H''. elim H''. right. apply B_vis. } }
      * apply computeAllOutgoingTransitions_onlyTransFromB in Ht.
        destruct (ProcessBehaviourDec p B); subst.
        { elim B_to_vis. subst. left. trivial. }
        { easy. }
Qed.

Lemma createBehaviourTransSet_NoDup :
  forall (P : ProcessName) (ctx : BehaviourExpressions) (T : BehaviourTransSet),
    (exists i, createBehaviourTransSet ctx P i = Some T) ->
    NoDup T.
Proof.
  intros P ctx T H. destruct H as [i createH].
  unfold createBehaviourTransSet in createH.
  destruct (getProcessBehaviour P ctx) as [B |] eqn:H; [| inversion createH].
  remember ([B]) as to_visit.
  assert (NoDup to_visit).
  { rewrite Heqto_visit. apply NoDup_cons; try easy. apply NoDup_nil. }
  remember (@nil ProcessBehaviour) as visited.
  clear B H Heqvisited Heqto_visit.
  generalize dependent T.
  generalize dependent visited.
  generalize dependent to_visit.
  induction i as [|i'];
  intros to_visit NoDup_to_visit visited T createH.
  - inversion createH.
  - destruct to_visit as [| B to_visit'].
    + simpl in createH. inversion createH. apply NoDup_nil.
    + simpl in createH.
      destruct (createBehaviourTransSet' ctx
                  (set_union ProcessBehaviourDec to_visit'
                     (set_diff' ProcessBehaviourDec
                        (targetBehaviours (computeAllOutgoingTransitions B ctx))
                        (B :: visited)))
                 (B :: visited) i') as [T'|] eqn:H.
      * inversion createH as [Teq]. apply NoDup_app. repeat split.
        { eapply IHi'; [| apply H];
          inversion NoDup_to_visit; apply set_union_nodup; auto;
            apply set_diff'_nodup; apply targetBehaviours_NoDup.  }
        { apply computeAllOutgoingTransitions_NoDup. }
        { unfold not. intros t H' H''.
          apply computeAllOutgoingTransitions_onlyTransFromB in H''.
          apply createBehaviourTransSet'_fromT with (B := B) (t := t) in H.
          { easy. }
          { left. trivial. }
          { intros H'''. apply set_union_iff in H'''. clear H' H''.
            destruct H''' as [H' | H'].
            { inversion NoDup_to_visit; auto. }
            { apply set_diff'_elim2 in H'. elim H'. left. trivial. } }
          { auto. } }
      * inversion createH.
Qed.

Theorem createBehaviourTransSet'_BehaviourTransSetR' :
  forall (i : nat) (ctx : BehaviourExpressions)
    (T : BehaviourTransSet) (to_visit visited : set ProcessBehaviour),
    NoDup to_visit ->
    (forall x, In x visited -> ~ In x to_visit) ->
    (forall x, In x to_visit -> ~ In x visited) ->
    createBehaviourTransSet' ctx to_visit visited i = Some T ->
    BehaviourTransSetR' ctx T to_visit visited.
Proof.
  intros i ctx. induction i as [|i']; [intros; easy|].
  intros T to_visit visited NoDup_to_vis In_vis In_to_vis createH.
  simpl in createH. destruct to_visit as [| B to_visit'];
  [inversion createH; apply behaviour_trans_empty_rule |].
  destruct (createBehaviourTransSet' ctx
              (set_union ProcessBehaviourDec to_visit'
                 (set_diff' ProcessBehaviourDec
                    (targetBehaviours (computeAllOutgoingTransitions B ctx))
                    (B :: visited)))
              (B :: visited) i') as [T'|] eqn:createH'.
  inversion createH as [T_eq]. clear createH.
  assert (from_T' : forall t, In t T' -> from t <> B).
  { intros t H. eapply createBehaviourTransSet'_fromT.
    { apply createH'. }
    { left. trivial. }
    { intros H'. inversion NoDup_to_vis. apply set_union_iff in H'.
      destruct H' as [H' | H']; [auto |]. apply set_diff'_elim2 in H'.
      elim H'. left. trivial. }
    { auto. } }
  assert (fromB_eq : transFromB B (T' ++ computeAllOutgoingTransitions B ctx) =
                     computeAllOutgoingTransitions B ctx).
  { remember T' as T'' eqn:T'_eq.
    assert (H : forall t, In t T' -> In t T''). { subst. auto. }
    rewrite T'_eq. clear T'_eq. induction T'.
    { apply transFromB_id. apply computeAllOutgoingTransitions_onlyTransFromB. }
    { simpl. assert (H' : In a T''). { apply H. left. trivial. }
      apply from_T' in H'. destruct a, p. unfold from in H'. simpl in H'.
      destruct (ProcessBehaviourDec B p); [ symmetry in e0; easy |]. apply IHT'.
      intros t H''. apply H. right. apply H''. } }
  apply behaviour_trans_inductive_rule.
  - rewrite fromB_eq. intros e B'. apply computeAllOutgoingTransitions_iff.
  - rewrite fromB_eq. rewrite set_diff'_app.
    assert (T'_diff :
      set_diff' BehaviourTransDec T' (computeAllOutgoingTransitions B ctx) =
      T').
    { clear fromB_eq createH' T_eq. remember T' as T'' eqn:T''_eq.
      rewrite T''_eq.
      assert (HT': forall x, In x T' -> In x T''). { subst. trivial. }
      clear T''_eq.
      induction T'; trivial. simpl.
      destruct (set_mem BehaviourTransDec a
        (computeAllOutgoingTransitions B ctx)) eqn:a_mem.
      { apply set_mem_correct1 in a_mem.
        apply computeAllOutgoingTransitions_onlyTransFromB in a_mem.
        assert (from a <> B). { apply from_T'. apply HT'. left. trivial. }
        easy. }
      { apply f_equal. apply IHT'. intros x H. apply HT'. right. apply H. } }
    rewrite T'_diff. apply IHi'; auto.
    + apply set_union_nodup.
      * inversion NoDup_to_vis; auto.
      * apply set_diff'_nodup. apply targetBehaviours_NoDup.
    + intros x In_B_vis. rewrite set_union_iff. unfold not. intros H.
      destruct H as [H | H].
      * simpl in In_B_vis. destruct In_B_vis as [B_eq | In_vis''].
        { subst. inversion NoDup_to_vis; easy. }
        { apply In_vis in In_vis''. elim In_vis''. right. apply H. }
      * apply set_diff'_elim2 in H. easy.
    + intros x In_union. apply set_union_elim in In_union.
      destruct In_union as [In_to_vis' | In_diff].
      * unfold not. intros In_vis'. simpl in In_vis'.
        destruct In_vis' as [B_eq | In_vis'].
        { subst. inversion NoDup_to_vis; easy. }
        { apply In_vis in In_vis'. elim In_vis'. right. trivial. }
      * apply set_diff'_elim2 in In_diff. apply In_diff.
  - inversion createH.
Qed.

Theorem createBehaviourTransSet_BehaviourTransSetR :
  forall (P : ProcessName) (ctx : BehaviourExpressions) (i : nat)
    (T : BehaviourTransSet),
    createBehaviourTransSet ctx P i = Some T ->
    BehaviourTransSetR ctx T P.
Proof.
  intros P ctx i T createH.
  unfold createBehaviourTransSet in createH.
  destruct (getProcessBehaviour P ctx) as [B |] eqn:H; [| inversion createH].
  apply behaviour_trans_set with (B := B); auto.
  - eapply createBehaviourTransSet_NoDup with (P := P). exists i.
    unfold createBehaviourTransSet. rewrite H. apply createH.
  - eapply createBehaviourTransSet'_BehaviourTransSetR'.
    + apply NoDup_cons; auto. apply NoDup_nil.
    + intros x H'. inversion H'.
    + intros x H'. unfold not. intro H''. inversion H''.
    + apply createH.
Qed.

Fixpoint getSetOutgoingTransitions (ctx : BehaviourExpressions)
  (t : set ProcessBehaviour) :=
  match t with
  | [] => []
  | B :: t' =>
    targetBehaviours (computeAllOutgoingTransitions B ctx) ++
    getSetOutgoingTransitions ctx t'
  end.

Fixpoint getSetTargetOutgoingBehaviours (ctx : BehaviourExpressions)
  (t : set ProcessBehaviour) :=
  match t with
  | [] => []
  | B :: t' =>
    getSetTargetOutgoingBehaviours ctx t' ++ computeAllOutgoingTransitions B ctx
  end.

Lemma getSetOutgoingTransitions_iff (ctx : BehaviourExpressions)
  (t: set ProcessBehaviour) :
  forall k, In k (getSetOutgoingTransitions ctx t) <->
  exists B, In k (targetBehaviours (computeAllOutgoingTransitions B ctx)) /\
            In B t.
Proof.
  intros k. split.
  - induction t; intros H; [inversion H|].
    simpl in H. apply in_app_iff in H. destruct H.
    + exists a. split; auto. left. trivial.
    + apply IHt in H. destruct H as [B [H H']]. exists B.
      split; auto. right. trivial.
  - intros H. destruct H as [B [H H']]. induction t; [inversion H' |].
    destruct H' as [H' | H'].
    + subst. simpl. apply in_app_iff. auto.
    + simpl. apply in_app_iff. auto.
Qed.

Lemma getSetOutgoingTransitions_equiv (ctx : BehaviourExpressions)
  (t t': set ProcessBehaviour) :
  t [=] t' ->
  getSetOutgoingTransitions ctx t [=] getSetOutgoingTransitions ctx t'.
Proof.
  intros H k. split; intros H';
  apply getSetOutgoingTransitions_iff;
  apply getSetOutgoingTransitions_iff in H'; destruct H' as [B [H' H'']];
    apply H in H''; exists B; auto.
Qed.

Lemma getSetTargetOutgoingBehaviours_iff (ctx : BehaviourExpressions)
  (t: set ProcessBehaviour) :
  forall k, In k (getSetTargetOutgoingBehaviours ctx t) <->
  exists B, In k (computeAllOutgoingTransitions B ctx) /\
            In B t.
Proof.
  intros k. split.
  - induction t; intros H; [inversion H|].
    simpl in H. apply in_app_iff in H. destruct H.
    + apply IHt in H. destruct H as [B [H H']]. exists B.
      split; auto. right. trivial.
    + exists a. split; auto. left. trivial.
  - intros H. destruct H as [B [H H']]. induction t; [inversion H' |].
    destruct H' as [H' | H'].
    + subst. simpl. apply in_app_iff. auto.
    + simpl. apply in_app_iff. auto.
Qed.

Lemma getSetTargetOutgoingBehaviours_equiv (ctx: BehaviourExpressions)
  (t t': set ProcessBehaviour) :
  t [=] t' ->
  getSetTargetOutgoingBehaviours ctx t [=]
  getSetTargetOutgoingBehaviours ctx t'.
Proof.
  intros H k. split; intros H';
  apply getSetTargetOutgoingBehaviours_iff;
  apply getSetTargetOutgoingBehaviours_iff in H'; destruct H' as [B [H' H'']];
  apply H in H''; exists B; auto.
Qed.

Lemma createBehaviourTransSet'_listStep' :
  forall (ctx : BehaviourExpressions) (i : nat)
    (t1 t2 v : set ProcessBehaviour),
    exists (t' : set ProcessBehaviour),
    createBehaviourTransSet' ctx (t1 ++ t2) v i =
    LETOPT T' <==
      createBehaviourTransSet' ctx (t2 ++ t') (rev t1 ++ v)
      (i - List.length t1) IN
        Some (T' ++ getSetTargetOutgoingBehaviours ctx t1) /\
    (forall B,
      In B t' <->
      In B (getSetOutgoingTransitions ctx t1) /\ ~ In B (t1 ++ t2 ++ v)) /\
    NoDup t'.
Proof.
  intros ctx i. induction i; intros t1 t2 v.
  - exists
      (nodup ProcessBehaviourDec
        (set_diff' ProcessBehaviourDec
          (getSetOutgoingTransitions ctx t1)
          (t1 ++ t2 ++ v))).
    split; auto; split; [| apply NoDup_nodup].
    intros B; split; intros H'.
    + eapply set_diff'_iff; apply nodup_In in H'; apply H'.
    + apply nodup_In; apply set_diff'_iff; auto.
  - destruct t1 as [| b t1'];
    [ exists []; rewrite app_nil_r; repeat rewrite app_nil_l;
      rewrite PeanoNat.Nat.sub_0_r;
      destruct (createBehaviourTransSet' ctx t2 v (S i));
      unfold getSetTargetOutgoingBehaviours; try rewrite app_nil_r;
      repeat split; try easy; apply NoDup_nil |];
    pose proof (set_union_elim2
      ProcessBehaviourDec
      (t1' ++ t2)
      (set_diff' ProcessBehaviourDec
        (targetBehaviours (computeAllOutgoingTransitions b ctx))
      (b :: v))) as H'.
    destruct H' as [x [union_eq [H' NoDup_x]]].
    pose proof (IHi t1' (t2 ++ x) (b :: v)) as IH.
    destruct IH as [t' [createH [H'' NoDup_t']]].
    rewrite <- app_assoc in createH. exists (x ++ t').
    split; [| split].
    + simpl. rewrite union_eq. repeat rewrite <- app_assoc. rewrite createH.
      simpl.
      destruct (createBehaviourTransSet' ctx (t2 ++ x ++ t') (rev t1' ++ b :: v)
            (i - Datatypes.length t1'));
      try rewrite <- app_assoc; trivial.
    +  intros B. split.
      * intros in_B. apply in_app_iff in in_B. destruct in_B as [in_B | in_B].
        { apply H' in in_B. destruct in_B as [in_B nin_B].
          apply set_diff'_iff in in_B. destruct in_B as [in_B nin_B']. split.
          { simpl. apply in_app_iff. auto. }
          { intros F. repeat (destruct F as [F | F];
            try (apply in_app_iff in F)).
            { elim nin_B'. subst. left. trivial. }
            { elim nin_B. apply in_app_iff. left. trivial. }
            { elim nin_B. apply in_app_iff. right. trivial. }
            { elim nin_B'. subst. right. trivial. } } }
        { apply H'' in in_B. destruct in_B as [in_B nin_B]. split.
          { simpl. apply in_app_iff. auto. }
          { intros F. repeat (destruct F as [F | F];
            try (apply in_app_iff in F)).
            { elim nin_B. repeat (apply in_app_iff; right). subst. left.
              trivial. }
            { elim nin_B. apply in_app_iff. left. trivial. }
            { elim nin_B. apply in_app_iff. right.
              do 2 (apply in_app_iff; left). trivial. }
            { elim nin_B. repeat (apply in_app_iff; right). subst. right.
              trivial. } } }
      * intros in_B. destruct in_B as [in_B nin_B]. simpl in in_B.
        apply in_app_iff. apply in_app_iff in in_B.
        destruct in_B as [in_B | in_B].
        { left. apply H'. split.
          { apply set_diff'_iff. split; auto. intros F. destruct F as [F | F].
            { elim nin_B. apply in_app_iff. left. left. trivial. }
            { elim nin_B. repeat (apply in_app_iff; right). trivial. } }
          { intros F. elim nin_B. right. rewrite app_assoc. apply in_app_iff.
            left. trivial. } }
        { destruct (In_dec ProcessBehaviourDec B x); auto.
          right. apply H''. split; auto. intros F. apply in_app_iff in F.
          repeat (destruct F as [F | F]; try (apply in_app_iff in F)).
          { elim nin_B. apply in_app_iff. left. right. trivial. }
          { elim nin_B. apply in_app_iff. right. apply in_app_iff. left.
            trivial. }
          { easy. }
          { elim nin_B. left. trivial. }
          { elim nin_B. repeat (apply in_app_iff; right). trivial. } }
    + apply NoDup_app2.
      assert (int' : forall k, In k t' -> ~ In k x).
      { intros k H'''. apply H'' in H'''. destruct H''' as [_ H''']. intros F.
        elim H'''. apply in_app_iff. right. apply in_app_iff. left.
        apply in_app_iff. right. auto. }
     apply NoDup_app; repeat split; auto.
Qed.

Lemma createBehaviourTransSet'_listStep :
  forall (ctx : BehaviourExpressions) (i : nat)  (t v : set ProcessBehaviour),
    exists (t' : set ProcessBehaviour),
    createBehaviourTransSet' ctx t v i =
    LETOPT T' <==
      createBehaviourTransSet' ctx t' (rev t ++ v) (i - List.length t) IN
      Some (T' ++ getSetTargetOutgoingBehaviours ctx t) /\
    (forall B, In B t' <->
               In B (getSetOutgoingTransitions ctx t) /\ ~ In B (t ++ v)) /\
    NoDup t'.
Proof.
  intros ctx i t v.
  pose proof (createBehaviourTransSet'_listStep' ctx i t [] v) as H.
  destruct H as [t' H].
  exists t'. repeat rewrite app_nil_r in H. repeat rewrite app_nil_l in H.
  apply H.
Qed.

Lemma Equiv_createBehaviourTransSet' :
  forall (ctx : BehaviourExpressions) (i : nat) (T : BehaviourTransSet)
    (to_visit visited to_visit' visited' : set ProcessBehaviour),
    createBehaviourTransSet' ctx to_visit visited i = Some T ->
    visited [=] visited' ->
    to_visit [=] to_visit' ->
    List.length to_visit = List.length to_visit' ->
    exists T',
      createBehaviourTransSet' ctx to_visit' visited' i = Some T' /\ T [=] T'.
Proof.
  intros ctx i.
  induction i using (well_founded_induction (well_founded_ltof nat (@id nat))).
  intros T to_visit visited to_visit' visited' H' visited_eqv to_visit_eqv
    length_eq.
  pose proof (createBehaviourTransSet'_listStep ctx i to_visit visited) as H''.
  destruct H'' as [t [createH1 H1]].
  destruct (createBehaviourTransSet' ctx t (rev to_visit ++ visited))
    eqn:createH1';
  [| rewrite createH1 in H'; inversion H'].
  pose proof (createBehaviourTransSet'_listStep ctx i to_visit' visited') as H''.
  destruct H'' as [t' [createH2 H2]]. destruct i; [inversion createH1|].
  destruct to_visit as [|B to_visit].
  - inversion H'. exists []. destruct to_visit' as [|B to_visit'].
    + split; auto. unfold Equiv. split; easy.
    + inversion length_eq.
  - assert (Hid : ltof nat id ((S i - Datatypes.length (B :: to_visit))) (S i)).
    { simpl. unfold ltof. unfold id.
      clear. generalize dependent (Datatypes.length to_visit).
      induction i; auto. destruct n; auto.
      apply PeanoNat.Nat.lt_lt_succ_r. simpl. apply IHi. }
    assert (H_eqv : getSetOutgoingTransitions ctx (B :: to_visit) [=]
                    getSetOutgoingTransitions ctx to_visit').
    { apply getSetOutgoingTransitions_equiv. auto. }
    assert (t [=] t').
    { destruct H1, H2. intros k; split; intro int;
      [apply H0 in int; apply H2 | apply H2 in int; apply H0];
      destruct int as [int nint]; split; try (apply H_eqv); auto;
      intros F; elim nint; apply in_app_iff; apply in_app_iff in F;
      destruct F as [F | F];
      try (left; apply to_visit_eqv; easy);
      right; apply visited_eqv; easy. }
    apply H with
      (T := b)
      (to_visit := t)
      (visited := rev (B :: to_visit) ++ visited)
      (to_visit' := t')
      (visited' := rev to_visit' ++ visited') in Hid; auto.
    + destruct Hid as [T' [createH2' H2']].
      rewrite length_eq in createH2'.
      rewrite createH2' in createH2.
      exists (T'  ++ getSetTargetOutgoingBehaviours ctx to_visit'). split; auto.
      rewrite createH1 in H'. inversion H'.
      assert (HT :
        getSetTargetOutgoingBehaviours ctx to_visit ++
          computeAllOutgoingTransitions B ctx =
        getSetTargetOutgoingBehaviours ctx (B :: to_visit)).
      { trivial. }
      rewrite HT. clear HT. apply Equiv_app; auto.
      apply getSetTargetOutgoingBehaviours_equiv; auto.
    + intros k. split; intros H_in; apply in_app_iff; apply in_app_iff in H_in;
      destruct H_in as [H_in | H_in];
      [apply in_rev in H_in | | apply in_rev in H_in |];
      try (left; apply -> in_rev; apply to_visit_eqv; easy);
      right; apply visited_eqv; easy.
    + destruct H1, H2.
      apply Equiv_eqLength; auto.
Qed.

Lemma targetBehaviours_iff :
  forall (T : BehaviourTransSet) (x : ProcessBehaviour),
    In x (targetBehaviours T) <-> exists t, In t T /\ to t = x.
Proof.
  intros T x. split.
  - intros H. induction T.
    + inversion H.
    + simpl in H. destruct a, p. apply set_add_iff in H. destruct H.
      * exists (p, e, p0). simpl. split; auto.
      * apply IHT in H. destruct H as [t [H H']]. exists t. simpl. split; auto.
  - intros H. destruct H as [t [H H']]. induction T; trivial.
    destruct H.
    + subst. simpl. destruct t, p. apply set_add_iff. left. trivial.
    + simpl. destruct a, p. apply set_add_iff. auto.
Qed.

Lemma Equiv_targetBehaviours :
  forall (T1 T2 : BehaviourTransSet),
    T1 [=] T2 ->
    targetBehaviours T1 [=] targetBehaviours T2.
Proof.
  intros T1 T2 H. unfold Equiv. intros x. split;
  intros H'; apply targetBehaviours_iff in H'; destruct H' as [t [H' to_t]];
  apply targetBehaviours_iff; exists t; split; auto; apply H; apply H'.
Qed.

Lemma createBehaviourTransSet'_succ :
  forall (ctx : BehaviourExpressions) (i : nat) (T : BehaviourTransSet)
    (to_visit visited : set ProcessBehaviour),
      createBehaviourTransSet' ctx to_visit visited i = Some T ->
      createBehaviourTransSet' ctx to_visit visited (S i) = Some T.
Proof.
  intros ctx i. induction i.
  - intros T to_visit visited H. inversion H.
  - intros T to_visit visited H. destruct to_visit as [|B to_visit'].
    + simpl. simpl in H. apply H.
    + simpl in H. remember (S i) as i'.
      destruct (createBehaviourTransSet' ctx
        (set_union ProcessBehaviourDec to_visit'
           (set_diff' ProcessBehaviourDec
              (targetBehaviours (computeAllOutgoingTransitions B ctx))
              (B :: visited))) (B :: visited) i) eqn:H';
      inversion H. apply IHi in H'.  simpl. rewrite H'. trivial.
Qed.

Lemma createBehaviourTransSet_succ :
  forall (P : ProcessName) (ctx : BehaviourExpressions) (T : BehaviourTransSet)
    (i : nat),
    createBehaviourTransSet ctx P i = Some T ->
    createBehaviourTransSet ctx P (S i) = Some T.
Proof.
  intros P ctx T i. unfold createBehaviourTransSet. intros H.
  destruct (getProcessBehaviour P ctx).
  - apply createBehaviourTransSet'_succ. apply H.
  - inversion H.
Qed.

Theorem BehaviourTransSetR'_createBehaviourTransSet' :
  forall (ctx : BehaviourExpressions) (T : BehaviourTransSet)
    (to_visit visited : set ProcessBehaviour),
    BehaviourTransSetR' ctx T to_visit visited ->
    (exists (i : nat) (T' : BehaviourTransSet),
      createBehaviourTransSet' ctx to_visit visited i = Some T' /\ T [=] T').
Proof.
  intros ctx T to_visit visited H.
  induction H.
  - exists 1, []. split; trivial. unfold Equiv. easy.
  - destruct IHBehaviourTransSetR' as [i [T''' [H' H'']]].
    exists (S i). simpl. unfold to_visit in H'.
    assert (T'_Equiv : T' [=] computeAllOutgoingTransitions B ctx).
    { unfold Equiv. intros x. split; intros inH;
      [ assert (from_x : from x = B); [eapply transFromB_from; apply inH | ] |
        assert (from_x : from x = B);
        [ eapply computeAllOutgoingTransitions_onlyTransFromB; apply inH |] ];
      destruct x, p; unfold from in from_x; simpl in from_x;
      rewrite from_x in *;
      [ apply computeAllOutgoingTransitions_iff; apply H |
        apply H; apply computeAllOutgoingTransitions_iff ];
      apply inH. }
    eapply Equiv_createBehaviourTransSet' in H'.
    + destruct H' as [T0 [H' Equiv_T0]]. rewrite H'.
      exists (T0 ++ (computeAllOutgoingTransitions B ctx)). split; trivial.
      unfold Equiv. intros x.
      assert (HT : In x T' -> In x T). { unfold T'. apply transFromB_subset. }
      apply set_diff'_subset with (A_dec := BehaviourTransDec) in HT.
      rewrite_eqv Equiv_T0 in H''. unfold T'' in H''. split.
      * intros inT. apply HT in inT. apply in_app_iff.
        destruct inT as [inT'' | inT'].
        { left. apply H''. apply inT''. }
        { right. eapply T'_Equiv. apply inT'. }
      * intros in_T0_comp. apply HT. apply in_app_iff in in_T0_comp.
        destruct in_T0_comp as [in_T0 | in_comp].
        { left. apply H''. apply in_T0. }
        { right. apply T'_Equiv. apply in_comp. }
    + unfold visited'. unfold Equiv. split; auto.
    + unfold Equiv. unfold visited'.
      clear visited' to_visit H'' T'' H0 H' i T'''.
      split; intros H'; apply set_union_iff in H'; apply set_union_iff;
      destruct H' as [H' | H']; auto; right; apply set_diff'_iff in H';
      apply set_diff'_iff; destruct H' as [H' H'']; split; auto;
      apply Equiv_targetBehaviours in T'_Equiv; apply T'_Equiv; auto.
    + apply set_union_eqLength. unfold visited'. apply set_diff'_eqv.
      apply Equiv_targetBehaviours; auto.
Qed.

Theorem BehaviourTransSetR_createBehaviourTransSet :
  forall (P : ProcessName) (ctx : BehaviourExpressions) (T : BehaviourTransSet),
    BehaviourTransSetR ctx T P ->
    (exists (i : nat) (T' : BehaviourTransSet),
      createBehaviourTransSet ctx P i = Some T' /\ T [=] T').
Proof.
  intros P ctx T H. inversion H as [ctx' T' P' B get_B NoDup_T H'].
  clear H0 H1 H2. unfold createBehaviourTransSet. rewrite <- get_B.
  apply BehaviourTransSetR'_createBehaviourTransSet'. apply H'.
Qed.
