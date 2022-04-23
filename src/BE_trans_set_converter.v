Require Import BE_semantics.
Require Import BE_syntax.
Require Import BE_trans_set.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import list_helper.
Require Import LTS.
Require Import PeanoNat.
Require Import String.

(* ======================== helper functions ================================ *)
Definition convertEvent (e : Event) : transition_label :=
  match e with
    | ExternalEvent name => event name
    | InternalEvent      => tau
  end.

Lemma convertEvent_inverse : forall e e',
  convertEvent e = convertEvent e' -> e = e'.
Proof.
  intros.
  destruct e, e'; inversion H; reflexivity.
Qed.

Fixpoint indexOf (B : ProcessBehaviour) (Lb : set ProcessBehaviour) : nat :=
  match Lb with
  | nil => 0
  | B' :: Lb' => if ProcessBehaviourDec B B' then 0 else S (indexOf B Lb')
  end.

Section Converter.

Variable ctx : BehaviourExpressions.
Variable behaviourTransitions : BehaviourTransSet.
Variable startProcess : ProcessName.
Hypothesis definitionOkWithTransition :
  BehaviourTransSetR ctx behaviourTransitions startProcess.

Fixpoint createBehaviourSet (T : BehaviourTransSet)
    : set ProcessBehaviour :=
  match T with
  | nil => nil
  | (B, _, B') :: T' =>
      set_add
        ProcessBehaviourDec
        B
        (set_add ProcessBehaviourDec B' (createBehaviourSet T'))
  end.

Definition behaviours := createBehaviourSet behaviourTransitions.

Definition idOf (B: ProcessBehaviour) : nat := indexOf B behaviours.

Definition startBehaviour : ProcessBehaviour :=
  match getProcessBehaviour startProcess ctx with
    | Some B => B
    | None   => stop
  end.

Fixpoint convertBehaviourTransitionsToLtsTransitions (L : BehaviourTransSet) 
    : list transition  :=
  match L with
  | nil => nil
  | (B, e, B') :: L' =>
      (idOf B, convertEvent e, idOf B') ::
      (convertBehaviourTransitionsToLtsTransitions L')
  end.

Fixpoint createLabelSet (L : BehaviourTransSet) : set label :=
  match L with
  | (_, ExternalEvent l, _) :: L' => set_add string_dec l (createLabelSet L')
  | (_, InternalEvent, _) :: L'   => createLabelSet L'
  | nil                           => nil
  end.

(* ============================ LTS parameters ============================== *)
Definition transitions :=
  convertBehaviourTransitionsToLtsTransitions behaviourTransitions.
Definition states := seq 0 (List.length behaviours).
Definition labels := createLabelSet behaviourTransitions.
Definition startState := idOf startBehaviour.

(* =============================== LTS lemmas =============================== *)
Lemma StateSetNotEmpty : behaviourTransitions <> nil -> states <> nil.
Proof.
  intros transNotEmpty.
  unfold states.
  unfold behaviours.
  destruct behaviourTransitions as [| hd tl]; try easy.
  clear transNotEmpty.
  destruct (createBehaviourSet (hd :: tl)) eqn:H.
  - simpl in H.
    destruct hd, p.
    destruct (set_add ProcessBehaviourDec p0 (createBehaviourSet tl)).
    + simpl in H.
      easy.
    + simpl in H.
      destruct (ProcessBehaviourDec p p1); easy.
  - simpl.
    easy.
Qed.

Lemma StateRepresentingBehaviourInStateSet :
  forall B, In B behaviours -> In (idOf B) states.
Proof.
  clear.
  unfold idOf.
  intros.
  unfold states.
  apply in_seq.
  simpl. split; try apply Nat.le_0_l.
  induction behaviours.
  - intros. inversion H.
  - intros. simpl. destruct (ProcessBehaviourDec B a).
    + apply Nat.lt_0_succ.
    + apply Lt.lt_n_S. apply IHs. destruct H; try trivial.
      symmetry in H. easy.
Qed.

Lemma AllBehavioursInBehaviourSet :
  forall (B1 B2 : ProcessBehaviour) (e : Event) (T : BehaviourTransSet),
    In (B1, e, B2) T ->
    In B1 (createBehaviourSet T) /\ In B2 (createBehaviourSet T).
Proof.
  clear.
  intros.
  induction T.
  - inversion H.
  - destruct H.
    + simpl. destruct a, p. inversion H. subst. split; apply set_add_iff.
      * left. reflexivity.
      * right. apply set_add_iff. left. reflexivity.
    + apply IHT in H. destruct H. simpl. destruct a, p.
      split; repeat (apply set_add_iff; right); trivial.
Qed.

Lemma AllEventsInLabelsSet :
  forall (B1 B2 : ProcessBehaviour) (e : EventName),
    In (B1, ExternalEvent e, B2) behaviourTransitions ->
    In e labels.
Proof.
  unfold labels.
  unfold transitions.
  clear.
  intros.
  induction behaviourTransitions; trivial.
  simpl. destruct a, p, e0.
  - apply IHb.
    destruct H.
    + inversion H.
    + apply H.
  - destruct H.
    + inversion H. apply set_add_iff. left. reflexivity.
    + apply set_add_iff. right. apply IHb. apply H.
Qed.

Lemma StartBehaviourInBehaviourSet:
  behaviourTransitions <> nil ->
  In startBehaviour behaviours.
Proof.
  intros.
  unfold behaviours.
  pose proof AllBehavioursInBehaviourSet as inBehaviourSet.
  destruct behaviourTransitions as [ | hd tl]; try easy.
  clear H.
  inversion definitionOkWithTransition as [? ? ? ? Behaviour _ H].
  clear H0 H1 H2.
  subst.
  clear definitionOkWithTransition.
  unfold startBehaviour.
  rewrite <- Behaviour.
  inversion H. subst.
  destruct (transFromB B (hd::tl)) eqn:H'.
  - unfold T' in to_visit. simpl in to_visit. unfold to_visit in H6.
    inversion H6.
  - revert H'. revert inBehaviourSet. clear. intros inBehaviourSet H.
    assert (H' : transFromB B (hd :: tl) <> []).
    { unfold not. intros. rewrite H in H0. inversion H0. }
    apply transFromBNotEmpty in H'. destruct H' as [e [B' H']].
    apply inBehaviourSet in H'. destruct H' as [H' _]. apply H'.
Qed.

Local Open Scope type_scope.

Lemma EachLtsTransitionHasAnEquivalentBehaviour :
  forall (x : BehaviourTransSet) (b1 b2 : state) (l : transition_label) ,
    (forall t, In t x -> In t behaviourTransitions) ->
    In (b1, l, b2) (convertBehaviourTransitionsToLtsTransitions x) ->
    exists (B1 B2 : ProcessBehaviour) (e : Event),
      In (B1, e, B2) x /\ b1 = idOf B1 /\ b2 = idOf B2 /\ l = convertEvent e.
Proof.
  clear.
  unfold idOf.
  intros.
  induction x.
  - inversion H0.
  - simpl in H0.
    destruct a, p.
    simpl in H0.
    destruct H0.
    + exists p, p0, e. inversion H0.
      repeat split; try reflexivity.
      simpl. left. reflexivity.
    + assert((forall t : BehaviourTrans, In t x -> In t behaviourTransitions)).
      {  intros. apply H. right. apply H1. }
      apply IHx in H1; auto.
      destruct H1 as [B1 [B2 [ e' ]]].
      destruct H1 as [H1 [H2 [H3 ]]].
      exists B1, B2, e'.
      repeat split; auto.
      right. apply H1.
Qed.

Local Close Scope type_scope.

Lemma ValidTransitionsEquivalence :
forall (x : list transition) (st : list state) (lb : list label),
  (forall t, In t x -> In t transitions) ->
  (forall (b1 b2 : state) (l : label),
    In (b1, event l, b2) transitions -> In b1 st /\ In b2 st /\ In l lb) ->
  (forall (b1 b2 : state), In (b1, tau, b2) transitions -> In b1 st /\ In b2 st) ->
  each_transition_is_valid x st lb.
Proof.
  clear.
  intros.
  induction x.
  - simpl. apply I.
  - destruct a, p.
    destruct t.
    + simpl. pose proof (H0 s0 s l).
      assert (H3 : In (s0, event l, s) transitions).
      { apply H. simpl. left. reflexivity. }
      apply H2 in H3.
      destruct H3 as [H4 [H5 H6] ].
      repeat split; trivial.
      apply IHx.
      intros.
      apply H.
      simpl. right. apply H3.
    + simpl. pose proof (H1 s0 s).
      assert (H3 : In (s0, tau, s) transitions).
      { apply H. simpl. left. reflexivity. }
      apply H2 in H3.
      destruct H3 as [H4 H5].
      repeat split; trivial.
      apply IHx.
      intros.
      apply H.
      simpl. right. apply H3.
Qed.

Lemma AllEventTransitionsAreValid :
  forall (b1 b2 : state) (l : label),
    In (b1, event l, b2) transitions ->
    In b1 states /\ In b2 states /\ In l labels.
Proof.
  unfold transitions.
  unfold behaviours.
  intros.
  assert (forall x, In x behaviourTransitions -> In x behaviourTransitions).
  { trivial. }
  eapply EachLtsTransitionHasAnEquivalentBehaviour in H0; try apply H.
  destruct H0 as [B1 [B2 [e [H1 [H2 [H3] ] ] ] ] ].
  assert(H5 : In (B1, e, B2) behaviourTransitions). { apply H1. }
  apply AllBehavioursInBehaviourSet in H1.
  destruct H1 as [H1 H1'].
  apply StateRepresentingBehaviourInStateSet in H1.
  apply StateRepresentingBehaviourInStateSet in H1'.
  unfold behaviours in H1, H1'.
  destruct e; inversion H0.
  apply AllEventsInLabelsSet in H5.
  subst.
  repeat split; trivial.
Qed.

Lemma AllInternalTransitionsAreValid :
  forall (b1 b2 : state),
    In (b1, tau, b2) transitions -> In b1 states /\ In b2 states.
Proof.
  unfold transitions.
  unfold behaviours.
  intros.
  assert (forall x, In x behaviourTransitions -> In x behaviourTransitions).
  { trivial. }
  eapply EachLtsTransitionHasAnEquivalentBehaviour in H0; try apply H.
  destruct H0 as [B1 [B2 [e [H1 [H2 [H3] ] ] ] ] ].
  apply AllBehavioursInBehaviourSet in H1.
  destruct H1 as [H1 H1'].
  apply StateRepresentingBehaviourInStateSet in H1.
  apply StateRepresentingBehaviourInStateSet in H1'.
  unfold behaviours in H1, H1'.
  destruct e; inversion H0.
  subst.
  repeat split; trivial.
Qed.

Lemma StartStateInStateSet :
  behaviourTransitions <> nil -> In startState states.
Proof.
  intros transNotEmpty.
  apply StateRepresentingBehaviourInStateSet.
  apply StartBehaviourInBehaviourSet.
  auto.
Qed.

Lemma NoRepetitionStates : NoDup states.
Proof.
  apply seq_NoDup.
Qed.

Lemma NoRepetitionLabels : NoDup labels.
Proof.
  clear.
  unfold labels.
  induction behaviourTransitions.
  - simpl. apply NoDup_nil.
  - simpl. destruct a, p.
    destruct e.
    + apply IHb.
    + apply set_add_nodup. apply IHb.
Qed.

Lemma idOf_inverse :
  forall (B1 B2 : ProcessBehaviour),
    In B1 behaviours -> idOf B1 = idOf B2 -> B1 = B2.
Proof.
  clear.
  unfold idOf.
  intros.
  induction behaviours.
  - inversion H.
  - simpl in H. destruct H.
    + simpl in H0. destruct (ProcessBehaviourDec B1 a); subst.
      * destruct (ProcessBehaviourDec B2 B1); easy.
      * easy.
    + simpl in H0. destruct (ProcessBehaviourDec B1 a); subst.
      * destruct (ProcessBehaviourDec B2 a); easy.
      * destruct (ProcessBehaviourDec B2 a); try easy.
        inversion H0.
        apply IHs; auto.
Qed.

Lemma NoRepetitionTransitions' :
forall (x : BehaviourTransSet),
  (forall t, In t x -> In t behaviourTransitions) ->
  (NoDup x -> NoDup (convertBehaviourTransitionsToLtsTransitions x)).
Proof.
  clear.
  intros.
  induction x.
  - simpl. apply NoDup_nil.
  - simpl. destruct a, p.
    apply NoDup_cons.
    + unfold not. intros.
      apply EachLtsTransitionHasAnEquivalentBehaviour in H1.
      * destruct H1 as [p' [p0' [e']]].
        destruct H1 as [H1 [H2 [H3]]].
        assert(H' : In (p', e', p0') behaviourTransitions).
        { apply H. right. auto. }
        apply AllBehavioursInBehaviourSet in H'.
        destruct H' as [H' H'' ].
        apply idOf_inverse with (B2 := p) in H'; auto.
        apply idOf_inverse with (B2 := p0) in H''; auto.
        apply convertEvent_inverse in H4.
        subst. inversion H0. apply H6 in H1. inversion H1.
      * intros. apply H. right. apply H2.
    + inversion H0. apply IHx; auto. intros. apply H. right. apply H5.
Qed.

Lemma NoRepetitionTransitions : NoDup transitions.
Proof.
  inversion definitionOkWithTransition as [? T P B _ H _].
  clear H0 H1 H2.
  clear definitionOkWithTransition startProcess ctx.
  unfold transitions.
  apply NoRepetitionTransitions'.
  - intros. apply H0.
  - apply H.
Qed.

Definition createLtsFromBehaviourTransSet : LTS.
Proof.
  destruct behaviourTransitions eqn:H.
  - clear.
    refine (mkLTS [0] [] [] 0 _ _ _ _ _ _); try apply NoDup_nil.
    + unfold not. intros. inversion H.
    + simpl. left. reflexivity.
    + simpl. apply I.
    + apply NoDup_cons.
      * unfold not. intros H. inversion H.
      * apply NoDup_nil.
  - refine (mkLTS states labels transitions startState _ _ _ _ _ _);
    rewrite <- H in definitionOkWithTransition.
    + apply StateSetNotEmpty. rewrite H. unfold not. intros H'. inversion H'.
    + apply StartStateInStateSet. rewrite H. unfold not. intros H'.
      inversion H'.
    + eapply ValidTransitionsEquivalence.
      * intros. apply H0.
      * apply AllEventTransitionsAreValid.
      * apply AllInternalTransitionsAreValid.
    + apply NoRepetitionStates.
    + apply NoRepetitionLabels.
    + apply NoRepetitionTransitions.
Defined.

(*behaviours
  In (B1, e, B2) T -> In B1 behaviours /\ In B2 behaviours
  In B behaviours -> exists B' e, In (B, e, B') T \/ In (B', e, B) T
states
  In x states -> exists B, In B behaviours /\ idOf B = x
  In B behaviours -> In (idOf B) states
  In B1 behaviour -> idOf B1 = idOf B2 <-> B1 = B2
labels
  In (B1, ExternalEvent e, B2) T -> In e labels
  In e labels -> exists B1 B2, In (B1, ExternalEvent e, B2) T
transitions
  In (B1, e, B2) T -> In (idOf B1, convert e, idOf B2) transitions
  In (b1, l, b2) transitions -> 
    exists B1 e B2,
      In (B1, e, B2) T /\ idOf B1 = b1 /\ idOf B2 = b2 /\ convert e = l
startState
  P ::= B -> startState = idOf B *)

(* ========= createLtsFromBehaviourTransSet correctness theorems ============ *)

(* behaviours theorems *)

Theorem behaviours_complete:
  forall (B1 B2 : ProcessBehaviour) (e : Event),
    In (B1, e, B2) behaviourTransitions -> In B1 behaviours /\ In B2 behaviours.
Proof.
  unfold behaviours.
  intros.
  apply AllBehavioursInBehaviourSet with (e:=e).
  auto.
Qed.

Local Open Scope type_scope.

Theorem behaviours_correct:
  forall (B : ProcessBehaviour),
    In B behaviours ->
    exists (B' : ProcessBehaviour) (e : Event),
      In (B, e, B') behaviourTransitions \/ In (B', e, B) behaviourTransitions.
Proof.
  clear.
  unfold behaviours.
  intros B H.
  induction behaviourTransitions as [| a b IHb].
  - inversion H.
  - simpl in H. destruct a as [[B1 e] B2]. apply set_add_elim in H.
    destruct H as [H | H].
    + subst. exists B2, e. left. left. reflexivity.
    + apply set_add_elim in H. destruct H as [H | H].
      * subst. exists B1, e. right. left. reflexivity.
      * apply IHb in H. destruct H as [B' [e' H]]. exists B', e'.
        destruct H as [H | H]; [left | right]; right; apply H.
Qed.

(* states theorem *)

Lemma NoDup_behaviours: NoDup behaviours.
Proof.
  clear. unfold behaviours. induction behaviourTransitions.
  - simpl. apply NoDup_nil.
  -  simpl. destruct a, p. do 2 apply set_add_nodup. apply IHb.
Qed.

Theorem states_correct:
  forall (x : nat), In x states -> exists B, In B behaviours /\ idOf B = x.
Proof.
  clear.
  unfold states.
  unfold idOf.
  intros x H.
  pose proof (NoDup_behaviours) as H'''.
  remember behaviours as bs' eqn:H'. rewrite H' in H.
  assert(Heq: Datatypes.length behaviours = Datatypes.length bs').
  { rewrite H'. reflexivity. }
  clear H'. generalize dependent bs'. induction behaviours as [|B bs IHbs];
  intros bs' H''' Heq.
  - inversion H.
  - simpl Datatypes.length in H.
    pose proof (Nat.add_comm 1 (Datatypes.length bs)) as H'. simpl in H'.
    rewrite H' in H. rewrite seq_app in H. simpl in H. apply in_app_or in H.
    simpl in Heq.
    assert (H'': exists (B' : ProcessBehaviour) (bs'' : list ProcessBehaviour),
            bs' = bs'' ++ [B']).
    { clear IHbs H' H B H'''. generalize dependent bs.
      induction bs'; intros bs H; [inversion H |]. simpl in H. inversion H.
      destruct bs'; [exists a, []; reflexivity |]. destruct bs; [inversion H1 |].
      apply IHbs' in H1. destruct H1 as [B' [bs'' H']]. exists B', (a :: bs'').
      rewrite H'. simpl. reflexivity. }
    destruct H'' as [B' [bs'' H'']]. rewrite H'' in Heq. rewrite app_length in Heq.
    simpl in Heq. rewrite <- plus_n_Sm in Heq. rewrite Nat.add_comm in Heq.
    simpl in Heq.
    destruct H as [H | H].
    + clear B.
      rewrite H'' in H'''. apply NoDup_app in H'''. destruct H''' as [H''' _].
      inversion Heq. eapply IHbs in H; [| apply H''' | apply H1]. clear H'''.
      destruct H as [B H].
      rewrite H''. exists B. clear IHbs bs' Heq H'' H1 H'. destruct H as [H H'].
      split; [apply in_or_app; auto |]. generalize dependent x.
      induction bs''; [inversion H |]. intros x H'. simpl in H'. simpl in H.
      simpl. destruct (ProcessBehaviourDec B a); auto. destruct H as [H | H].
      * elim n. auto.
      * destruct x; [inversion H'|]. inversion H'. apply f_equal. apply IHbs''; auto.
    + destruct H; [| inversion H]. clear IHbs H'. inversion Heq. rewrite H in H1.
      rewrite H1. rewrite H''. rewrite H'' in H'''. clear H Heq bs H'' H1 x B.
      exists B'. induction bs''.
      * split; simpl; auto. destruct (ProcessBehaviourDec B' B'); easy.
      * simpl in H'''. inversion H'''. apply IHbs'' in H2.
        destruct H2 as [H' H'']. simpl. rewrite H''. split; auto.
        destruct (ProcessBehaviourDec B' a); auto. subst. easy.
Qed.

Theorem states_complete : forall B, In B behaviours -> In (idOf B) states.
Proof.
  apply StateRepresentingBehaviourInStateSet.
Qed.

(* idOf *)
Theorem idOf_injective:
  forall B1 B2, In B1 behaviours -> idOf B1 = idOf B2 <-> B1 = B2.
Proof.
  split.
  - apply idOf_inverse. apply H.
  - intros H'. rewrite H'. easy.
Qed.

(* labels *)
Theorem labels_complete:
  forall (B1 B2 : ProcessBehaviour) (e : EventName),
    In (B1, ExternalEvent e, B2) behaviourTransitions -> In e labels.
Proof.
  apply AllEventsInLabelsSet.
Qed.

Theorem labels_correct:
  forall e,
    In e labels -> exists B1 B2, In (B1, ExternalEvent e, B2) behaviourTransitions.
Proof.
  clear.
  unfold labels. intros e H. induction behaviourTransitions.
  - inversion H.
  - simpl in H. destruct a, p. destruct e0.
    + apply IHb in H. destruct H as [B1 [B2 H]]. exists B1, B2. right. auto.
    + apply set_add_elim in H. destruct H as [H | H].
      * exists p, p0. rewrite H. left. auto.
      * apply IHb in H. destruct H as [B1 [B2 H]]. exists B1, B2. right. auto.
Qed.

(* transitions *)
Theorem transitions_complete:
  forall (B1 B2 : ProcessBehaviour) (e : Event),
    In (B1, e, B2) behaviourTransitions ->
    In (idOf B1, convertEvent e, idOf B2) transitions.
Proof.
  clear. unfold transitions. induction behaviourTransitions.
  - intros B1 B2 e H. inversion H.
  - intros B1 B2 e H. destruct a, p. destruct H as [H | H].
    + inversion H. simpl. left. reflexivity.
    + simpl. right. apply IHb. apply H.
Qed.

Theorem transitions_correct:
  forall (b1 b2 : nat) (l : transition_label),
  In (b1, l, b2) transitions ->
    exists B1 B2 e,
      In (B1, e, B2) behaviourTransitions /\
      b1 = idOf B1 /\ b2 = idOf B2 /\ l = convertEvent e.
Proof.
  clear. unfold transitions. intros b1 b2 l H.
  apply EachLtsTransitionHasAnEquivalentBehaviour in H; auto.
Qed.

(* startState *)
Theorem startState_correct:
  forall B, Some B = getProcessBehaviour startProcess ctx -> startState = idOf B.
Proof.
  clear. intros B H. unfold startState. unfold startBehaviour. rewrite <- H. auto.
Qed.

End Converter.
