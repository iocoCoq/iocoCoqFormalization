Require Import IOTS.
Require Import LTS.
Require Import LTS_functions.
Require Import Bool BinPos BinNat PeanoNat Nnat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import String.
Require Import list_helper.

Inductive ind_out_one_state : state -> set s_label -> s_IOLTS -> Prop :=
  | out_one_state_r1 (s : state) (p : s_IOLTS) :
      In s p.(Ts) -> ind_out_one_state s [delta] p
  | out_one_state_r2 (s : state) (p : s_IOLTS) (so : set s_label) :
      ~ In s p.(Ts) ->
      ~ In delta so ->
      (forall (l : label),
        In (s_event l) so <->
        exists (s' : state),
          In l p.(iolts).(L_u) /\ ind_transition s (event l) s' p.(iolts).(sc_lts).(lts)) ->
      ind_out_one_state s so p.

Definition ind_out (Q : set state) (so : set s_label) (p : s_IOLTS) : Prop :=
  (forall (x : s_label),
    (In x so -> exists (s : state) (so' : set s_label),
                (In s Q /\ ind_out_one_state s so' p /\ In x so')))
    /\
    (forall (s : state), In s Q ->
      exists (so' : set s_label), ind_out_one_state s so' p /\
        forall (o : s_label), In o so' -> In o so).

Theorem s_label_dec : forall x y : s_label, {x = y} + {x <> y}.
Proof.
  decide equality.
  apply string_dec.
Defined.

Fixpoint f_out_one_state' (s : state) (lt: list transition) (Lu : set label)
    : set s_label :=
  match lt with
  | [] => []
  | (q1, e, q2) :: t =>
      if s =? q1
      then
        match e with
        | event e' =>
            if set_mem string_dec e' Lu
            then set_add s_label_dec (s_event e') (f_out_one_state' s t Lu)
            else f_out_one_state' s t Lu
        | tau => f_out_one_state' s t Lu
        end
     else f_out_one_state' s t Lu
  end.

Definition f_out_one_state (s : state) (p : s_IOLTS) : set s_label :=
  f_out_one_state' s p.(iolts).(sc_lts).(lts).(T) p.(iolts).(L_u).

Fixpoint f_out (ls : set state) (p : s_IOLTS) : set s_label :=
  match ls with
  | []     => []
  | h :: t =>
      if set_mem Nat.eq_dec h p.(Ts)
      then set_add s_label_dec delta (f_out t p)
      else set_union s_label_dec (f_out_one_state h p) (f_out t p)
  end.

Lemma f_out_one_state'_complete:
  forall (l : label) (Lu : set label) (s s': state) (T : list transition),
    In l Lu -> In (s, event l, s') T -> In (s_event l) (f_out_one_state' s T Lu).
Proof.
  intros l Lu s s' T H1 H2. induction T.
  - inversion H2.
  - destruct H2 as [H2 | H2]; simpl; destruct a, p.
    + destruct t; try inversion H2. subst. rewrite Nat.eqb_refl.
      eapply set_mem_correct2 in H1. rewrite H1. apply set_add_intro. left.
      reflexivity.
    + destruct (s =? s1); destruct t; try destruct (set_mem string_dec l0 Lu);
      try (apply set_add_intro; right); apply IHT; apply H2.
Qed.

Lemma f_out_one_state'_correct:
  forall (l : label) (Lu : set label) (s : state) (T : list transition),
    In (s_event l) (f_out_one_state' s T Lu) ->
    exists (s' : state), In l Lu /\ In (s, event l, s') T.
Proof.
  intros l Lu s T H. induction T.
  - inversion H.
  - simpl in H. destruct a, p. destruct (s =? s1) eqn:Eq_s; destruct t.
    + destruct (set_mem string_dec l0 Lu) eqn:H'.
       * apply set_add_iff in H. destruct H as [H|H].
         -- inversion H. apply set_mem_correct1 in H'. exists s0.
            split; try apply H'. left. apply Nat.eqb_eq in Eq_s. subst. reflexivity.
         -- apply IHT in H. destruct H as [s' H]. exists s'. destruct H. split; auto.
            right. auto.
       * apply IHT in H; destruct H as [s' H]; exists s'; destruct H; split; auto.
         right; auto.
    + apply IHT in H; destruct H as [s' H]; exists s'; destruct H; split; auto;
      right; auto.
    + apply IHT in H; destruct H as [s' H]; exists s'; destruct H; split; auto;
      right; auto.
    + apply IHT in H; destruct H as [s' H]; exists s'; destruct H; split; auto;
      right; auto.
Qed.

Lemma f_out_one_state'_no_delta:
  forall  (Lu : set label) (s : state) (T : list transition),
    ~ In delta (f_out_one_state' s T Lu).
Proof.
  intros Lu s T. induction T.
  - intros H. inversion H.
  - simpl. destruct a, p. destruct (s =? s1); destruct t; try apply IHT.
    destruct (set_mem string_dec l Lu); try apply IHT. intros H.
    apply set_add_iff in H. destruct H as [H | H]; try inversion H.
    apply IHT. apply H.
Qed.

Lemma ind_out_equiv_f_out:
  forall (Q : set state) (so : set s_label) (p : s_IOLTS),
    ind_out Q so p <-> so [=] f_out Q p.
Proof.
  intros.
  split.
  - intros H. unfold Equiv. intros x. split.
    + intros H'. unfold ind_out in H. destruct H as [H _].
      apply H in H'. destruct H' as [s [so' [H'_1 [H'_2 H'_3]]]].
      clear H. induction Q.
      * inversion H'_1.
      * destruct H'_1 as [H'_1 | H'_1]; subst.
        -- simpl. inversion H'_2; subst.
           ++ eapply set_mem_correct2 in H. rewrite H.
              destruct H'_3 as [H'_3 | H'_3]; inversion H'_3.
              apply set_add_intro. left. reflexivity.
           ++ eapply set_mem_complete2 in H. rewrite H. apply set_union_intro1.
              destruct x; [|apply H0 in H'_3; inversion H'_3 ].
              apply H1 in H'_3. unfold f_out_one_state.
              destruct H'_3 as [s' [H'_3_1 H'_3_2]]. inversion H'_3_2.
              apply f_out_one_state'_complete with (s' := s'); auto.
        -- simpl. destruct (set_mem Nat.eq_dec a (Ts p)).
           ++ apply set_add_intro. right. apply IHQ. apply H'_1.
           ++ apply set_union_intro2. apply IHQ. apply H'_1.
    + intros H'. unfold ind_out in H. destruct H as [_ H].
      induction Q; try inversion H'. simpl in H'.
      assert (H_aux : In a (a :: Q)). { left. reflexivity. } apply H in H_aux.
      destruct H_aux as [so' [H_1 H_2]].
      destruct (set_mem Nat.eq_dec a (Ts p)) eqn:H''.
      * apply set_add_iff in H'. destruct H' as [H' | H'].
        -- subst.
           apply set_mem_correct1 in H''. inversion H_1; subst.
           ++ apply H_2. left. reflexivity.
           ++ apply H0 in H''. inversion H''.
        -- apply IHQ.
           ++ intros s H'''. apply H. right. apply H'''.
           ++ apply H'.
      * apply set_union_iff in H'. destruct H' as [H' | H'].
        -- destruct x; [| apply f_out_one_state'_no_delta in H'; inversion H'].
           inversion H_1; subst.
           ++ apply set_mem_complete1 in H''. apply H'' in H0. inversion H0.
           ++ apply H_2. apply H2. apply f_out_one_state'_correct in H'.
              destruct H' as [s' H']. exists s'. destruct H' as [H'_1 H'_2].
              split; auto. apply transition_r1. apply H'_2.
        -- apply IHQ.
           ++ intros s H'''. apply H. right. apply H'''.
           ++ apply H'.
  - intros H. unfold ind_out. split.
    + intros x H'. apply H in H'. clear H. induction Q; [inversion H'|].
      simpl in H'. destruct (set_mem Nat.eq_dec a (Ts p)) eqn:H.
      * apply set_add_iff in H'. destruct H' as [H'|H'].
        -- subst. exists a, [delta]. repeat split; try (left; reflexivity).
           apply out_one_state_r1. apply set_mem_correct1 in H. apply H.
        -- apply IHQ in H'. destruct H' as [s [so' H']]. exists s, so'.
           destruct H' as [H'_1 [H'_2 H'_3]]. repeat split; auto. right. auto.
      * apply set_union_iff in H'. destruct H' as [H'|H'].
        -- exists a, (f_out_one_state a p).
           repeat split; try (left; reflexivity); auto.
           apply out_one_state_r2;
           [apply set_mem_complete1 in H; apply H |
            apply f_out_one_state'_no_delta |].
           intros l. split.
           ++ intros H''. apply f_out_one_state'_correct in H''.
              destruct H'' as [s' H'']. exists s'. destruct H'' as [H''_1 H''_2].
              split; auto. apply transition_r1. apply H''_2.
           ++ intros H''. destruct H'' as [s' [H''_1 H''_2]]. inversion H''_2.
              subst. eapply f_out_one_state'_complete; auto. apply H2.
        -- apply IHQ in H'. destruct H' as [s [so' H']]. exists s, so'.
           destruct H' as [H'_1 [H'_2 H'_3]]. repeat split; auto. right. auto.
    + intros s H'.
      assert (H'': forall x, In x (f_out Q p) -> In x so). { apply H. }
      clear H. induction Q; [inversion H'|]. destruct H' as [H'|H'].
      * subst. simpl in H''. destruct (set_mem Nat.eq_dec s (Ts p)) eqn:H.
        -- exists [delta]. split.
           ++ apply out_one_state_r1. apply set_mem_correct1 in H. apply H.
           ++ intros o H'. apply H''. destruct H' as [H'|H']; try inversion H'.
              apply set_add_iff. left. reflexivity.
        -- exists (f_out_one_state s p). split.
           ++ apply out_one_state_r2;
             [apply set_mem_complete1 in H; apply H | apply f_out_one_state'_no_delta |].
             intros l. split.
              ** intros H'. apply f_out_one_state'_correct in H'.  destruct H' as [s' H'].
              exists s'. destruct H' as [H'_1 H'_2]. split; auto.
              apply transition_r1. apply H'_2.
              ** intros H'. destruct H' as [s' [H'_1 H'_2]]. inversion H'_2.
                 subst. eapply f_out_one_state'_complete; auto. apply H2.
           ++ intros o H'. apply H''. apply set_union_iff. left. apply H'.
      * apply IHQ; auto. intros l H. apply H''. simpl.
        destruct (set_mem Nat.eq_dec a (Ts p)).
        -- apply set_add_iff. right. apply H.
        -- apply set_union_iff. right. apply H.
Qed.

Definition ind_s_after (s : state) (ll : list s_label) (ls : list state)
    (p : s_IOLTS) : Prop :=
  forall (a : state), ind_s_seq_reachability s ll a p <-> In a ls.

Definition ind_s_after_IOLTS (ll : list s_label) (ls : list state)
    (p : s_IOLTS) : Prop :=
  ind_s_after p.(iolts).(sc_lts).(lts).(q0) ll ls p.

Definition ind_ioco (i : IOTS) (s : IOLTS) : Prop :=
  forall (Qi Qs : set state) (t : list s_label) (out_i out_s : set s_label),
    ind_s_traces_LTS t (create_s_IOLTS s) ->
    ind_s_after_IOLTS t Qi (create_s_IOLTS i.(embedded_iolts)) ->
    ind_s_after_IOLTS t Qs (create_s_IOLTS s) ->
    ind_out Qi out_i (create_s_IOLTS i.(embedded_iolts)) ->
    ind_out Qs out_s (create_s_IOLTS s) ->
    incl out_i out_s.
Local Open Scope bool_scope.

Fixpoint f_after_one_s_label' (s : state) (l : s_label)
  (lt : list transition) (Ts : set state) : set state :=
  match l with
  | delta => if set_mem Nat.eq_dec s Ts
             then [s]
             else []
  | s_event e =>
      match lt with
      | []               =>  []
      | (a, l', b) :: t  =>  if (s =? a) && (b_transition_label_dec (event e) l')
                             then set_add Nat.eq_dec b (f_after_one_s_label' s l t Ts)
                             else f_after_one_s_label' s l t Ts
      end
  end.
Local Close Scope bool_scope.

Fixpoint f_after_one_s_label (ls : set state) (l : s_label)
    (lt : list transition) (Ts: set state): set state :=
  match ls with
  | []     => []
  | h :: t =>
      set_union
        Nat.eq_dec
        (f_after_one_s_label' h l lt Ts)
        (f_after_one_s_label t l lt Ts)
  end.

Fixpoint f_after_IOLTS' (ls : set state) (ll : list s_label) (p : s_IOLTS)
    : set state :=
  match ll with
  | []       => all_reachable_by_tau ls p.(iolts).(sc_lts).(lts)
  | h :: ll' =>
    let ls_tau := all_reachable_by_tau ls p.(iolts).(sc_lts).(lts) in
    let ls_after_one_step := 
      f_after_one_s_label ls_tau h p.(iolts).(sc_lts).(lts).(T) p.(Ts) in
      f_after_IOLTS' ls_after_one_step ll' p
  end.

Definition f_after_single_state_IOLTS (s : state) (ll : list s_label)
    (p : s_IOLTS) : set state :=
  f_after_IOLTS' [s] ll p.

Definition f_after_IOLTS (ll : list s_label) (p : s_IOLTS) : set state := 
  f_after_single_state_IOLTS p.(iolts).(sc_lts).(lts).(q0) ll p.

Lemma ind_after_IOLTS_equiv_f_after_IOLTS:
  forall (ll : list s_label) (ls : set state) (p : s_IOLTS),
    ind_s_after_IOLTS ll ls p <-> ls [=] f_after_IOLTS ll p.
Proof.
Admitted.

Definition f_ioco (i : IOTS) (s : IOLTS) : Prop :=
  forall (t : list s_label),
    ind_s_traces_LTS t (create_s_IOLTS s) ->
      incl (f_out
            (f_after_IOLTS t (create_s_IOLTS i.(embedded_iolts)))
            (create_s_IOLTS i.(embedded_iolts)))
           (f_out (f_after_IOLTS t (create_s_IOLTS s)) (create_s_IOLTS s)).
