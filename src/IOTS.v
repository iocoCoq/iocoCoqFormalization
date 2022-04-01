Require Import LTS.
Require Import list_helper.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import String.
Require Import Bool.

Open Scope list_scope.

(* Definição 6*)
Section SectionIOLTS.

  Definition is_disjoint (L_i L_u : list label) : Prop :=
    Forall (fun x => ~ In x L_u) L_i.

  Record IOLTS : Type := mkIOLTS {
      sc_lts : SC_LTS
    ; L_i : list label
    ; L_u : list label
    ; disjoint_input_output_labels  : is_disjoint L_i L_u
    ; is_IOLTS                      : (L_i ++ L_u) [=] sc_lts.(lts).(L)
    ; no_repetition_L_i             : NoDup L_i
    ; no_repetition_L_u             : NoDup L_u
  }.

  Lemma is_disjoint_dec :
    forall (Li Lu : set label), {is_disjoint Li Lu} + {~ is_disjoint Li Lu}.
  Proof.
    intros Li Lu. unfold is_disjoint. apply Forall_dec.
    intros x. pose proof (in_dec string_dec x Lu) as in_dec. inversion in_dec.
    - right. unfold not. intros H'. auto.
    - left. auto.
  Qed.

  Definition create_IOLTS (sc_lts : SC_LTS) (Li Lu : list label) : option IOLTS :=
    match is_disjoint_dec Li Lu with
    | left h_is_disjoint =>
        match Equiv_dec (Li ++ Lu) sc_lts.(lts).(L) string_dec with
        | left h_is_IOLTS =>
            match NoDup_dec Li string_dec with
            | left h_NoDup_Li =>
                match NoDup_dec Lu string_dec with
                | left h_NoDup_Lu =>
                    Some (mkIOLTS
                            sc_lts
                            Li
                            Lu
                            h_is_disjoint
                            h_is_IOLTS
                            h_NoDup_Li
                            h_NoDup_Lu)
                | right _ => None
                end
            | right _ => None
            end
        | right _ => None
        end
    | right _ => None
    end.

  Theorem create_IOLTS_correct :
    forall (sc_lts : SC_LTS) (L_i L_u : list label),
      is_disjoint L_i L_u /\ (L_i ++ L_u) [=] sc_lts.(lts).(L) /\ NoDup L_i /\ NoDup L_u
      -> create_IOLTS sc_lts L_i L_u <> None.
  Proof.
    intros sc_lts Li Lu H. destruct H as [H [H2 [H3 H4]]].
    unfold create_IOLTS. destruct (is_disjoint_dec Li Lu);auto.
    destruct (Equiv_dec (Li ++ Lu) sc_lts.(lts).(L) string_dec);auto.
    destruct (NoDup_dec Li string_dec);auto.
    destruct (NoDup_dec Lu string_dec);auto.
    unfold not. intros H5. inversion H5.
  Qed.
End SectionIOLTS.

(* Definição 7*)
Section SectionIOTS.

  Fixpoint elem_reaches_another_with_all_labels (s : state) (ll : set label)
    (p : LTS) : Prop :=
  match ll with
  | []      =>  True
  | l :: t  =>  ind_has_reachability_to_some_other s [l] p /\
                         elem_reaches_another_with_all_labels s t p
  end.

  Fixpoint every_elem_reaches_some_other (ls : set state) (ll : set label)
    (p : LTS) : Prop :=
  match ls with
  | []      =>  True
  | h :: t  =>  elem_reaches_another_with_all_labels h ll p /\
                                    every_elem_reaches_some_other t ll p
  end.

  Definition valid_iots (p : IOLTS) : Prop :=
      exists (ls : set state),
          ind_der_LTS ls p.(sc_lts).(lts) /\
          every_elem_reaches_some_other ls p.(L_i) p.(sc_lts).(lts).

  Record IOTS : Type := mkIOTS {
      embedded_iolts                   : IOLTS
    ; input_actions_activated : valid_iots embedded_iolts
  }.
End SectionIOTS.

(* Definição 8*)
Inductive ind_quiescent : state -> IOLTS -> Prop :=
| quiescent_r1 : forall (s : state) (p : IOLTS),
              (forall (s' : state) (l : label),
                  In l p.(L_u) ->
                  ~ ind_transition s (event l) s' p.(sc_lts).(lts))->
                  (forall (s' : state),
                  ~ ind_transition s tau s' p.(sc_lts).(lts)) -> ind_quiescent s p.

Inductive ind_quiescent_traces : list label -> IOLTS -> Prop :=
| quiescent_trace_r1  : forall (ll : list label) (p : IOLTS) (ls : set state),
                ind_traces_LTS ll p.(sc_lts).(lts) /\
                    ind_after_LTS ll ls p.(sc_lts).(lts) /\
                        (exists (s : state), In s ls /\ 
                            ind_quiescent s p) ->  ind_quiescent_traces ll p.

(* Definição 9*)
Section SectionSuspensionIOLTS.

  Record s_IOLTS : Type := mksIOLTS {
      iolts : IOLTS
    ; Ts : set state
    ; Ts_complete_correct :
        forall (s : state),
          In s Ts <-> In s iolts.(sc_lts).(lts).(Q) /\ ind_quiescent s iolts
  }.

  Definition out_transition (q : state) (Lu : set label)
      (t : state * transition_label * state) : bool :=
    match t with
    | (q1, e, q2) =>
        if Nat.eqb q1 q
        then
          match e with
          | tau => true
          | event e' => set_mem string_dec e' Lu
          end
        else false
    end.

  Definition is_quiescent (l : list (state * transition_label * state))
      (Lu : list label) (q : state) : bool :=
    negb (existsb (out_transition q Lu) l).

  Definition create_Ts (iolts : IOLTS) : list state :=
    filter (is_quiescent iolts.(sc_lts).(lts).(T) iolts.(L_u)) iolts.(sc_lts).(lts).(Q).

  Lemma create_Ts_valid_del_transitions :
    forall (iolts : IOLTS) (s : state),
      In s (create_Ts iolts) -> In s iolts.(sc_lts).(lts).(Q).
  Proof.
    intros iolts s H. unfold create_Ts in H. apply filter_In in H.
    destruct H as [H _]. apply H.
  Qed.

  Lemma create_Ts_complete_correct :
    forall (iolts : IOLTS) (s : state), 
      In s (create_Ts iolts) <-> In s iolts.(sc_lts).(lts).(Q) /\ ind_quiescent s iolts.
  Proof.
    intros iolts s. split.
    - intros H. split.
      + apply create_Ts_valid_del_transitions. apply H.
      + apply filter_In in H. destruct H as [_ H].
        apply quiescent_r1; [intros s' l H' | intros s'];
        apply negb_true_iff in H; apply existsb_false in H; unfold not;
        intros H''; apply H; inversion H'';
        [ exists (s, event l, s') | exists (s, tau, s')];
        split; auto; simpl; rewrite PeanoNat.Nat.eqb_refl;
        [ apply (set_mem_correct2 string_dec); apply H' |
          reflexivity ].
    - intros H. destruct H as [H H']. apply filter_In. split.
      + apply H.
      + apply negb_true_iff. apply existsb_false. unfold not.
        intros H''. destruct H'' as [x H'']. destruct H'' as [H'' H'''].
        destruct x as [[q0 e] q1]. simpl in H'''.
        destruct (Nat.eqb q0 s) eqn: EQ.
        * apply EqNat.beq_nat_true in EQ. rewrite EQ in H''. inversion H'.
          destruct e.
          -- apply set_mem_correct1 in H'''. specialize (H0 q1 l).
             destruct H0; auto. apply transition_r1; auto.
          -- clear H'''. specialize (H1 q1). destruct H1.
             apply transition_r2. auto.
        * inversion H'''.
  Qed.

  Definition create_s_IOLTS (iolts : IOLTS) : s_IOLTS :=
    mksIOLTS
      iolts
      (create_Ts iolts)
      (create_Ts_complete_correct iolts).

  Theorem create_s_IOLTS_correct :
    forall (iolts : IOLTS), exists (s_iolts : s_IOLTS),
      create_s_IOLTS iolts = s_iolts.
  Proof.
    intros iolts. exists (create_s_IOLTS iolts). reflexivity.
  Qed.

End SectionSuspensionIOLTS.

Inductive s_label : Type :=
  | s_event : label -> s_label
  | delta : s_label.

Fixpoint s_trace_without_delta (l : list s_label) : list label :=
  match l with
  | [] => []
  | s_event e :: t => e :: s_trace_without_delta t
  | delta :: t => s_trace_without_delta t
  end.

Inductive ind_s_seq_reachability : state -> list s_label -> state -> s_IOLTS
    -> Prop :=
  | s_seq_reachability_r1  (s s' : state) (p : s_IOLTS) :
      ind_empty_reachability s s' p.(iolts).(sc_lts).(lts) ->
      ind_s_seq_reachability s [] s' p
  | s_seq_reachability_r2 (s s' si : state) (l: label) (t : list s_label) (p : s_IOLTS) :
      ind_one_step_reachability s l si p.(iolts).(sc_lts).(lts) ->
      ind_s_seq_reachability si t s' p ->
      ind_s_seq_reachability s (s_event l :: t) s' p
  | s_seq_reachability_r3 (s s' : state) (t : list s_label) (p : s_IOLTS) :
      In s p.(Ts) ->
      ind_s_seq_reachability s t s' p ->
      ind_s_seq_reachability s (delta :: t) s' p.

Lemma s_seq_reachability_eqv_seq_reachability :
  forall (s s': state) (l: list s_label) (p : s_IOLTS),
    ind_s_seq_reachability s l s' p ->
    ind_seq_reachability s (s_trace_without_delta l) s' p.(iolts).(sc_lts).(lts).
Proof.
  intros s s' l p H. induction H.
  - simpl. apply seq_reachability_r1; auto.
  - simpl. apply seq_reachability_r2 with (si := si); auto.
  - simpl; auto.
Qed.

Definition ind_s_traces (s : state) (t : list s_label) (p : s_IOLTS) : Prop :=
  exists (s' : state), ind_s_seq_reachability s t s' p.

Lemma s_trace_eqv_trace :
  forall (s : state) (l: list s_label) (p : s_IOLTS),
    ind_s_traces s l p ->
    ind_traces s (s_trace_without_delta l) p.(iolts).(sc_lts).(lts).
Proof.
  intros s l p H. unfold ind_s_traces in H. destruct H as [s' H].
  apply traces_r1. apply has_reachability_to_some_other_r1 with (s' := s').
  apply s_seq_reachability_eqv_seq_reachability; auto.
Qed.

Definition ind_s_traces_LTS (t : list s_label) (p : s_IOLTS) : Prop :=
  ind_s_traces p.(iolts).(sc_lts).(lts).(q0) t p.
