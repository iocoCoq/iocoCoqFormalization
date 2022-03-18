Require Import LTS.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import RelationClasses.
Require Import BE_ltacs.
Require Import String.
Require Import Bool.

Open Scope list_scope.

(* Definição 6*)
Section SectionIOLTS.

  Definition is_disjoint (L_i L_u : list label) : Prop :=
    Forall (fun x => ~ In x L_u) L_i.

  Record IOLTS : Type := mkIOLTS {
      lts : LTS
    ; L_i : list label
    ; L_u : list label
    ; disjoint_input_output_labels  : is_disjoint L_i L_u
    ; is_IOLTS                      : (L_i ++ L_u) = lts.(L)
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

  Lemma NoDup_dec :
    forall {A : Type} (l : list A),
    (forall a1 a2 : A, { a1 = a2 } + { a1 <> a2 }) ->
     { NoDup l } + { ~ NoDup l }.
  Proof.
    intros A l Aeq_dec. induction l as [| h l' H].
    - left. apply NoDup_nil.
    - inversion H.
      + pose proof (in_dec Aeq_dec h l') as H'. inversion H'.
        * right. intros H''. inversion H''. auto.
        * left. apply NoDup_cons; auto.
      + right. intros H'. inversion H'. auto.
  Qed.

  Definition create_IOLTS (lts : LTS) (Li Lu : list label) : option IOLTS :=
    match is_disjoint_dec Li Lu with
    | left h_is_disjoint =>
        match list_eq_dec string_dec (Li ++ Lu) lts.(L) with
        | left h_is_IOLTS =>
            match NoDup_dec Li string_dec with
            | left h_NoDup_Li =>
                match NoDup_dec Lu string_dec with
                | left h_NoDup_Lu =>
                    Some (mkIOLTS
                            lts
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
    forall (lts : LTS) (L_i L_u : list label),
      is_disjoint L_i L_u /\ (L_i ++ L_u) = lts.(L) /\ NoDup L_i /\ NoDup L_u
      -> create_IOLTS lts L_i L_u <> None.
  Proof.
    intros lts Li Lu H. destruct H as [H [H2 [H3 H4]]].
    unfold create_IOLTS. destruct (is_disjoint_dec Li Lu);auto.
    destruct (list_eq_dec string_dec (Li ++ Lu) lts.(L));auto.
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
          ind_der_LTS ls p.(lts) /\
          every_elem_reaches_some_other ls p.(L_i) p.(lts).

  Record IOTS : Type := mkIOTS {
      embedded_iolts                   : IOLTS
    ; input_actions_activated : valid_iots embedded_iolts
  }.
End SectionIOTS.

Ltac exists_reachability :=
apply seq_reachability_r1; right ; left; split ; split ;
unfold not ; intros ; try (inversion H) ;
try reflexivity;
split; simpl; unfold not; try intro; try inversion H.

Ltac empty_reachability_left := left; reflexivity.

(* Definição 8*)
Inductive ind_quiescent : state -> IOLTS -> Prop :=
| quiescent_r1 : forall (s : state) (p : IOLTS),
              (forall (s' : state) (l : label),
                  In l p.(L_u) ->
                  ~ ind_transition s (event l) s' p.(lts))->
                  (forall (s' : state),
                  ~ ind_transition s tau s' p.(lts)) -> ind_quiescent s p.

Inductive ind_quiescent_traces : list label -> IOLTS -> Prop :=
| quiescent_trace_r1  : forall (ll : list label) (p : IOLTS) (ls : set state),
                ind_traces_LTS ll p.(lts) /\
                    ind_after_LTS ll ls p.(lts) /\
                        (exists (s : state), In s ls /\ 
                            ind_quiescent s p) ->  ind_quiescent_traces ll p.

(* Definição 9*)
Section SectionSuspensionIOLTS.

  Inductive delta_label : Type :=
  | delta : delta_label.

  (*Definition delta := "delta".*)

  Record s_IOLTS : Type := mksIOLTS {
      iolts               : IOLTS
    ; Ts                  :  list (state)
    (*; Q_del                 :=  iolts.(lts).(Q)*)
    (*; L_del                 :=  set_union string_dec s_iolts.(lts).(L) [delta]*)
    (*; Li_del                :=  s_iolts.(L_i)*)
    (*; Lu_del                :=  set_union string_dec s_iolts.(L_u) [delta]*)
    (*; T_del                 :=  s_iolts.(lts).(T) ++ Ts*)
    (*; delta_not_in_L        : ~ In delta s_iolts.(lts).(L)*)
    ; valid_del_transitions : forall (s : state), 
                                        In s Ts -> In s iolts.(lts).(Q)
    ; Ts_complete_correct   : forall (s : state), In s Ts <-> In s iolts.(lts).(Q) /\
                                        ind_quiescent s iolts
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
    filter (is_quiescent iolts.(lts).(T) iolts.(L_u)) iolts.(lts).(Q).

  Lemma create_Ts_valid_del_transitions :
    forall (iolts : IOLTS) (s : state), In s (create_Ts iolts) -> In s iolts.(lts).(Q).
  Proof.
    intros iolts s H. unfold create_Ts in H. apply filter_In in H.
    destruct H as [H _]. apply H.
  Qed.

  Lemma existsb_false:
    forall (A : Type) (f : A -> bool) (l : list A),
      existsb f l = false <-> ~ exists x : A, In x l /\ f x = true.
  Proof.
    intros. split.
    - intros H. pose proof (existsb_exists f l) as H'. apply iff_sym in H'.
      apply Bool.iff_reflect in H'. rewrite H in H'. inversion H'. auto.
    - intros H. pose proof (existsb_exists f l) as H'. apply iff_sym in H'.
      apply Bool.iff_reflect in H'. inversion H'.
      + unfold not in H. destruct H. apply H1.
      + reflexivity.
  Qed.

  Lemma create_Ts_complete_correct :
    forall (iolts : IOLTS) (s : state), 
      In s (create_Ts iolts) <-> In s iolts.(lts).(Q) /\ ind_quiescent s iolts.
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
      (create_Ts_valid_del_transitions iolts)
      (create_Ts_complete_correct iolts).

  Theorem create_s_IOLTS_correct :
    forall (iolts : IOLTS), exists (s_iolts : s_IOLTS),
      create_s_IOLTS iolts = s_iolts.
  Proof.
    intros iolts. exists (create_s_IOLTS iolts). reflexivity.
  Qed.

End SectionSuspensionIOLTS.

Inductive ind_s_traces : state -> list label -> s_IOLTS -> Prop :=
| s_traces_r1 : forall (s : state) (t : list label) (p : s_IOLTS),
                   ind_traces s t p.(iolts).(lts) -> ind_s_traces s t p.

Inductive ind_s_traces_LTS : list label -> s_IOLTS -> Prop :=
| s_traces_LTS_r1 : forall (t : list label) (p : s_IOLTS),
                   ind_traces_LTS t p.(iolts).(lts) -> ind_s_traces_LTS t p.
