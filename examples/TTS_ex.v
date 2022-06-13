Require Import TTS.
Require Import ltacs.
Require Import String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import LTS.
Require Import IOTS.
Require Import list_helper.
Require Import LTS_functions.
Require Import IOTS.
Require Import IOTS_ex.

Local Open Scope string.

Definition fig7_t1_LTS : LTS.
Proof.
   solve_LTS_rules
          [0;1;2;3;4]
          ["but"; "liq";"choc";"theta"]
          [(1, event "but", 2); (1, event "liq", 0); (1, event "choc", 0);
           (2, event "liq", 3); (2, event "theta", 0); (2, event "choc", 0);
           (3, event "theta", 4); (3, event "liq", 0); (3, event "choc", 0);
           (0, event "liq", 0); (0, event "choc", 0); (0, event "theta", 0);
           (4, event "liq", 4); (4, event "choc", 4); (4, event "theta", 4)]
          1.
Defined.

Definition fig7_t1_SC_LTS : SC_LTS.
Proof.
  apply (mkSC_LTS fig7_t1_LTS).
  unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'.
    + subst. proof_absurd_transition H5.
    + subst. expand_transition H3.
Defined.

Definition fig7_t1_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    fig7_t1_SC_LTS
    ["liq";"choc"]
    ["but"; "theta"].
Defined.

Definition fig7_t1_IOTS : IOTS.
Proof.
  apply (mkIOTS fig7_t1_IOLTS).
  unfold valid_iots. exists [0;1;2;3;4]. split.
  - apply der_LTS_r1. apply der_r1. intros s'. simpl q0. split.
    + intros H. destruct H as [ll H].
      repeat (
        induction ll; expand_seq_reachability H; try elem_in_list; auto; clear IHll).
    + intros H. expand_In H.
      * exists ["liq"]. proof_seq_reachability [(@nil nat, 0)] (@nil nat).
      * exists [ ]. proof_seq_reachability (@nil nat) (@nil nat).
      * exists ["but"]. proof_seq_reachability [(@nil nat, 2)] (@nil nat).
      * exists ["but"; "liq"].
        proof_seq_reachability [(@nil nat, 2); (@nil nat, 3)] (@nil nat).
      * exists ["but"; "liq"; "theta"].
        proof_seq_reachability [(@nil nat, 2); (@nil nat, 3); (@nil nat, 4)] (@nil nat).
  - simpl. repeat split; eapply has_reachability_to_some_other_r1;
    try (proof_seq_reachability [(@nil nat, 0)] (@nil nat)).
   + proof_seq_reachability [(@nil nat, 3)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 4)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 4)] (@nil nat).
Defined.

Definition fig7_t1_TTS : TTS.
Proof.
  create_TTS fig7_t1_IOTS 0 4 "theta".
Defined.

Example k1_passes_t1 : ind_passes fig4_k1_IOTS fig7_t1_TTS.
Proof.
  unfold ind_passes. intros sigma i' _ H.
  unfold ind_test_execution_trace in H. simpl in H.
  destruct sigma; expand_test_execution_seq_reachability H.
  destruct sigma; expand_test_execution_seq_reachability H.
  destruct sigma; expand_test_execution_seq_reachability H.
  induction sigma; expand_test_execution_seq_reachability H; auto.
Qed.

Example k3_fails_t1 : ~ ind_passes fig4_k3_IOTS fig7_t1_TTS.
Proof.
  unfold ind_passes. unfold ind_test_execution_trace. simpl. intros H.
  specialize (H ["but"; fig7_t1_TTS.(theta)] 2).
  apply H;
  [ unfold ind_test_run; exists 2; right; simpl fail_state;
    unfold ind_test_execution_trace; simpl q0 |];
  eapply test_execution_seq_reachability_r2 with (i2 := 2);
   try (eapply test_execution_one_step_reachability_r1;
    try (apply test_execution_empty_reachability_r1);
    apply test_execution_transition_r2; try elem_in_list; apply transition_r1;
    elem_in_list);
    apply test_execution_seq_reachability_r2 with (t2 := 0) (i2 := 2);
    try (apply test_execution_seq_reachability_r1;
      apply test_execution_empty_reachability_r1);
    eapply test_execution_one_step_reachability_r1;
      try (apply test_execution_empty_reachability_r1);
      apply test_execution_transition_r3; try elem_in_list; auto;
      apply transition_r1; simpl; elem_in_list.
Qed.

Local Close Scope string.