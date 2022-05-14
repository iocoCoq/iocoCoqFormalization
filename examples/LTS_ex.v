Require Import ltacs.
Require Import String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import LTS.
Require Import LTS_functions.
Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.

Local Open Scope string.

Definition fig2_r' : LTS.
Proof.
  solve_LTS_rules
          [0;1;2;3;4;5]
          ["but";"liq";"choc"]
          [(0, event "but", 1);(1, event "liq", 3);
            (0, event "but", 2);(2, event "but", 4);(4, event "choc", 5)]
          0.
Defined.

Definition fig2_r_BE : BehaviourExpressions.
Proof.
  create_behaviour_expressions
    ["fig2_r" ::= "but";; "liq";; STOP [] "but";; "but";; "choc";; STOP].
Defined.

Definition fig2_r : LTS.
Proof. create_LTS_from_BE fig2_r_BE "fig2_r" 6. Defined.

Definition fig2_r_SC_LTS : SC_LTS.
Proof.
  apply (mkSC_LTS fig2_r).
  unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'; subst.
    + proof_absurd_transition H5.
    + proof_absurd_transition H3.
Defined.

Definition fig4_k1_LTS : LTS.
Proof.
   solve_LTS_rules
          [0;1;2]
          ["but"; "liq";"choc"]
          [(0, event "but",1); (1, event "but", 1); (1, event "liq", 2);
           (2, event "but",2)]
          0.
Defined.

Definition fig4_k1_SC_LTS : SC_LTS.
Proof.
  apply (mkSC_LTS fig4_k1_LTS).
  unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'.
    + subst. proof_absurd_transition H5.
    + subst. expand_transition H3.
Defined.

Definition fig4_k3_LTS : LTS.
Proof.
   solve_LTS_rules
          [0;1;2;3;4;5]
          ["but"; "liq";"choc"]
          [(0, event "but",1);(1, event "liq",3);
            (0, event "but",2);(2, event "but",4);(4, event "choc",5);
            (1, event "but", 1); (3, event "but", 3); (4, event "but", 4);
            (5, event "but", 5)]
          0.
Defined.

Definition fig4_k3_SC_LTS : SC_LTS.
Proof.
  apply (mkSC_LTS fig4_k3_LTS).
  unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'.
    + subst. proof_absurd_transition H5.
    + subst. expand_transition H3.
Defined.

Definition mLTS : LTS.
Proof.
  solve_LTS_rules
          [0;1;2;3;4;5]
          ["but";"liq";"choc"]
          [(0, event "but", 1);(1, event "liq", 3);
            (0, event "but", 2);(2, event "but", 4);
            (4, event "choc", 5); (2, tau, 5); (5, tau, 3)]
          0.
Defined.

Example test_f_init :
  f_init 0 fig2_r = [event "liq"].
Proof.
  vm_compute. auto.
Qed.

Example test_f_init_LTS :
  f_init_LTS fig2_r = [ event "but"].
Proof.
  unfold f_init_LTS. vm_compute. reflexivity.
Qed.

Example test_ind_init :
  ind_init 2 [ event "but"; tau] mLTS.
Proof.
  proof_ind_init [4;5].
Qed.

Example teste_ind_transition :
  ind_transition 3 (event "choc") 4 fig2_r.
Proof.
   apply transition_r1. vm_compute. elem_in_list.
Qed.

Example test_ind_empty_reachability :
  ind_empty_reachability 3 3 mLTS.
Proof.
  apply empty_reachability_r1.
Qed.

Example test_ind_empty_reachability_2 :
  ind_empty_reachability 4 4 mLTS.
Proof.
  apply empty_reachability_r1.
Qed.

Example test_ind_one_step :
  ind_one_step_reachability 4 "choc" 3 mLTS.
Proof.
  eapply one_step_reachability_r1; auto.
  - apply empty_reachability_r1.
  - apply transition_r1. simpl. elem_in_list.
  - eapply empty_reachability_r2.
    + elem_in_list.
    + apply empty_reachability_r1.
Qed.


Example test_ind_traces :
  ind_traces 1 ["but"; "but"] fig2_r.
Proof.
  apply traces_r1. eapply has_reachability_to_some_other_r1.
  eapply seq_reachability_r2.
  - apply one_step_reachability_r1 with (s1 := 1) (s2 := 2); 
    try (apply empty_reachability_r1). apply transition_r1. vm_compute. elem_in_list.
  - eapply seq_reachability_r2.
    + apply one_step_reachability_r1 with (s1 := 2) (s2 := 3);
      try (apply empty_reachability_r1). apply transition_r1. vm_compute. elem_in_list.
    + apply seq_reachability_r1. apply empty_reachability_r1.
Qed.

Example ind_transition_test : 
  ~ ind_transition 6 tau 2 mLTS.
Proof.
  unfold not; intros Htr.
  proof_absurd_transition Htr.
Qed.

Example teste_ind_empty_reachability :
  ~ ind_empty_reachability 2 0 mLTS.
Proof.
  unfold not; intros _Haer. proof_absurd_empty_reachability _Haer.
Qed.

Example teste_ind_transition_seq :
  ~ ind_transition_seq 1 [ event "liq"; event "but"; event "but"] 4 mLTS.
Proof.
  unfold not. intros H. proof_absurd_transition_seq H.
Qed.

Example test_ind_refuses :
  ind_refuses fig2_r.(Q) [ event "but"; event "choc"] fig2_r.
Proof.
  apply refuses_r1 with (s := 0).
  - elem_in_list.
  - simpl; repeat split; unfold not; intros H; inversion H;
    expand_transition_seq H0.
Qed.

Local Close Scope string.