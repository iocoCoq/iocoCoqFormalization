Require Import IOCO.
Require Import BE_ltacs.
Require Import String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import LTS.
Require Import LTS_functions.
Require Import IOTS.

Local Open Scope string.
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
    + subst. explore_transition H3.
Defined.

Definition fig4_k3_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    fig4_k3_SC_LTS
    ["but"]
    ["liq";"choc"].
Defined.

Definition fig4_k3 : s_IOLTS :=
  create_s_IOLTS fig4_k3_IOLTS.

Definition fig6_r_LTS : LTS.
Proof.
  solve_LTS_rules
          [0;1;2;3;4;5]
          ["but";"liq";"choc"]
          [(0, event "but",1);(1, event "liq",3);
            (0, event "but",2);(2, event "but",4);(4, event "choc",5)]
          0.
Defined.

Definition fig6_r_SC_LTS : SC_LTS.
Proof.
  apply (mkSC_LTS fig6_r_LTS).
  unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'.
    + subst. proof_absurd_transition H5.
    + subst. explore_transition H3.
Defined.

Definition fig6_r_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    fig6_r_SC_LTS
    ["but"]
    ["liq";"choc"].
Defined.

Definition fig6_r : s_IOLTS :=
  create_s_IOLTS fig6_r_IOLTS.

Definition imp_i1_LTS : LTS.
Proof.
  solve_LTS_rules
          [1;2;3]
          ["a"; "b"; "x"]
          [(1, event "b",1);(1, event "a",2);(2, event "a",2);
            (2, event "b",2);(2, event "x",3);(3, event "a",3);(3, event "b",3)]
          1.
Defined.

Definition imp_i1_SC_LTS : SC_LTS.
Proof.
  apply (mkSC_LTS imp_i1_LTS).
  unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'.
    + subst. proof_absurd_transition H5.
    + subst. explore_transition H3.
Defined.

Definition imp_i1_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    imp_i1_SC_LTS
    ["a";"b"]
    ["x"].
Defined.

Definition imp_i1 : IOTS.
Proof.
  apply (mkIOTS imp_i1_IOLTS).
  unfold valid_iots. exists [1;2;3]. split.
  - apply der_LTS_r1. apply der_r1. simpl. exists []. split.
    + apply seq_reachability_r1. apply empty_reachability_r1.
    + exists ["a"]. split.
      * apply seq_reachability_r2 with (si := 2).
        -- apply one_step_reachability_r1 with (s1 := 1) (s2 := 2);
           try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
        -- apply seq_reachability_r1. apply empty_reachability_r1.
      * exists ["a"; "x"]. split.
        -- apply seq_reachability_r2 with (si := 2).
           ++ apply one_step_reachability_r1 with (s1 := 1) (s2 := 2);
              try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
           ++ apply seq_reachability_r2 with (si := 3).
              ** apply one_step_reachability_r1 with (s1 := 2) (s2 := 3);
                 try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
              ** apply seq_reachability_r1. apply empty_reachability_r1.
        -- apply I.
  - simpl. repeat split.
    + eapply has_reachability_to_some_other_r1. eapply seq_reachability_r2.
      * apply one_step_reachability_r1 with (s1 := 1) (s2 := 2);
        try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
      * apply seq_reachability_r1. apply empty_reachability_r1.
    + eapply has_reachability_to_some_other_r1. eapply seq_reachability_r2.
      * apply one_step_reachability_r1 with (s1 := 1) (s2 := 1);
        try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
      * apply seq_reachability_r1. apply empty_reachability_r1.
    + eapply has_reachability_to_some_other_r1. eapply seq_reachability_r2.
      * apply one_step_reachability_r1 with (s1 := 2) (s2 := 2);
        try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
      * apply seq_reachability_r1. apply empty_reachability_r1.
    + eapply has_reachability_to_some_other_r1. eapply seq_reachability_r2.
      * apply one_step_reachability_r1 with (s1 := 2) (s2 := 2);
        try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
      * apply seq_reachability_r1. apply empty_reachability_r1.
    + eapply has_reachability_to_some_other_r1. eapply seq_reachability_r2.
      * apply one_step_reachability_r1 with (s1 := 3) (s2 := 3);
        try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
      * apply seq_reachability_r1. apply empty_reachability_r1.
    + eapply has_reachability_to_some_other_r1. eapply seq_reachability_r2.
      * apply one_step_reachability_r1 with (s1 := 3) (s2 := 3);
        try (apply empty_reachability_r1). apply transition_r1. elem_in_list.
      * apply seq_reachability_r1. apply empty_reachability_r1.
Defined.

Definition spec_s1_LTS : LTS.
Proof.
  solve_LTS_rules
    [1;2;3]
    ["a";"x"]
    [(1, event "a", 2);(2, event "x", 3)]
    1.
Defined.

Definition spec_s1_SC_LTS : SC_LTS.
Proof.
 apply (mkSC_LTS spec_s1_LTS).
 unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'.
    + subst. proof_absurd_transition H5.
    + subst. explore_transition H3.
Defined.

Definition spec_s1_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    spec_s1_SC_LTS
    ["a"]
    ["x"].
Defined.

(*

Theorem i1_ioco_s1 : ind_ioco imp_i1 spec_s1_IOLTS.
Proof.
  unfold ind_ioco. simpl. intros Qi Qs t out_i out_s H.
  unfold ind_s_traces_LTS in H. unfold ind_s_traces in H. destruct H as [s' H].
  simpl in H. inversion H; subst.
  - clear. intros H1 H2. unfold ind_s_after_LTS in H2. simpl in H2. unfold ind_s_after in H2.
    intros H3 H4. unfold ind_out in H4. intros l H'.
    assert (H'': forall s, In s Qs -> In l out_s).
    { intros s H. remember H as H_new. clear HeqH_new. apply H2 in H.
      inversion H. subst. inversion H0.
      - subst. simpl in *. specialize (H4 l). destruct H4 as [_ H4].
        apply H4 in H_new. destruct H_new as [so' [H_new1 H_new2]].
        inversion H_new1; subst.
        +
    
    }
    apply H''.





  unfold ind_ioco. simpl. intros Qi Qs t out_i out_s H1 H2 H3 H4 H5.
  unfold incl. intros l. intros H6. destruct l.
  - admit.
  - unfold ind_out in H4. specialize (H4 delta).
    destruct H4 as [H4 _]. apply H4 in H6. clear H4. destruct H6 as [s [so' H6]].
    destruct H6 as [H6_1 [H6_2 H6_3]]. inversion H6_2; subst.
    + unfold ind_out in H5. specialize (H5 delta). destruct H5 as [_ H5].
      unfold ind_s_after_LTS in H3. unfold ind_s_after in H3. simpl in H3.
  unfold ind_out in H4. specialize (H4 l).
  destruct H4 as [H4 _]. apply H4 in H6. clear H4. destruct H6 as [s [so' H6]].
  destruct H6 as [H6_1 [H6_2 H6_3]]. inversion H6_2; subst.
  - admit.
  - simpl in H4. unfold ind_out in H5. specialize (H5 l). destruct H5 as [_ H5].
    unfold ind_s_after_LTS in H3. unfold ind_s_after in H3. simpl in H3.
  
  
  
  
  unfold ind_s_traces_LTS in H1.
  unfold ind_s_traces in H1. destruct H1 as [s' H1].
  simpl in H1. inversion H1; subst.
  - unfold ind_s_after_LTS in H2. unfold ind_s_after in H2. simpl in H2.
    unfold ind_s_after_LTS in H3. unfold ind_s_after in H3. simpl in H3.
    unfold ind_out in H4. apply H4 in H6. destruct H6 as [s [so' H6]].
    destruct H6 as [ [H6_1 [H6_2 H6_3]] _]. clear H4. inversion H6_2. 
    + subst. simpl in H0.
  unfold ind_s_after_LTS in H2. unfold ind_s_after in H2. specialize (H2 x).
   unfold ind_s_after_LTS in H3. unfold ind_s_after in H3. specialize (H3 x).
   apply H3 in H1. unfold ind_out in H5. specialize (H5 a). 
   -
*)
Definition spec_s3_LTS : LTS.
Proof.
  solve_LTS_rules
    [1;2;3;4;5]
    ["a";"b";"x";"y"]
    [(1, event "a", 2);(2, event "x", 3);(1, event "b", 4);(4, event "y", 5)]
    1.
Defined.

Definition spec_s3_SC_LTS : SC_LTS.
Proof.
 apply (mkSC_LTS spec_s3_LTS).
 unfold strongly_converging. intros s t H. destruct t.
  - destruct H. unfold not in H. exfalso. apply H. reflexivity.
  - unfold all_labels_tau in H. destruct H as [_ [H _]].
    unfold not. intros H'. inversion H'.
    + subst. proof_absurd_transition H5.
    + subst. explore_transition H3.
Defined.

Definition spec_s3_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    spec_s3_SC_LTS
    ["a";"b"]
    ["x";"y"].
Defined.

Local Close Scope string.
