Require Import IOCO.
Require Import ltacs.
Require Import String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.
Require Import LTS.
Require Import LTS_functions.
Require Import IOTS.

Local Open Scope string.

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

Definition fig4_k1_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    fig4_k1_SC_LTS
    ["but"]
    ["liq";"choc"].
Defined.

Definition fig4_k1_IOTS : IOTS.
Proof.
  apply (mkIOTS fig4_k1_IOLTS).
  unfold valid_iots. exists [0;1;2]. split.
  - apply der_LTS_r1. apply der_r1. intros s'. simpl q0. split.
    + intros H. destruct H as [ll H].
      repeat (induction ll; expand_seq_reachability H; try elem_in_list; auto;
      clear IHll).
    + intros H. expand_In H.
      * exists [ ]. proof_seq_reachability (@nil nat) (@nil nat).
      * exists ["but"]. proof_seq_reachability [(@nil nat, 1)] (@nil nat).
      * exists ["but"; "liq"].
        proof_seq_reachability [(@nil nat, 1); (@nil nat, 2)] (@nil nat).
  - simpl. repeat split; eapply has_reachability_to_some_other_r1.
   + proof_seq_reachability [(@nil nat, 1)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 1)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 2)] (@nil nat).
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

Definition fig4_k3_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    fig4_k3_SC_LTS
    ["but"]
    ["liq";"choc"].
Defined.

Definition fig4_k3_IOTS : IOTS.
Proof.
  apply (mkIOTS fig4_k3_IOLTS).
  unfold valid_iots. exists [0;1;2;3;4;5]. split.
  - apply der_LTS_r1. apply der_r1. intros s'. simpl q0. split.
    + intros H. destruct H as [ll H].
      repeat(
        induction ll; expand_seq_reachability H; try elem_in_list; auto;
        clear IHll).
    + intros H. expand_In H.
      * exists [ ]. proof_seq_reachability (@nil nat) (@nil nat).
      * exists ["but"]. proof_seq_reachability [(@nil nat, 1)] (@nil nat).
      * exists ["but"]. proof_seq_reachability [(@nil nat, 2)] (@nil nat).
      * exists ["but"; "liq"].
        proof_seq_reachability [(@nil nat, 1); (@nil nat, 3)] (@nil nat).
      * exists ["but"; "but"].
        proof_seq_reachability [(@nil nat, 2); (@nil nat, 4)] (@nil nat).
      * exists ["but"; "but"; "choc"].
        proof_seq_reachability [(@nil nat, 2); (@nil nat, 4); (@nil nat, 5)] (@nil nat).
  - simpl. repeat split; eapply has_reachability_to_some_other_r1.
   + proof_seq_reachability [(@nil nat, 1)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 1)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 4)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 3)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 4)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 5)] (@nil nat).
Defined.

Definition fig4_k3 : s_IOLTS :=
  create_s_IOLTS fig4_k3_IOLTS.

Definition fig6_r_BE :=
  "fig6_r" ::= "but";; "liq";; STOP [] "but";; "but";; "choc";; STOP.

Definition fig6_r_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [fig6_r_BE]. Defined.

Definition fig6_r_LTS : LTS.
Proof. create_LTS_from_BE fig6_r_ctx "fig6_r" 100. Defined.

Definition fig6_r_LTS' : LTS.
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
    + subst. expand_transition H3.
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

Definition i1 :=
  "i1" ::= "b";; "i1" [] "a";; "i1_aux1".
Definition i1_aux1 :=
  "i1_aux1" ::= "a";; "i1_aux1" [] "b";; "i1_aux1"[] "x";; "i1_aux2".
Definition i1_aux2 :=
  "i1_aux2" ::= "a";; "i1_aux2" [] "b";; "i1_aux2".

Definition i1_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [i1; i1_aux1; i1_aux2]. Defined.

Definition imp_i1_LTS : LTS.
Proof. create_LTS_from_BE i1_ctx "i1" 100. Defined.

Definition imp_i1_LTS' : LTS.
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
  - destruct H as [H _]. unfold not in H. exfalso. apply H. reflexivity.
  - destruct H as [_ H]. unfold not. intros H'. simpl in H.
    destruct H as [Eq H]. subst. inversion H'; subst.
    + expand_transition H5; subst; inversion H0.
    + expand_transition H3; subst; simpl in H; destruct H as [Eq H]; subst;
      inversion H6 as [? ? ? ? H_Trans | ? ? ? ? ? ? ? H_Trans ?];
      expand_transition H_Trans.
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
  unfold valid_iots. exists [0;1;2;3;4;5]. split.
  - apply der_LTS_r1. apply der_r1. intros s'. split.
    + intros H. destruct H as [ll H]. vm_compute q0 in H.
      assert(H4 : forall ll,
        ind_seq_reachability 4 ll s' (lts (sc_lts imp_i1_IOLTS)) ->
        s' = 4 \/ ind_seq_reachability 5 ll s' (lts (sc_lts imp_i1_IOLTS))).
      { intros ll' H'. destruct ll'; expand_seq_reachability H'; auto; right.
        - apply seq_reachability_r1; auto.
        - apply seq_reachability_r2 with (si := 4); auto.
          eapply one_step_reachability_r1; try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
        - apply seq_reachability_r2 with (si := 5); auto.
          eapply one_step_reachability_r1 with (s2 := 4);
          try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
          apply empty_reachability_r2 with (si := 5); auto.
        - apply seq_reachability_r2 with (si := 4); auto.
          eapply one_step_reachability_r1; try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
        - apply seq_reachability_r2 with (si := 5); auto.
          eapply one_step_reachability_r1 with (s2 := 4);
          try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
          apply empty_reachability_r2 with (si := 5); auto. }
      assert (H5 : forall ll,
        ind_seq_reachability 5 ll s' (lts (sc_lts imp_i1_IOLTS)) ->
        In s' [0; 1; 2; 3; 4; 5]).
      { intros ll' H'. induction ll'; expand_seq_reachability H';
        try elem_in_list; auto; apply H4 in H'; destruct H'; auto;
        subst; elem_in_list. }
      assert(H2: forall ll,
        ind_seq_reachability 2 ll s' (lts (sc_lts imp_i1_IOLTS)) -> 
        s' = 2 \/ ind_seq_reachability 3 ll s' (lts (sc_lts imp_i1_IOLTS))).
      { intros ll' H'. destruct ll'; expand_seq_reachability H'; auto; right.
        - apply seq_reachability_r1; auto.
        - apply seq_reachability_r2 with (si := 4); auto.
          eapply one_step_reachability_r1; try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
        - apply seq_reachability_r2 with (si := 5); auto.
          eapply one_step_reachability_r1 with (s2 := 4);
          try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
          apply empty_reachability_r2 with (si := 5); auto.
        - apply seq_reachability_r2 with (si := 2); auto.
          eapply one_step_reachability_r1; try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
        - apply seq_reachability_r2 with (si := 3); auto.
          eapply one_step_reachability_r1 with (s2 := 2);
          try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
          apply empty_reachability_r2 with (si := 3); auto.
        - apply seq_reachability_r2 with (si := 2); auto.
          eapply one_step_reachability_r1; try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
        - apply seq_reachability_r2 with (si := 3); auto.
          eapply one_step_reachability_r1 with (s2 := 2);
          try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
          apply empty_reachability_r2 with (si := 3); auto. }
     assert (H3 : forall ll,
       ind_seq_reachability 3 ll s' (lts (sc_lts imp_i1_IOLTS)) ->
       In s' [0; 1; 2; 3; 4; 5]).
     { intros ll' H'. induction ll'; expand_seq_reachability H';
        try elem_in_list; auto.
        - apply H4 in H'. destruct H' as [H' | H']; subst;
          try elem_in_list. apply H5 in H'. apply H'.
        - apply H5 in H'. apply H'.
        - apply H2 in H'. destruct H' as [H' | H']; subst;
          try elem_in_list. auto.
        - apply H2 in H'. destruct H' as [H' | H']; subst;
          try elem_in_list. auto. }
     assert(H0: forall ll,
        ind_seq_reachability 0 ll s' (lts (sc_lts imp_i1_IOLTS)) -> 
        s' = 0 \/ ind_seq_reachability 1 ll s' (lts (sc_lts imp_i1_IOLTS))).
      { intros ll' H'. destruct ll'; expand_seq_reachability H'; auto; right.
        - apply seq_reachability_r1; auto.
        - apply seq_reachability_r2 with (si := 2); auto.
          eapply one_step_reachability_r1; try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
        - apply seq_reachability_r2 with (si := 3); auto.
          eapply one_step_reachability_r1 with (s2 := 2);
          try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
          apply empty_reachability_r2 with (si := 3); auto.
        - apply seq_reachability_r2 with (si := 0); auto.
          eapply one_step_reachability_r1; try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
        - apply seq_reachability_r2 with (si := 1); auto.
          eapply one_step_reachability_r1 with (s2 := 0);
          try apply empty_reachability_r1.
          apply transition_r1. vm_compute T. elem_in_list.
          apply empty_reachability_r2 with (si := 1); auto. }
      induction ll; expand_seq_reachability H; try elem_in_list; auto.
      * apply H2 in H. destruct H as [H | H]; subst; try elem_in_list.
        apply H3 in H. apply H.
      * apply H3 in H. apply H.
      * apply H0 in H. destruct H as [H | H]; subst; try elem_in_list.
        auto.
    + intros H. expand_In H.
      * exists ["b"]. proof_seq_reachability [(@nil nat, 0)] (@nil nat).
      * exists [ ]. proof_seq_reachability (@nil nat) (@nil nat).
      * exists ["a"]. proof_seq_reachability [(@nil nat, 2)] (@nil nat).
      * exists ["a"]. proof_seq_reachability [(@nil nat, 2)] [3].
      * exists ["a"; "x"]. proof_seq_reachability [(@nil nat, 2); ([3], 4)] (@nil nat).
      * exists ["a"; "x"]. proof_seq_reachability [(@nil nat, 2); ([3], 4)] [5].
 - vm_compute L_i. simpl. repeat split; eapply has_reachability_to_some_other_r1.
   + proof_seq_reachability [([1], 2)] (@nil nat).
   + proof_seq_reachability [([1], 0)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 2)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 0)] (@nil nat).
   + proof_seq_reachability [([3], 2)] (@nil nat).
   + proof_seq_reachability [([3], 2)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 2)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 2)] (@nil nat).
   + proof_seq_reachability [([5], 4)] (@nil nat).
   + proof_seq_reachability [([5], 4)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 4)] (@nil nat).
   + proof_seq_reachability [(@nil nat, 4)] (@nil nat).
Defined.

Definition spec_s1_LTS' : LTS.
Proof.
  solve_LTS_rules
    [1;2;3]
    ["a";"x"]
    [(1, event "a", 2);(2, event "x", 3)]
    1.
Defined.

Definition s1 :=
  "s1" ::= "a";; "x";; STOP.

Definition s1_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [s1]. Defined.

Definition spec_s1_LTS : LTS.
Proof. create_LTS_from_BE s1_ctx "s1" 100. Defined.

Definition spec_s1_SC_LTS : SC_LTS.
Proof.
  apply (mkSC_LTS spec_s1_LTS).
  unfold strongly_converging. intros s t H. destruct t.
  - destruct H as [H _]. unfold not in H. exfalso. apply H. reflexivity.
  - destruct H as [_ H]. unfold not. intros H'. simpl in H.
    destruct H as [Eq H]. subst. inversion H'; subst.
    + expand_transition H5; subst; inversion H0.
    + expand_transition H3; subst; simpl in H; destruct H as [Eq H]; subst;
      inversion H6 as [? ? ? ? H_Trans | ? ? ? ? ? ? ? H_Trans ?];
      expand_transition H_Trans.
Defined.

Definition spec_s1_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    spec_s1_SC_LTS
    ["a"]
    ["x"].
Defined.

Definition s3 :=
  "s3" ::= "a";; "x";; STOP [] "b";; "y";; STOP.

Definition s3_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [s3]. Defined.

Definition spec_s3_LTS : LTS.
Proof. create_LTS_from_BE s3_ctx "s3" 100. Defined.

Definition spec_s3_LTS' : LTS.
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
    + subst. expand_transition H3.
Defined.

Definition spec_s3_IOLTS : IOLTS.
Proof.
  solve_IOLTS_rules
    spec_s3_SC_LTS
    ["a";"b"]
    ["x";"y"].
Defined.

Local Close Scope string.
