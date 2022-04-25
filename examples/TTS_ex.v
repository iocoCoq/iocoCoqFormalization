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


Ltac try_all list f :=
  lazymatch list with
  | [ ] => idtac
  | ?h :: ?t => f h + try_all t f
  end.

Ltac create_TTS iots pass_state fail_state theta imp_Li :=
  apply (mkTTS iots pass_state fail_state theta); try elem_in_list; auto;
  try (intros l s H; expand_transition H; subst; simpl; split; auto);
  [
    unfold ind_deterministic; intros t ls H; inversion H as [? ? H_aux]; subst;
    clear H; rename H_aux into H;
    inversion H as [? ? ? H_aux]; subst; clear H; rename H_aux into H;
    simpl in H; inversion H as [? ? ? ? H_aux]; subst; clear H; rename H_aux into H;
    intros H' H''; inversion H' as [? ? ? H_aux]; subst; simpl in H_aux;
    clear H'; rename H_aux into H';
    apply ind_after_reflect in H';  unfold f_after in H';
    symmetry_eqv in H';
    repeat (induction t as [| ? t IHt]; expand_seq_reachability H; auto;
      simpl f_after' in H';
      try (apply Equiv_eqLength in H'; auto; apply NoDup_cons; auto;
           apply NoDup_nil); clear IHt)
  |
    intros t; destruct t; intros s H H'; [destruct H; reflexivity |];
    simpl in H';
      assert (H_fail:
        forall s t,
          ind_seq_reachability fail_state t s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = fail_state);
      [ intros s' t' H''; induction t'; expand_seq_reachability H''; auto |];
      assert (H_pass:
        forall s t,
          ind_seq_reachability pass_state t s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = pass_state);
      [ intros s' t' H''; induction t'; expand_seq_reachability H''; auto |];
      expand_seq_reachability H'; auto;
      repeat (destruct t as [| ? t];
        try (
         inversion H' as [ ? ? ? H_empty |];
         inversion H_empty as [ | ? ? ? ? H_trans ?];
         subst; expand_transition H_trans; fail);
        expand_seq_reachability H';
        try (apply H_pass in H'; inversion H');
        try (apply H_fail in H'; inversion H'))
  |
    intros q H; simpl; expand_In H; vm_compute f_init;
    try (left; proof_Equiv); right;
    try_all (imp_Li) ltac:(fun x => (exists x; split; auto; proof_Equiv)) ].


Definition fig7_t1_TTS : TTS.
Proof.
  create_TTS fig7_t1_IOTS 0 4 "theta" ["but"].
Defined.

Ltac expand_test_execution_transition H :=
  let H_trans := fresh "H_trans" in
  let H_trans' := fresh "H_trans'" in
  let H_In := fresh "H_In" in
  let H_eq := fresh "H_eq" in
    lazymatch type of H with
    | ind_test_execution_transition _ _ tau _ _ _ _ =>
        inversion H as [? ? ? ? ? H_trans | |]; subst; expand_transition H_trans
    | ind_test_execution_transition _ _ (event _) _ _ _ _ =>
        inversion H as [|
          ? ? ? ? ? ? ? H_In H_trans H_trans' |
          ? ? ? ? ? ? H_eq H_trans H_In];
        subst; try (inversion H_eq); subst; expand_In H_In; subst;
        expand_transition H_trans; try (expand_transition H_trans')
    end.

Ltac expand_test_execution_empty_reachability H :=
  let H_tau := fresh "H_tau" in
  let H_empty := fresh "H_empty" in
    inversion H as [ | ? ? ? ? ? ? ? ? H_tau H_empty]; subst;
    try (expand_test_execution_transition H_tau; subst;
         expand_test_execution_empty_reachability H_empty; subst).

Ltac expand_test_execution_one_step_reachability H :=
  let H_empty := fresh "H_empty" in
  let H_trans := fresh "H_trans" in
    inversion H as [? ? ? ? ? ? ? ? ? H_empty H_trans]; subst;
    expand_test_execution_empty_reachability H_empty;
    expand_test_execution_transition H_trans;
    clear H_empty H_trans.
 
Ltac expand_test_execution_seq_reachability H :=
  let H_empty := fresh "H_empty" in
  let H_one_step := fresh "H_one_step" in
  let H_seq := fresh "H_seq" in
    lazymatch type of H with
    | ind_test_execution_seq_reachability _ _ [ ] _ _ _ _ =>
        inversion H as [ ? ? ? ? ? ? H_empty |]; subst;
        expand_test_execution_empty_reachability H_empty; subst; clear H_empty
    | ind_test_execution_seq_reachability _ _ (_ :: _) _ _ _ _ =>
        inversion H as [| ? ? ? ? ? ? ? ? ? ? H_one_step H_seq]; subst;
        expand_test_execution_one_step_reachability H_one_step; subst;
        expand_test_execution_seq_reachability H_seq; subst; clear H H_one_step;
        rename H_seq into H
    | ind_test_execution_seq_reachability _ _ _ _ _ _ _ => idtac
    | _ => fail "Invalid Hypothesis format"
    end.

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