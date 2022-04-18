Require Import IOCO.
Require Import IOTS.
Require Import LTS.
Require Import list_helper.
Require Import BE_ltacs.
Require Import LTS_ex.
Require Export IOTS_ex.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import String.

Local Open Scope string.
(* Exemplo 8 *)
Example test_fout_1 :
  f_out (f_after_IOLTS [] fig4_k3) fig4_k3 = [delta].
Proof.
  reflexivity.
Qed.

Example test_fout_2 :
  f_out (f_after_IOLTS [delta] fig4_k3) fig4_k3 = [delta].
Proof.
  reflexivity.
Qed.

Example test_fout_3 :
  f_out (f_after_IOLTS [s_event "liq"] fig4_k3) fig4_k3 = [].
Proof.
  reflexivity.
Qed.

Example test_fout_4 :
  f_out (f_after_IOLTS [s_event "but"] fig4_k3) fig4_k3 = [s_event "liq"; delta].
Proof.
  reflexivity.
Qed.

Example test_fout_5 :
  f_out (
    f_after_IOLTS [s_event "but"; s_event "but"]
    fig4_k3
  ) fig4_k3 = [s_event "choc"; s_event "liq"].
Proof.
  reflexivity.
Qed.

Example test_fout_6 :
  f_out (
    f_after_IOLTS [s_event "but"; delta; s_event "but"]
    fig4_k3
  ) fig4_k3 = [s_event "choc"].
Proof.
  reflexivity.
Qed.

Example test_fout_7 :
  f_out (
    f_after_IOLTS [s_event "but"; s_event "but"; s_event "liq"]
    fig4_k3
  ) fig4_k3 = [delta].
Proof.
  reflexivity.
Qed.

Example test_fout_8 :
  f_out (
    f_after_IOLTS [s_event "but"; delta; s_event "but"; s_event "liq"]
    fig4_k3
  ) fig4_k3 = [].
Proof.
  reflexivity.
Qed.

Example i1_ioco_s1 : ind_ioco imp_i1 spec_s1_IOLTS.
Proof.
  unfold ind_ioco. intros Qi Qs t out_i out_s H H1 H2 H3 H4 x H5.
  unfold ind_s_traces_LTS in H. unfold ind_s_traces in H.
  simpl in H. destruct H as [s H].
  unfold ind_out in H3. destruct H3 as [H3 _].
  unfold ind_out in H4. destruct H4 as [_ H4].
  apply H3 in H5. destruct H5 as [s' [so' [H5_1 [H5_2 H5_3]]]].
  unfold ind_s_after_IOLTS in H1. simpl in H1. unfold ind_s_after in H1.
  apply H1 in H5_1.
  unfold ind_s_after_IOLTS in H2. simpl in H2. unfold ind_s_after in H2.
  remember H as H'. clear HeqH'. apply H2 in H'. apply H4 in H'.
  destruct H' as [so'' [H' H'_2]]. apply H'_2.
  clear H1 H2 H3 H4 H'_2 Qi Qs out_i out_s.
  induction t as [| a t' IHt']; [| destruct a].
  - (* t = [] *)
    expand_s_seq_reachability H5_1. expand_out_one_state H5_2 x H5_3.
    expand_s_seq_reachability H. inversion H'; [elem_in_list |].
    destruct H1. elem_in_list.
  - (* t = s_event "a" :: t' => destruct t' *)
    clear IHt'. destruct t' as [| a t'']; [| destruct a].
    + (* t = [ s_event "a" ] *)
      expand_s_seq_reachability H.
      expand_s_seq_reachability H5_1. expand_out_one_state H5_2 x H5_3.
      clear H_so H5_1 H5_2 H0 H1 H4. inversion H'; [expand_In H0 |].
      apply H2. exists 3. split; try apply transition_r1; elem_in_list.
    + (* t = s_event "a" :: s_event "x" :: t'' => induction t'' *)
      induction t'' as [| a t''' IHt''']; [| destruct a].
      * (* t = [ s_event "a"; s_event "x" ] *)
        expand_s_seq_reachability H.
        expand_s_seq_reachability H5_1; expand_out_one_state H5_2 x H5_3.
        clear H0 H1 H2 H3 H4. inversion H'; [elem_in_list |].
        destruct H0. elem_in_list.
      * (* t = s_event _ :: s_event _ :: s_event _ :: t'' => contradiction *)
        expand_s_seq_reachability H.
      * (* t = s_event "a" :: s_event "x" :: delta :: t''' => use IHt''' *)
        apply IHt'''.
        -- inversion H. subst. expand_one_step_reachability H3.
           apply s_seq_reachability_r2 with (si := 2); auto.
           inversion H6. subst. expand_one_step_reachability H5.
           apply s_seq_reachability_r2 with (si := 3); auto.
           inversion H9. subst. apply H8.
        -- inversion H5_1. subst. expand_one_step_reachability H3;
           eapply s_seq_reachability_r2; try (apply H3);
           inversion H6; subst; expand_one_step_reachability H5;
           eapply s_seq_reachability_r2; try (apply H5); inversion H9; auto.
    + (* t = s_event "a" :: delta :: t'' => contradiction *)
      expand_s_seq_reachability H.
  - (* t = delta :: t' => use IHt' *)
    inversion H5_1. subst. inversion H. subst. apply IHt'; auto.
Qed.

Example i1_not_ioco_s3 : ~ (ind_ioco imp_i1 spec_s3_IOLTS).
Proof.
  unfold ind_ioco. unfold not. intros H. simpl in H.
  specialize (H [1] [4] [s_event "b"] [delta] [s_event "y"] ).
  assert ( H': ~ incl [delta] [s_event "y"]).
  { unfold incl. intros H''. specialize (H'' delta). destruct H'';
    try inversion H0. left. reflexivity.
  }
  apply H'. apply H.
  - unfold ind_s_traces_LTS. unfold ind_s_traces. exists 4. simpl.
    apply s_seq_reachability_r2 with (si := 4).
    + apply one_step_reachability_r1 with (s1 := 1) (s2 := 4);
      try apply empty_reachability_r1.
      apply transition_r1. elem_in_list.
    + apply s_seq_reachability_r1. apply empty_reachability_r1.
  - unfold ind_s_after_IOLTS. unfold ind_s_after. intros a. split.
    + simpl. intros H''. inversion H''; subst. simpl in *. inversion H3; subst.
      inversion H0; subst.
      * inversion H1; subst. expand_In H7. subst. inversion H2; subst.
        -- inversion H6; subst. simpl in H4. inversion H4; subst.
           ++ left. reflexivity.
           ++ inversion H5; subst. expand_In H9.
        -- inversion H4; subst. expand_In H8.
      * inversion H4; subst. expand_In H7.
    + intros H''. expand_In H''. simpl. apply s_seq_reachability_r2 with (si := 1).
      * apply one_step_reachability_r1 with (s1 := 1) (s2 := 1);
        try apply empty_reachability_r1.
        apply transition_r1. elem_in_list.
      * apply s_seq_reachability_r1. apply empty_reachability_r1.
  - unfold ind_s_after_IOLTS. unfold ind_s_after. intros a. split.
    + simpl. intros H''. inversion H''; subst. simpl in *. inversion H3; subst.
      inversion H0; subst.
      * inversion H1; subst. expand_In H7. subst. inversion H2; subst.
        -- inversion H6; subst. simpl in H4. inversion H4; subst.
           ++ left. reflexivity.
           ++ inversion H5; subst. expand_In H9.
        -- inversion H4; subst. expand_In H8.
      * inversion H4; subst. expand_In H7.
    + intros H''. expand_In H''. simpl. apply s_seq_reachability_r2 with (si := 4).
      * apply one_step_reachability_r1 with (s1 := 1) (s2 := 4);
        try apply empty_reachability_r1.
        apply transition_r1. elem_in_list.
      * apply s_seq_reachability_r1. apply empty_reachability_r1.
  - unfold ind_out. split.
    + intros l H''. expand_In H''. exists 1. exists [delta].
      repeat split; try(apply out_one_state_r1); elem_in_list.
    + intros s H''. expand_In H''. exists [delta]. split.
      * try(apply out_one_state_r1); elem_in_list.
      * intros o H'''. expand_In H'''. elem_in_list.
  - unfold ind_out. split.
    + intros l H''. expand_In H''. exists 4. exists [s_event "y"].
      repeat split; try elem_in_list. apply out_one_state_r2.
      * intros H'''; expand_In H'''.
      * intros H'''; expand_In H'''.
      * intros l'. split.
        -- intros H'''. expand_In H'''. exists 5. split; try (elem_in_list).
           apply transition_r1. elem_in_list.
        -- intros H'''. destruct H''' as [ s' [ H'''_1 H'''_2]].
           inversion H'''_2; subst.
           expand_In H'''_1; subst; expand_In H3. elem_in_list.
    + intros s H''. expand_In H''. exists [s_event "y"]. split.
      * apply out_one_state_r2.
        -- intros H'''; expand_In H'''.
        -- intros H'''; expand_In H'''.
        -- intros l'. split.
           ++ intros H'''. expand_In H'''. exists 5. split; try (elem_in_list).
              apply transition_r1. elem_in_list.
           ++ intros H'''. destruct H''' as [ s' [ H'''_1 H'''_2]].
              inversion H'''_2; subst. expand_In H'''_1; subst; expand_In H3.
              elem_in_list.
      * intros l' H'''. expand_In H'''. elem_in_list.
Qed.