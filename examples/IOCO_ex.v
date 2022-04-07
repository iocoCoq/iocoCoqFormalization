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
Proof. Admitted.

(*
  unfold ind_ioco. intros Qi Qs t out_i out_s H H1 H2 H3 H4.
  apply ind_out_equiv_f_out in H3. simpl in H3.
  apply ind_out_equiv_f_out in H4. simpl in H4.
  unfold incl. intros l H5. apply H3 in H5. apply H4.
  clear H1.
  assert (H1 : Qi [=] (f_after_IOLTS t (create_s_IOLTS (embedded_iolts imp_i1)))).
  { admit. }
  clear H2.
  assert (H2 : Qs [=] (f_after_IOLTS t (create_s_IOLTS spec_s1_IOLTS))).
  { admit. }
  clear H3 H4.
  induction H. simpl in H. induction t.
  - simpl in H. unfold f_after_IOLTS in H2. unfold f_after_single_state_IOLTS in H2.
    simpl in H2. unfold LTS_functions.all_reachable_by_tau in H2. simpl in H2.  admit.
  - 
  unfold incl. intros l' H'.
  unfold ind_out in H3. specialize (H3 l'). destruct H3 as [H3_1 H3_2].
  unfold ind_out in H4. specialize (H4 l'). destruct H4 as [H4_1 H4_2].
  apply H3_1 in H'. destruct H' as [s'' [so [H'_1 [H'_2 H'_3]]]].
  inversion H'_2; subst.
  + expand_In H'_3; subst. expand_In H3; subst.
    * unfold ind_s_after_LTS in H1. unfold ind_s_after in H1. simpl in *.
      unfold ind_s_after_LTS in H2. unfold ind_s_after in H2. simpl in H2.
      apply H1 in H'_1. inversion H'_1; subst.
      * simpl in H0. unfold ind_s_traces_LTS in H.
        unfold ind_s_traces in H. destruct H as [s'' H]. simpl in H. inversion H; subst.
        simpl in *. inversion H5; subst.
        -- apply H2 in H. apply H4_2 in H. destruct H as [so' [H_1 H_2]].
           inversion H_1; subst.
           ++ apply H_2. elem_in_list.
           ++ destruct H. elem_in_list.
        -- inversion H6; subst. expand_In H8.
      * simpl in *. inversion H0; subst. inversion H6; subst.
        -- inversion H7; subst. expand_In H11; subst.
    unfold ind_out in H4. specialize (H4 l). destruct H4 as [H4_1 H4_2].
    
  
  
   inversion H0; subst.
    + intros H1 H2 H3 H4. unfold ind_s_after_LTS in H2. unfold ind_s_after in H2.
      simpl in H2. apply H2 in H. 
      apply H4_2 in H. destruct H as [so' [H_1 H_2]]. inversion H_1; subst.
      * apply H_2. apply H3_1 in H''.
    intros H'. unfold ind_s_after_LTS in H'. unfold ind_s_after in H'.
    simpl in *. intros H1 H2 H3.  
    unfold ind_out in H2. specialize (H2 l). destruct H2 as [H2_1 H2_2].
    unfold ind_out in H3. specialize (H3 l). destruct H3 as [H3_1 H3_2].
    apply H2_1 in H''.
    destruct H'' as [s [so' [H''_1 [H''_2 H''_3]]]]. inversion H''_2; subst.
    + expand_In H''_3; subst. unfold ind_s_after_LTS in H1. unfold ind_s_after in H1.
      simpl in *. 
      *
Admitted.
*)

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
    + apply one_step_reachability_r1 with (s1 := 1) (s2 := 4); try apply empty_reachability_r1.
      apply transition_r1. elem_in_list.
    + apply s_seq_reachability_r1. apply empty_reachability_r1.
  - unfold ind_s_after_LTS. unfold ind_s_after. intros a. split.
    + simpl. intros H''. inversion H''; subst. simpl in *. inversion H3; subst.
      inversion H0; subst.
      * inversion H1; subst. expand_In H7. subst. inversion H2; subst.
        -- inversion H6; subst. simpl in H4. inversion H4; subst.
           ++ left. reflexivity.
           ++ inversion H5; subst. expand_In H9.
        -- inversion H4; subst. expand_In H8.
      * inversion H4; subst. expand_In H7.
    + intros H''. expand_In H''. simpl. apply s_seq_reachability_r2 with (si := 1).
      * apply one_step_reachability_r1 with (s1 := 1) (s2 := 1); try apply empty_reachability_r1.
        apply transition_r1. elem_in_list.
      * apply s_seq_reachability_r1. apply empty_reachability_r1.
  - unfold ind_s_after_LTS. unfold ind_s_after. intros a. split.
    + simpl. intros H''. inversion H''; subst. simpl in *. inversion H3; subst.
      inversion H0; subst.
      * inversion H1; subst. expand_In H7. subst. inversion H2; subst.
        -- inversion H6; subst. simpl in H4. inversion H4; subst.
           ++ left. reflexivity.
           ++ inversion H5; subst. expand_In H9.
        -- inversion H4; subst. expand_In H8.
      * inversion H4; subst. expand_In H7.
    + intros H''. expand_In H''. simpl. apply s_seq_reachability_r2 with (si := 4).
      * apply one_step_reachability_r1 with (s1 := 1) (s2 := 4); try apply empty_reachability_r1.
        apply transition_r1. elem_in_list.
      * apply s_seq_reachability_r1. apply empty_reachability_r1.
  - unfold ind_out. intros l. split.
    + intros H''. expand_In H''. exists 1. exists [delta].
      repeat split; try(apply out_one_state_r1); elem_in_list.
    + intros s H''. expand_In H''. exists [delta]. split.
      * try(apply out_one_state_r1); elem_in_list.
      * intros o H'''. expand_In H'''. elem_in_list.
  - unfold ind_out. intros l. split.
    + intros H''. expand_In H''. exists 4. exists [s_event "y"].
      repeat split; try elem_in_list. apply out_one_state_r2.
      * intros H'''; expand_In H'''.
      * intros H'''; expand_In H'''.
      * intros l'. split.
        -- intros H'''. expand_In H'''. exists 5. split; try (elem_in_list).
           apply transition_r1. elem_in_list.
        -- intros H'''. destruct H''' as [ s' [ H'''_1 H'''_2]]. inversion H'''_2; subst.
           expand_In H'''_1; subst; expand_In H3. elem_in_list.
    + intros s H''. expand_In H''. exists [s_event "y"]. split.
      * apply out_one_state_r2.
        -- intros H'''; expand_In H'''.
        -- intros H'''; expand_In H'''.
        -- intros l'. split.
           ++ intros H'''. expand_In H'''. exists 5. split; try (elem_in_list).
           apply transition_r1. elem_in_list.
           ++ intros H'''. destruct H''' as [ s' [ H'''_1 H'''_2]]. inversion H'''_2; subst.
           expand_In H'''_1; subst; expand_In H3. elem_in_list.
      * intros l' H'''. expand_In H'''. elem_in_list.
Qed.