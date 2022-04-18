Require Import LTS.
Require Import IOTS.
Require Import List.
Require Import ListSet.
Require Import String.
Import Coq.Lists.List.ListNotations.
Require Import list_helper.
Require Import LTS_functions.


Section SectionTTS.

  Record TTS : Type := mkTTS {
      iots : IOTS
    ; fail_state : state
    ; pass_state : state
    ; theta : label
    ; fail_is_valid : In fail_state iots.(embedded_iolts).(sc_lts).(lts).(Q)
    ; pass_is_valid : In pass_state iots.(embedded_iolts).(sc_lts).(lts).(Q)
    ; theta_is_valid : In theta iots.(embedded_iolts).(L_u)
    ; TTS_Li := iots.(embedded_iolts).(L_u)
    ; TTS_Lu := set_remove string_dec theta iots.(embedded_iolts).(L_i)
    ; is_deterministic : ind_deterministic iots.(embedded_iolts).(sc_lts).(lts)
    ; pass_fail_diff : pass_state <> fail_state
    ; pass_cycle :
        forall (l : label) (s : state),
          ind_transition pass_state (event l) s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = pass_state /\ (l = theta \/ In l TTS_Lu)
    ; fail_cycle :
        forall (l : label) (s : state),
          ind_transition fail_state (event l) s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = fail_state /\ (l = theta \/ In l TTS_Lu)
    ; no_other_cycles :
        forall (t : list label) (s : state),
          t <> [] ->
          ind_seq_reachability s t s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = fail_state \/ s = pass_state
    ; valid_out_label :
        forall (q : state),
          In q iots.(embedded_iolts).(sc_lts).(lts).(Q) ->
          f_init q iots.(embedded_iolts).(sc_lts).(lts) [=]
            map event (theta :: TTS_Lu) \/
          exists (a : label),
            In a TTS_Li /\
            f_init q iots.(embedded_iolts).(sc_lts).(lts) [=]
                 map event (a :: TTS_Lu)
  }.

End SectionTTS.

(* Definition 16.1 *)
Inductive ind_test_execution_transition :
    state -> state -> transition_label -> state -> state -> TTS -> IOTS -> Prop :=
  | test_execution_transition_r1 (t i i' : state) (test : TTS) (imp : IOTS) :
      ind_transition i tau i' imp.(embedded_iolts).(sc_lts).(lts) ->
      ind_test_execution_transition t i tau t i' test imp
  | test_execution_transition_r2 (t i t' i' : state) (a : label) (test : TTS)
        (imp : IOTS) :
      In a (test.(TTS_Li) ++ test.(TTS_Lu)) ->
      ind_transition t (event a) t' test.(iots).(embedded_iolts).(sc_lts).(lts) ->
      ind_transition i (event a) i' imp.(embedded_iolts).(sc_lts).(lts) ->
      ind_test_execution_transition t i (event a) t' i' test imp
  | test_execution_transition_r3 (t i t' : state) (a : label) (test : TTS)
        (imp : IOTS) :
      ind_transition
        t
        (event test.(theta))
        t'
        test.(iots).(embedded_iolts).(sc_lts).(lts) ->
      In i (create_s_IOLTS imp.(embedded_iolts)).(Ts) ->
      ind_test_execution_transition t i (event test.(theta)) t' i test imp.

(* Definition 16.2 *)
Inductive ind_test_execution_empty_reachability :
    state -> state -> state -> state -> TTS -> IOTS -> Prop :=
  | test_execution_empty_reachability_r1 (t i : state) (test: TTS) (imp : IOTS) :
      ind_test_execution_empty_reachability t i t i test imp
  | test_execution_empty_reachability_r2 (t1 t2 t3 i1 i2 i3 : state) (test : TTS)
        (imp : IOTS) :
      ind_test_execution_transition t1 i1 tau t2 i2 test imp ->
      ind_test_execution_empty_reachability t2 i2 t3 i3 test imp ->
      ind_test_execution_empty_reachability t1 i1 t3 i3 test imp.

Inductive ind_test_execution_one_step_reachability :
    state -> state -> label -> state -> state -> TTS -> IOTS -> Prop :=
  | test_execution_one_step_reachability_r1 (t1 t2 t3 i1 i2 i3 : state)
        (l : label) (test : TTS) (imp : IOTS) :
      ind_test_execution_empty_reachability t1 i1 t2 i2 test imp ->
      ind_test_execution_transition t2 i2 (event l) t3 i3 test imp ->
      ind_test_execution_one_step_reachability t1 i1 l t3 i3 test imp.

Inductive ind_test_execution_seq_reachability :
    state -> state -> list label -> state -> state -> TTS -> IOTS -> Prop :=
  | test_execution_seq_reachability_r1 (t1 t2 i1 i2 : state) (test : TTS) (imp : IOTS) :
      ind_test_execution_empty_reachability t1 i1 t2 i2 test imp ->
      ind_test_execution_seq_reachability t1 i1 [] t2 i2 test imp
  | test_execution_seq_reachability_r2 (t1 i1 t2 i2 t3 i3 : state) (l : label)
        (ll : list label) (test : TTS) (imp : IOTS) :
      ind_test_execution_one_step_reachability t1 i1 l t2 i2 test imp ->
      ind_test_execution_seq_reachability t2 i2 ll t3 i3 test imp ->
      ind_test_execution_seq_reachability t1 i1 (l :: ll) t3 i3 test imp.

Definition ind_test_trace (ll : list label) (final_t final_i : state)
    (test : TTS) (imp : IOTS) : Prop :=
  ind_test_execution_seq_reachability
    test.(iots).(embedded_iolts).(sc_lts).(lts).(q0)
    imp.(embedded_iolts).(sc_lts).(lts).(q0)
    ll
    final_t
    final_i
    test
    imp.

Definition ind_test_run (ll : list label) (test : TTS) (imp : IOTS) : Prop :=
  exists (i' : state),
    ind_test_trace ll test.(pass_state) i' test imp \/
    ind_test_trace ll test.(fail_state) i' test imp.

(* Definition 16.3 *)
Definition ind_passes (test : TTS) (imp : IOTS) : Prop :=
  forall (ll : list label) (i' : state),
    ind_test_run ll test imp ->
    ~ ind_test_trace ll test.(fail_state) i' test imp.

(* Definition 16.4 *)
Inductive ind_passes_set : set TTS -> IOTS -> Prop :=
  | passes_set_r1 (imp : IOTS) :
      ind_passes_set [] imp
  | passes_set_r2 (test : TTS) (tests : set TTS) (imp : IOTS) :
      ind_passes test imp ->
      ind_passes_set tests imp ->
      ind_passes_set (test :: tests) imp.

Definition ind_fails_set (tests : set TTS) (imp : IOTS) : Prop :=
  exists (test : TTS), In test tests /\ ~ ind_passes test imp.
