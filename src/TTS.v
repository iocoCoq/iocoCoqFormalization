Require Import LTS.
Require Import IOTS.
Require Import List.
Import Coq.Lists.List.ListNotations.
Require Import list_helper.
Require Import LTS_functions.


Section SectionTTS.

  Record TTS : Type := mkTTS {
      iots : IOTS
    ; fail_state : state
    ; pass_state : state
    ; sigma : label
    ; is_deterministic : True
    (*; TTs_Li := In sigma iots.(embedded_iolts).(L_u) *)
    ; sigma_is_valid : In sigma iots.(embedded_iolts).(L_u)
    ; fail_is_valid : In fail_state iots.(embedded_iolts).(sc_lts).(lts).(Q)
    ; pass_is_valid : In pass_state iots.(embedded_iolts).(sc_lts).(lts).(Q)
    ; valid_out_label : forall (q : state),
              In q iots.(embedded_iolts).(sc_lts).(lts).(Q) ->
              exists (a : label),
                In a iots.(embedded_iolts).(L_u) /\
                f_init q iots.(embedded_iolts).(sc_lts).(lts) [=]
                 map event (a :: iots.(embedded_iolts).(L_i))
    ; no_cycles :
        forall (t : list label) (s : state),
          t <> [] ->
          ind_seq_reachability s t s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = fail_state \/ s = pass_state
    ; pass_cycle :
        forall (l : label) (s : state),
          ind_transition pass_state (event l) s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = pass_state /\ (l = sigma \/ In l iots.(embedded_iolts).(L_i))
    ; fail_cycle :
        forall (l : label) (s : state),
          ind_transition fail_state (event l) s iots.(embedded_iolts).(sc_lts).(lts) ->
          s = fail_state /\ (l = sigma \/ In l iots.(embedded_iolts).(L_i))
  }.