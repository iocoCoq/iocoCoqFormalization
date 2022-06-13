Require Import IOTS_ex.
Require Import LTS_ex.
Require Import TTS_ex.
Require Import semantics.
Require Import graphviz.
Require Import String.

Local Open Scope string_scope.
(* Uncomment this to see generated DOT strings.
Compute (generate_dot_behaviour_expressions "USER" vending_machine_ctx 100).
Compute (generate_dot_behaviour_expressions "MACHINE" vending_machine_ctx 100).
Compute (generate_dot_behaviour_expressions "SYSTEM" vending_machine_ctx 100).

Compute (generate_dot_behaviour_expressions "fig2_r" fig2_r_BE 6).
Compute (generate_dot_lts fig2_r).
Compute (generate_dot_IOLTS fig2_r_IOLTS).
Compute (generate_dot_s_IOLTS fig6_r).
Compute (generate_dot_TTS fig7_t1_TTS).
*)
Local Close Scope string_scope.
