Require Import IOTS_ex.
Require Import LTS_ex.
Require Import semantics.
Require Import graphviz.
Require Import String.

Local Open Scope string_scope.
(* Uncomment this to see generated DOT strings. 
Compute (generate_dot_behaviour_expressions "USER" vending_machine_ctx 100).
Compute (generate_dot_behaviour_expressions "MACHINE" vending_machine_ctx 100).
Compute (generate_dot_behaviour_expressions "SYSTEM" vending_machine_ctx 100).
Compute (generate_dot_lts fig2_r).
Compute ( generate_dot_IOLTS fig4_k3_IOLTS).
Compute ( generate_dot_s_IOLTS fig6_r).
*)
Local Close Scope string_scope.
