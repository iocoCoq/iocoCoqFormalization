Require Export IOCO.
Require Export IOTS.
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