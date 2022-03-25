Require Import IOTS.
Require Import LTS.
Require Import LTS_functions.
Require Import Bool BinPos BinNat PeanoNat Nnat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import String.

Inductive out_label : Type :=
  | out_event : label -> out_label
  | delta : out_label.

Inductive ind_out_one_state : state -> set out_label -> s_IOLTS -> Prop :=
  | out_one_state_r1 (s : state) (p : s_IOLTS) :
      In s p.(Ts) -> ind_out_one_state s [delta] p
  | out_one_state_r2 (s : state) (p : s_IOLTS) (so : set out_label) :
      ~ In delta so ->
      (forall (l : label) (s' : state),
        In (out_event l) so <->
        In l p.(iolts).(L_u) /\ ind_transition s (event l) s' p.(iolts).(sc_lts).(lts)) ->
      ind_out_one_state s so p.

Definition ind_out (Q : set state) (so : set out_label) (p : s_IOLTS) : Prop :=
  forall (x : out_label),
    In x so <->
    exists (s : state) (so' : set out_label),
      (In s Q /\ ind_out_one_state s so' p /\ In x so').

Lemma out_label_dec :
  forall (o1 o2 : out_label), {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality. apply string_dec.
Qed.

Fixpoint f_out_one_state' (s : state) (lt: list transition) (Lu : set label)
    : set out_label :=
  match lt with
  | [] => []
  | (q1, e, q2) :: t =>
      if s =? q1
      then
        match e with
        | event e' =>
            if set_mem string_dec e' Lu
            then set_add out_label_dec (out_event e') (f_out_one_state' s t Lu)
            else f_out_one_state' s t Lu
        | tau => f_out_one_state' s t Lu
        end
     else f_out_one_state' s t Lu
  end.

Definition f_out_one_state (s : state) (p : s_IOLTS) : set out_label :=
  f_out_one_state' s p.(iolts).(sc_lts).(lts).(T) p.(iolts).(L_u).

Fixpoint f_out (ls : set state) (p : s_IOLTS) : set out_label :=
  match ls with
  | []     => []
  | h :: t =>
      if set_mem Nat.eq_dec h p.(Ts)
      then set_add out_label_dec delta (f_out t p)
      else set_union out_label_dec (f_out_one_state h p) (f_out t p)
  end.

Definition ind_ioco (i : IOTS) (s : IOLTS) : Prop :=
  forall (t : list label),
    ind_s_traces_LTS t (create_s_IOLTS s) ->
      incl (f_out
            (f_after_LTS t i.(embedded_iolts).(sc_lts).(lts))
            (create_s_IOLTS i.(embedded_iolts)))
           (f_out (f_after_LTS t s.(sc_lts).(lts)) (create_s_IOLTS s)).

