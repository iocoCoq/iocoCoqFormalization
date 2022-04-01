Require Import IOTS.
Require Import LTS.
Require Import LTS_functions.
Require Import Bool BinPos BinNat PeanoNat Nnat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import String.

Inductive ind_out_one_state : state -> set s_label -> s_IOLTS -> Prop :=
  | out_one_state_r1 (s : state) (p : s_IOLTS) :
      In s p.(Ts) -> ind_out_one_state s [delta] p
  | out_one_state_r2 (s : state) (p : s_IOLTS) (so : set s_label) :
      ~ In s p.(Ts) ->
      ~ In delta so ->
      (forall (l : label) (s' : state),
        In (s_event l) so <->
        In l p.(iolts).(L_u) /\ ind_transition s (event l) s' p.(iolts).(sc_lts).(lts)) ->
      ind_out_one_state s so p.

Definition ind_out (Q : set state) (so : set s_label) (p : s_IOLTS) : Prop :=
  forall (x : s_label),
    In x so -> exists (s : state) (so' : set s_label),
                (In s Q /\ ind_out_one_state s so' p /\ In x so')
    /\
    forall (s : state), In s Q ->
      exists (so' : set s_label), ind_out_one_state s so' p /\
        forall (o : s_label), In o so' -> In o so.

Theorem s_label_dec : forall x y : s_label, {x = y} + {x <> y}.
Proof.
  decide equality.
  apply string_dec.
Defined.

Fixpoint f_out_one_state' (s : state) (lt: list transition) (Lu : set label)
    : set s_label :=
  match lt with
  | [] => []
  | (q1, e, q2) :: t =>
      if s =? q1
      then
        match e with
        | event e' =>
            if set_mem string_dec e' Lu
            then set_add s_label_dec (s_event e') (f_out_one_state' s t Lu)
            else f_out_one_state' s t Lu
        | tau => f_out_one_state' s t Lu
        end
     else f_out_one_state' s t Lu
  end.

Definition f_out_one_state (s : state) (p : s_IOLTS) : set s_label :=
  f_out_one_state' s p.(iolts).(sc_lts).(lts).(T) p.(iolts).(L_u).

Fixpoint f_out (ls : set state) (p : s_IOLTS) : set s_label :=
  match ls with
  | []     => []
  | h :: t =>
      if set_mem Nat.eq_dec h p.(Ts)
      then set_add s_label_dec delta (f_out t p)
      else set_union s_label_dec (f_out_one_state h p) (f_out t p)
  end.

Definition ind_s_after (s : state) (ll : list s_label) (ls : list state)
    (p : s_IOLTS) : Prop :=
  forall (a : state), ind_s_seq_reachability s ll a p <-> In a ls.

Definition ind_s_after_LTS (ll : list s_label) (ls : list state)
    (p : s_IOLTS) : Prop :=
  ind_s_after p.(iolts).(sc_lts).(lts).(q0) ll ls p.

Definition ind_ioco (i : IOTS) (s : IOLTS) : Prop :=
  forall (t : list label) (Qi Qs : set state) (t out_i out_s : set s_label),
    ind_s_traces_LTS t (create_s_IOLTS s) ->
    ind_s_after_LTS t Qi (create_s_IOLTS i.(embedded_iolts)) ->
    ind_s_after_LTS t Qs (create_s_IOLTS s) ->
    ind_out Qi out_i (create_s_IOLTS i.(embedded_iolts)) ->
    ind_out Qs out_s (create_s_IOLTS s) ->
    incl out_i out_s.
Local Open Scope bool_scope.

Fixpoint f_after_one_s_label' (s : state) (l : s_label)
  (lt : list transition) (Ts : set state) : set state :=
  match l with
  | delta => if set_mem Nat.eq_dec s Ts
             then [s]
             else []
  | s_event e =>
      match lt with
      | []               =>  []
      | (a, l', b) :: t  =>  if (s =? a) && (b_transition_label_dec (event e) l')
                             then set_add Nat.eq_dec b (f_after_one_s_label' s l t Ts)
                             else f_after_one_s_label' s l t Ts
      end
  end.
Local Close Scope bool_scope.

Fixpoint f_after_one_s_label (ls : set state) (l : s_label)
    (lt : list transition) (Ts: set state): set state :=
  match ls with
  | []     => []
  | h :: t =>
      set_union
        Nat.eq_dec
        (f_after_one_s_label' h l lt Ts)
        (f_after_one_s_label t l lt Ts)
  end.

Fixpoint f_after_IOLTS' (ls : set state) (ll : list s_label) (p : s_IOLTS)
    : set state :=
  match ll with
  | []       => all_reachable_by_tau ls p.(iolts).(sc_lts).(lts)
  | h :: ll' =>
    let ls_tau := all_reachable_by_tau ls p.(iolts).(sc_lts).(lts) in
    let ls_after_one_step := 
      f_after_one_s_label ls_tau h p.(iolts).(sc_lts).(lts).(T) p.(Ts) in
      f_after_IOLTS' ls_after_one_step ll' p
  end.

Definition f_after_single_state_IOLTS (s : state) (ll : list s_label)
    (p : s_IOLTS) : set state :=
  f_after_IOLTS' [s] ll p.

Definition f_after_IOLTS (ll : list s_label) (p : s_IOLTS) : set state := 
  f_after_single_state_IOLTS p.(iolts).(sc_lts).(lts).(q0) ll p.

Definition f_ioco (i : IOTS) (s : IOLTS) : Prop :=
  forall (t : list s_label),
    ind_s_traces_LTS t (create_s_IOLTS s) ->
      incl (f_out
            (f_after_IOLTS t (create_s_IOLTS i.(embedded_iolts)))
            (create_s_IOLTS i.(embedded_iolts)))
           (f_out (f_after_IOLTS t (create_s_IOLTS s)) (create_s_IOLTS s)).
