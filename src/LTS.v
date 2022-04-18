(** Uma biblioteca em Coq para testes baseados em modelos **)

Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import PeanoNat.

(* Definition 1 *)
Section SectionLTS.
  Definition state  := nat.
  Definition label := string.
  Inductive transition_label :=
  | event : label -> transition_label
  | tau   : transition_label.

  Local Open Scope type_scope.
  Definition transition := state * transition_label * state.
  Local Close Scope type_scope.

  Theorem transition_label_dec : forall x y : transition_label, {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply string_dec.
  Defined.

  Theorem transition_dec : forall x y : transition, {x = y} + {x <> y}.
  Proof.
    decide equality.
    - apply Nat.eq_dec.
    - decide equality.
      + decide equality.
        apply string_dec.
      + apply Nat.eq_dec.
  Defined.

  Fixpoint each_transition_is_valid
    (t : list transition) (Q : list state) (L : list label) : Prop :=
      match t with
      | []                      => True
      | (s1, event l, s2) :: tl => In s1 Q /\ In s2 Q /\ In l L /\
                                   each_transition_is_valid tl Q L
      | (s1, tau, s2) :: tl     => In s1 Q /\ In s2 Q /\
                                   each_transition_is_valid tl Q L
      end.

  Record LTS : Type := mkLTS {
      Q   : set state
    ; L   : set label
    ; T   : set transition
    ; q0  : state

    ; Q_non_empty       : Q <> []
    ; q0_in_Q           : In q0 Q
    ; valid_transitions : each_transition_is_valid T Q L
    ; no_repetition_Q   : NoDup Q
    ; no_repetition_L   : NoDup L
    ; no_repetition_T   : NoDup T
  }.
End SectionLTS.

(** Definition 3*)
Inductive ind_transition : state -> transition_label -> state -> LTS -> Prop :=
  | transition_r1 (s s' : state) (l : label) (p : LTS):
      In (s, event l, s') p.(T) ->
      ind_transition s (event l) s' p
  | transition_r2 (s s' : state) (p : LTS) :
      In (s, tau, s') p.(T) ->
      ind_transition s tau s' p.

Inductive ind_transition_seq : state -> list transition_label -> state -> LTS -> Prop :=
  | transition_seq_r1 (s s' : state) (l : transition_label) (p : LTS) :
      ind_transition s l s' p ->
      ind_transition_seq s [l] s' p
  | transition_seq_r2  (s s' si : state) (l1 l2 : transition_label)
        (ll : list transition_label) (p : LTS) :
      ind_transition s l1 si p ->
      ind_transition_seq si (l2 :: ll) s' p ->
      ind_transition_seq s (l1 :: l2 :: ll) s' p.

Inductive ind_state_reaches_some_other : state -> list transition_label -> LTS -> Prop :=
  | state_reaches_some_other_r1 (s s': state) (ll : list transition_label) (p : LTS) :
      ind_transition_seq s ll s' p ->
      ind_state_reaches_some_other s ll p.

(** Definition 4*)
Inductive ind_empty_reachability : state -> state -> LTS -> Prop :=
  | empty_reachability_r1 (s : state) (p : LTS) :
      ind_empty_reachability s s p
  | empty_reachability_r2 (s si s' : state) (p : LTS) :
      ind_transition s tau si p ->
      ind_empty_reachability si s' p ->
      ind_empty_reachability s s' p.

Inductive ind_one_step_reachability : state -> label -> state -> LTS -> Prop :=
  | one_step_reachability_r1 (s s' s1 s2 : state) (l : label) (p : LTS) :
      ind_empty_reachability s s1 p ->
      ind_transition s1 (event l) s2 p ->
      ind_empty_reachability s2 s' p ->
      ind_one_step_reachability s l s' p.

Inductive ind_seq_reachability : state -> list label -> state -> LTS -> Prop :=
  | seq_reachability_r1 (s s' : state) (p : LTS) :
      ind_empty_reachability s s' p ->
      ind_seq_reachability s [] s' p
  | seq_reachability_r2 (s si s' : state) (l1: label) (ll : set label) (p : LTS) :
      ind_one_step_reachability s l1 si p ->
      ind_seq_reachability si ll s' p ->
      ind_seq_reachability s (l1 :: ll) s' p.

Inductive ind_has_reachability_to_some_other : state -> list label -> LTS -> Prop :=
  | has_reachability_to_some_other_r1 (s s' : state) (ll : list label) (p : LTS) :
      ind_seq_reachability s ll s' p ->
      ind_has_reachability_to_some_other s ll p.

Inductive ind_init : state -> set transition_label -> LTS -> Prop :=
  | init_r1 (s : state) (ll : set transition_label) (p : LTS) :
      (forall (l : transition_label),
        In l ll <-> exists (s' : state), In (s, l, s') p.(T)) ->
      ind_init s ll p.

Inductive ind_init_LTS : set transition_label -> LTS -> Prop :=
  | init_LTS_r1 (ll : set transition_label) (p : LTS) :
      ind_init p.(q0) ll p -> ind_init_LTS ll p.

(* TODO: we have analysed the definitions up to this point *)

(* Definition 5.2 *)
Inductive ind_traces : state -> list label -> LTS -> Prop :=
  | traces_r1 (s : state) (t : list label) (p : LTS) :
      ind_has_reachability_to_some_other s t p ->
      ind_traces s t p.

Inductive ind_traces_LTS : list label -> LTS -> Prop :=
  | traces_LTS_r1 (ll : list label) (p : LTS) :
      ind_traces p.(q0) ll p -> ind_traces_LTS ll p.

(* Definition 5.3 *)
Definition ind_after (s : state) (ll : list label) (ls : list state) (p : LTS)
    : Prop :=
  forall (a : state), ind_seq_reachability s ll a p <-> In a ls.

Inductive ind_after_LTS : list label -> list state -> LTS -> Prop :=
  | after_LTS_r1 (ll : list label) (ls : list state) (p : LTS) :
      ind_after p.(q0) ll ls p ->
      ind_after_LTS ll ls p.

(* Definition 5.4 *)
Inductive ind_P_after_sigma : set state -> list label -> set state -> LTS -> Prop :=
  | P_after_sigma_r1 (P : set state) (t : list label) (ls : set state) (p : LTS) :
      (forall (s' : state),
        In s' ls <->
        exists (s : state), In s P /\ ind_seq_reachability s t s' p) ->
      ind_P_after_sigma P t ls p.

(* Definition 5.5 *)
Fixpoint elem_has_no_transition_in_A (s : state) (ll : set transition_label)
    (p : LTS) : Prop :=
  match ll with
  | []        =>  True
  | h :: tail =>  ~ ind_state_reaches_some_other s [h] p /\ 
                    elem_has_no_transition_in_A s tail p
  end.

Inductive ind_refuses : set state -> set transition_label -> LTS -> Prop :=
  | refuses_r1 (ls : set state) (s : state) (ll : set transition_label) (p : LTS) :
      In s ls ->
      elem_has_no_transition_in_A s (set_add transition_label_dec tau ll) p ->
      ind_refuses ls ll p.

(* Definition 5.6 *)
Fixpoint exists_seq_to_reach_every_elem (s : state) (ls : set state) (p : LTS) : Prop :=
  match ls with
  | []      =>  True
  | h :: t  =>  exists (ll : list label), 
                    ind_seq_reachability s ll h p /\ 
                    exists_seq_to_reach_every_elem s t p
  end.

Inductive ind_der : state -> set state -> LTS -> Prop :=
  | der_r1 (s : state) (ls : set state) (p : LTS) :
     exists_seq_to_reach_every_elem s ls p ->
     ind_der s ls p.

Inductive ind_der_LTS : set state -> LTS -> Prop :=
  | der_LTS_r1 (ls : set state) (p : LTS) :
                     ind_der p.(q0) ls p -> ind_der_LTS ls p.

(* Definition 5.7 *)
Definition has_finite_behaviour (s : state) (lts : LTS) : Prop :=
  exists (n : nat), forall (t : list label), ind_traces s t lts -> length t <= n.

Definition has_finite_behaviour_LTS (lts : LTS) : Prop :=
  exists (n : nat), forall (t : list label), ind_traces lts.(q0) t lts -> length t <= n.

(* Definition 5.8 *)
Definition finite_state (p : state) (lts : LTS) : Prop :=
  exists (n : nat),
    forall (ls : set state),
      ind_der p ls lts -> length ls < n.

Definition finite_state_LTS (lts : LTS) : Prop :=
  exists (n : nat),
    forall (ls : set state),
      ind_der_LTS ls lts -> length ls < n.

(* Definition 5.9 *)
Definition ind_deterministic (lts : LTS) : Prop :=
  forall (t : list label) (ls : set state),
    ind_traces_LTS t lts ->
    ind_after_LTS t ls lts ->
    length ls = 1.

(* Definição 5.10 *)
Definition image_finite (p : state) (lts : LTS) : Prop :=
    forall (ll : list label) (ls : set state),
      incl ls lts.(Q) /\ ind_after p ll ls lts -> exists (n : nat), length ls < n.

Definition image_finite_LTS (lts : LTS) : Prop :=
  image_finite lts.(q0) lts.

(* Definição 5.11 *)
Fixpoint all_labels_tau (ll : list transition_label) : Prop :=
  match ll with
  | []      => True
  | h :: tl => h = tau /\ all_labels_tau tl
  end.

(* Definição 5.12 *)
Definition strongly_converging (lts : LTS) : Prop :=
  forall (s : state) (t : list transition_label),
    t <> [] /\ all_labels_tau t ->
    ~ ind_transition_seq s t s lts.

(* Strongly converging LTS *)
Record SC_LTS : Type := mkSC_LTS {
      lts : LTS
    ; is_strongly_converging  : strongly_converging lts
  }.
