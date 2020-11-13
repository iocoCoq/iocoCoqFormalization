(** Uma biblioteca em Coq para testes baseados em modelos **)

Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Lists.ListSet.
Require Import PeanoNat.
Require Import String.

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

  Theorem transition_dec : forall x y : transition, {x = y} + {x <> y}.
  Proof.
    decide equality.
    - apply Nat.eq_dec.
    - decide equality.
      + decide equality.
        apply string_dec.
      + apply Nat.eq_dec.
  Qed.

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
    ; T   : list transition
    ; q0  : state

    ; Q_non_empty       : Q <> []
    ; q0_in_Q           : In q0 Q
    ; valid_transitions : each_transition_is_valid T Q L
    ; no_repetition_Q   : NoDup Q
    ; no_repetition_L   : NoDup L
    ; no_repetition_T   : NoDup T
  }.
End SectionLTS.
