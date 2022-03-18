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
  Qed.

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

(* TODO: Move this function to the place it is required. *)
Fixpoint all_labels_tau (ll : list transition_label) : Prop :=
  match ll with
  | []      => True
  | h :: tl => h = tau /\ all_labels_tau tl
  end.

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

(* TODO: Adjust the following definition (seq_reachability_r1) such that
         at least one label is required. *) 
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

(* Definition 5.1 *)
Fixpoint f_init_aux (s : state)
  (lt : list (state * transition_label * state)) : set transition_label :=
 match lt with
 | [] => []
 | h :: t => match h with
             | (a,l,b) => if s =? a
                          then set_add transition_label_dec l (f_init_aux s t)
                          else (f_init_aux s t)
             end
 end.
 
Definition f_init (s : state) (p : LTS) : set transition_label :=
  f_init_aux s p.(T).

Inductive ind_init : state -> set transition_label -> LTS -> Prop :=
  | init_r1 (s : state) (ll : set transition_label) (p : LTS) :
      (forall (l : transition_label),
        In l ll <-> exists (s' : state), In (s, l, s') p.(T)) ->
      ind_init s ll p.

Theorem ind_init_reflect :
  forall (s : state) (ll : set transition_label) (p : LTS),
    ind_init s ll p <-> f_init s p = ll.
Proof. Admitted.

Definition f_init_LTS (p : LTS) : list transition_label :=
  f_init p.(q0) p.

Inductive ind_init_LTS : set transition_label -> LTS -> Prop :=
  | init_LTS_r1 (ll : set transition_label) (p : LTS) :
      ind_init p.(q0) ll p -> ind_init_LTS ll p.
      
Theorem ind_init_LTS_reflect :
  forall (ll : set transition_label) (p : LTS),
    ind_init_LTS ll p <-> f_init_LTS p = ll.
Proof. Admitted.

(* TODO: we have analysed the definitions up to this point *)

(* Definition 5.2 *)
Inductive ind_traces : state -> list label -> LTS -> Prop :=
  | traces_r1 (s : state) (t : list label) (p : LTS) :
      ind_has_reachability_to_some_other s t p ->
      ind_traces s t p.

Inductive ind_traces_LTS : list label -> LTS -> Prop :=
  | traces_LTS_r1 (ll : list label) (p : LTS) :
      ind_traces p.(q0) ll p -> ind_traces_LTS ll p.

Definition b_transition_label_dec (t1 t2 : transition_label) : bool :=
  if transition_label_dec t1 t2
  then true
  else false.

Local Open Scope bool_scope.
(* Definition 5.3 *)
Fixpoint f_transition_seq (s : state) (l : transition_label)
  (lt : list transition) : set state :=
  match lt with
  | []               =>  []
  | (a, l', b) :: t  =>  if (s =? a) && (b_transition_label_dec l l')
                         then set_add Nat.eq_dec b (f_transition_seq s l t)
                         else f_transition_seq s l t
  end.
Local Close Scope bool_scope.

Fixpoint f_after_aux' (ls : set state) (l : transition_label)
  (lt : list (state * transition_label * state)) : set state :=
  match ls with
  | []      =>  []
  | h :: t  =>  set_union Nat.eq_dec (f_transition_seq h l lt) (f_after_aux' t l lt)
  end.

Fixpoint f_after_aux (ls : set state) (ll : list transition_label)
    (lt : list transition) : set state :=
  match ls, ll with
  | [], _               =>  []
  | a, []               =>  a
  | h1 :: t1, h2 :: t2  =>
    set_union
      Nat.eq_dec
      (f_after_aux (f_transition_seq h1 h2 lt) t2 lt)
      (f_after_aux (f_after_aux' t1 h2 lt) t2 lt)
  end.

Definition f_after (s : state) (ll : list transition_label)
    (lt : list transition) : set state :=
  f_after_aux [s] ll lt.

Definition f_after_LTS (ll : list transition_label) (p : LTS) : set state := 
  f_after p.(q0) ll p.(T).

Inductive ind_after : state -> list label -> set state -> LTS -> Prop :=
  | after_r1 (s : state) (ll : list label) (ls : list state) (p : LTS) :
      (forall (a : state),
        In a p.(Q) -> ind_seq_reachability s ll a p <-> In a ls) ->
      ind_after s ll ls p.

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
Definition is_deterministic (lts : LTS) : Prop :=
  forall (s : state) (t : list label) (ls : set state),
  In s lts.(Q) /\ ind_traces s t lts
    /\ ind_after s t ls lts -> length ls = 1.

(* Definição 5.10 *)
Definition image_finite (p : state) (lts : LTS) : Prop :=
    forall (ll : list label) (ls : set state),
      incl ls lts.(Q) /\ ind_after p ll ls lts -> exists (n : nat), length ls < n.

Definition image_finite_LTS (lts : LTS) : Prop :=
  image_finite lts.(q0) lts.

(* Definição 5.11 *)
Definition strongly_converging (lts : LTS) : Prop :=
  forall (s : state) (t : list transition_label),
    t <> [] /\ all_labels_tau t ->
    ~ ind_transition_seq s t s lts.

(* Definição 5.12 *)
Definition is_valid_LTS (ll : set label) (lts : LTS) : Prop :=
  strongly_converging lts /\ lts.(L) = ll.
