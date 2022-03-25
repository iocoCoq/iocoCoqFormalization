Require Import LTS.
Require Import list_helper.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import PeanoNat.


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

Theorem ind_init_reflect :
  forall (s : state) (ll : set transition_label) (p : LTS),
    ind_init s ll p <-> f_init s p = ll.
Proof. Admitted.

Definition f_init_LTS (p : LTS) : list transition_label :=
  f_init p.(q0) p.

Theorem ind_init_LTS_reflect :
  forall (ll : set transition_label) (p : LTS),
    ind_init_LTS ll p <-> f_init_LTS p = ll.
Proof. Admitted.

(* Definition 5.3 *)
Local Open Scope bool_scope.

Definition b_transition_label_dec (t1 t2 : transition_label) : bool :=
  if transition_label_dec t1 t2
  then true
  else false.

(* All states reachable from 's' immediately after a transition_label
   'l' (tau or event) *)
Fixpoint f_after_one_transition_label' (s : state) (l : transition_label)
  (lt : list transition) : set state :=
  match lt with
  | []               =>  []
  | (a, l', b) :: t  =>  if (s =? a) && (b_transition_label_dec l l')
                         then set_add Nat.eq_dec b (f_after_one_transition_label' s l t)
                         else f_after_one_transition_label' s l t
  end.
Local Close Scope bool_scope.

(* All states reachable from the states in 'ls' immediately after a
   transition_label 'l' (tau or event) *)
Fixpoint f_after_one_transition_label (ls : set state) (l : transition_label)
    (lt : list transition) : set state :=
  match ls with
  | []     => []
  | h :: t =>
      set_union
        Nat.eq_dec
        (f_after_one_transition_label' h l lt)
        (f_after_one_transition_label t l lt)
  end.

(* All states reachable from the states in 'ls' after following up to n tau
   transitions *)
Fixpoint f_after_n_tau (ls : set state) (n : nat) (lt : list transition) : set state :=
  match n, ls with
  | _, []   => []
  | 0, _    => ls
  | S n', _ => set_union
                  Nat.eq_dec
                  ls
                  (f_after_n_tau (f_after_one_transition_label ls tau lt) n' lt)
  end.

(* All states reachable from the states in 'ls' following only tau transitions *)
Definition all_reachable_by_tau (ls : set state) (p : LTS) :=
  f_after_n_tau ls (length p.(Q)) p.(T).

(* ls after ll *)
Fixpoint f_after' (ls : set state) (ll : list label) (p : LTS) : set state :=
  match ll with
  | []       => all_reachable_by_tau ls p
  | h :: ll' =>
    let ls_tau := all_reachable_by_tau ls p in
    let ls_after_one_step := f_after_one_transition_label ls_tau (event h) p.(T) in
      f_after' ls_after_one_step ll' p
  end.

(* s after ll *)
Definition f_after (s : state) (ll : list label) (p : LTS) : set state :=
  f_after' [s] ll p.

Definition f_after_LTS (ll : list label) (p : LTS) : set state := 
  f_after p.(q0) ll p.

Theorem ind_after_reflect:
  forall (s : state) (lt : list transition) (ll : list label)
      (ls : list state) (p : LTS),
    ind_after s ll ls p <-> (f_after s ll p) [=] ls.
Proof. Admitted.

Theorem ind_after_LTS_reflect:
  forall (lt : list transition) (ll : list label) (ls : list state) (p : LTS),
    ind_after_LTS ll ls p <-> (f_after_LTS ll p) [=] ls.
Proof. Admitted.
