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

Ltac t_list_not_empty :=
  unfold not ; intros H ; inversion H.

Ltac t_elem_not_in_list :=
  unfold not ; intros H ; simpl in H ;
  repeat (destruct H ; inversion H).

Ltac t_elem_in_list :=
  repeat (try (left ; reflexivity) ; right).

Ltac t_all_elem_in_list :=
  repeat (split) ; t_elem_in_list.

Ltac t_all_elem_not_in_list :=
  repeat (split) ; t_elem_not_in_list.

Ltac t_trans_list_valid :=
  repeat split; (t_elem_in_list; fail) + ((right; reflexivity) + (left; t_elem_in_list)).

Ltac proof_absurd_different_hyp _Hd :=
  (unfold not in _Hd; exfalso; apply _Hd; reflexivity) + (idtac).

Ltac tr_not_in_list_hyp Hyp :=
  let Hyp' := fresh "Hyp'" in
    repeat(inversion Hyp as [Hyp'|Hyp']; [inversion Hyp'|]; clear Hyp; rename Hyp' into Hyp); inversion Hyp.

Ltac core_transition _Ht3 _Ht4 _Ht5 _Ht6 := 
  repeat(inversion _Ht4 as [_Aux|_Aux];
    [(inversion _Aux; fail) + (subst); tr_not_in_list_hyp _Ht6 |];
   clear _Ht4; rename _Aux into _Ht4); (inversion _Ht4; fail) + (idtac).

Ltac proof_incl H :=
  let aux := fresh "aux" in
    repeat(inversion H as [aux|aux]; [inversion aux; fail |]; clear H; rename aux into Hs).

Ltac proof_incl_goal :=
  simpl; unfold incl; intros Hlabel Hincl; apply Hincl.

Ltac proof_absurd_transition _Ht :=
  let s1 := fresh "s1" in
  let s2 := fresh "s2" in
  let l := fresh "l" in
  let p := fresh "p" in
  let _Ht3 := fresh "_Ht3" in
  let _Ht5 := fresh "_Ht5" in
  let _Ht6 := fresh "_Ht6" in
    inversion _Ht as [s1 s2 l p [_Ht3 [_Ht4 [_Ht5 _Ht6]]]]; subst; core_transition _Ht3 _Ht4 _Ht5 _Ht6.

Ltac loop_tactics ltac Hyp :=
  let Hyp' := fresh "Hyp'" in
    repeat(
            inversion Hyp as [Hyp'|Hyp'];
            [ subst; ltac |];
            clear Hyp; rename Hyp' into Hyp);
    inversion Hyp.

(*Definition fig2_r : LTS.
Proof.
  apply (mkLTS
          [0;1;2;3;4;5]
          ["but";"liq";"choc"]
          [(0,"but",1);(1,"liq",3);
            (0,"but",2);(2,"but",4);(4,"choc",5)]
          0).
  { t_list_not_empty. }
  { t_elem_not_in_list. }
  { t_elem_in_list. }
  { t_trans_list_valid. }
  { t_all_elem_not_in_list. }
  { t_all_elem_not_in_list. }
  { t_all_elem_not_in_list. }
Defined. *)

(** Definition 3*)
Inductive ind_transition : state -> transition_label -> state -> LTS -> Prop :=
  | transition_r1 : forall (s s' : state) (l : label) (p : LTS),
                          In s p.(Q) /\ In s' p.(Q) /\ In l p.(L)
                                /\ In (s, event l, s') p.(T) -> ind_transition s (event l) s' p
  | transition_r2 : forall (s s' : state) (p : LTS),
                          In s p.(Q) /\ In s' p.(Q)
                                /\ In (s, tau, s') p.(T) -> ind_transition s tau s' p.

Inductive ind_transition_seq : state -> list transition_label -> state -> LTS -> Prop :=
  | transition_seq_r1 : forall (s s' : state) (ll : list transition_label) (p : LTS),
                          ((length ll = 1) /\ (ind_transition s (hd tau ll) s' p))
                              \/
                          ((length ll > 1) /\ (exists (si : state), ind_transition s (hd tau ll) si p 
                                                  /\ ind_transition_seq si (tl ll) s' p))
                          -> ind_transition_seq s ll s' p.

Inductive ind_state_reaches_some_other : state -> list transition_label -> LTS -> Prop :=
  | state_reaches_some_other_r1 : forall (s : state) (ll : list transition_label) (p : LTS),
                                    (exists (s' : state), ind_transition_seq s ll s' p) ->
                                                            (ind_state_reaches_some_other s ll p).

Fixpoint all_labels_tau (ll : list transition_label) : Prop :=
  match ll with
  | []      => True
  | h :: tl => h = tau /\ all_labels_tau tl
  end.

(** Definition 4*)
Inductive ind_empty_reachability : state -> state -> LTS -> Prop :=
| empty_reachability_r1 : 
    forall (s s' : state) (p : LTS),
        s = s' \/
        ind_transition s tau s' p \/
        (exists (si : state), si <> s' /\
                              ind_transition s tau si p /\
                              ind_empty_reachability si s' p)
    -> ind_empty_reachability s s' p.

Inductive ind_one_step_reachability : state -> label -> state -> LTS -> Prop :=
| one_step_reachability_r1 : 
    forall (s s' : state) (l : label) (p : LTS),
        (exists (s1 s2 : state), ind_empty_reachability s s1 p
                                      /\
                                 ind_transition s1 (event l) s2 p
                                      /\
                                 ind_empty_reachability s2 s' p)
    -> ind_one_step_reachability s l s' p.

Inductive ind_seq_reachability : state -> list label -> state -> LTS -> Prop :=
| seq_reachability_r1 : 
    forall (s s' : state) (ll : list label) (p : LTS),
        (ll = [] /\ ind_empty_reachability s s p)
            \/
        ((ll <> [] /\ tl ll = []) /\ ind_one_step_reachability s (hd EmptyString ll) s' p)
            \/
        ((tl ll <> []) /\ (exists (si : state),
                              ind_one_step_reachability s (hd EmptyString ll) si p  /\
                              ind_seq_reachability si (tl ll) s' p))
    -> ind_seq_reachability s ll s' p.

Inductive ind_has_reachability_to_some_other : state -> list label -> LTS -> Prop :=
| has_reachability_to_some_other_r1 : 
    forall (s : state) (ll : list label) (p : LTS),
        (exists (s' : state), ind_seq_reachability s ll s' p) 
    -> ind_has_reachability_to_some_other s ll p.

(* Definition 5.1 *)
Fixpoint f_init (s : state)
  (lt : list (state * transition_label * state)) : set transition_label :=
 match lt with
 | [] => []
 | h :: t => match h with
             | (a,l,b) => if s =? a
                          then set_add transition_label_dec l (f_init s t)
                          else (f_init s t)
             end
 end.

Definition f_init_LTS (p : LTS) : list transition_label :=
  f_init p.(q0) p.(T).

Inductive ind_init : state -> set transition_label -> LTS -> Prop :=
| init_r1 : forall (s : state) (ll : set transition_label) (p : LTS),
              (forall (l : transition_label),
                  In l ll <-> exists (s' : state), In (s, l, s') p.(T))
            -> ind_init s ll p.

Inductive ind_init_LTS : set transition_label -> LTS -> Prop :=
| init_LTS_r1 : forall (ll : set transition_label) (p : LTS),
    ind_init p.(q0) ll p -> ind_init_LTS ll p.

(* A PARTIR DAQUI 02/03/2022 *)
(* Definition 5.2 *)
Inductive ind_traces : state -> list label -> LTS -> Prop :=
| traces_r1 : forall (s : state) (t : list label) (p : LTS),
                ind_has_reachability_to_some_other s t p
                -> ind_traces s t p.

Inductive ind_traces_LTS : list label -> LTS -> Prop :=
| traces_LTS_r1 : forall (ll : list label) (p : LTS),
    ind_traces p.(q0) ll p -> ind_traces_LTS ll p.

(* n entendi pra que serve a definicao de baixo *)
Definition b_string_dec (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(* mas fiz essa pra ajustar a definição de baixo *)
Definition b_transition_label_dec (t1 t2 : transition_label) : bool :=
  if transition_label_dec t1 t2 then true
  else false.

(*adicionei o scope de bool tbm pra funcionar o && *)
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

Fixpoint f_after_aux (ls : set state) (ll : list transition_label)(lt : list transition) : set state :=
  match ls, ll with
  | [], _               =>  []
  | a, []               =>  a
  | h1 :: t1, h2 :: t2  =>  set_union Nat.eq_dec (f_after_aux (f_transition_seq h1 h2 lt) t2 lt) (f_after_aux (f_after_aux' t1 h2 lt) t2 lt)
  end.

Definition f_after (s : state) (ll : list transition_label) (lt : list transition) : set state :=
  f_after_aux [s] ll lt.
  
Definition f_after_LTS (ll : list transition_label) (p : LTS) : set state := 
  f_after p.(q0) ll p.(T).

Inductive ind_after : state -> list label -> set state -> LTS -> Prop:=
| after_r1 : forall (s : state) (ll : list label) (ls : list state) (p : LTS),
                  ls = [] /\ ~ ind_has_reachability_to_some_other s ll p 
                                                        -> ind_after s ll [] p
| after_r2 : forall (s : state) (ll : list label) (ls : list state) (p : LTS),
                  ls <> [] /\ 
                  (forall (a : state),
                      In a p.(Q) -> ind_seq_reachability s ll a p <-> In a ls)
                                                        -> ind_after s ll ls p.

Inductive ind_after_LTS : list label -> list state -> LTS -> Prop :=
| after_LTS_r1 : forall (ll : list label) (ls : list state) (p : LTS),
                    ind_after p.(q0) ll ls p -> ind_after_LTS ll ls p.

(* Definition 5.4 *)
Inductive ind_P_after_sigma : set state -> list label -> set state -> LTS -> Prop :=
| P_after_sigma_r1 : 
    forall (P : set state) (t : list label) (ls : set state) (p : LTS),
        (forall (s' : state),
            In s' ls <-> exists (s : state), In s P /\ ind_seq_reachability s t s' p)
    ->  ind_P_after_sigma P t ls p.

(* Definition 5.5 *)
Fixpoint elem_has_no_transition_in_A (s : state) (ll : set transition_label) (p : LTS) : Prop :=
match ll with
| []        =>  True
| h :: tail =>  ~ ind_state_reaches_some_other s [h] p /\ 
                  elem_has_no_transition_in_A s tail p
end.

Inductive ind_refuses : set state -> set transition_label -> LTS -> Prop :=
| refuses_r1  : forall (ls : set state) (ll : set transition_label) (p : LTS),
                  (exists (s : state), In s ls /\
                         elem_has_no_transition_in_A s (set_add transition_label_dec tau ll) p) 
                -> ind_refuses ls ll p.

(* Definition 5.6 *)
Fixpoint exists_seq_to_reach_every_elem (s : state) (ls : set state) (p : LTS) : _ :=
match ls with
| []      =>  True
| h :: t  =>  exists (ll : list label), 
                  ind_seq_reachability s ll h p /\ 
                  exists_seq_to_reach_every_elem s t p
end.

Inductive ind_der : state -> set state -> LTS -> Prop :=
| der_r1  : forall  (s : state) (ls : set state) (p : LTS),
               exists_seq_to_reach_every_elem s ls p -> ind_der s ls p.

Inductive ind_der_LTS : set state -> LTS -> Prop :=
| der_LTS_r1  : forall (ls : set state) (p : LTS),
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
