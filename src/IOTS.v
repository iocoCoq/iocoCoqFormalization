Require Import LTS.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import RelationClasses.

Open Scope list_scope.

(* Definição 6*)
Section SectionIOLTS.

  Fixpoint is_disjoint (l m : list label) : Prop :=
    match l with
    | []      =>  True
    | h :: t  =>  ~ In h m /\ is_disjoint t m
    end.

  Record IOLTS : Type := mkIOLTS {
      lts : LTS
    ; L_i : list label
    ; L_u : list label
    ; disjoint_input_output_labels  : is_disjoint L_i L_u
    ; is_IOLTS                       : is_valid_LTS (L_i ++ L_u) lts
    ; no_repetition_L_i             : NoDup L_i
    ; no_repetition_L_u             : NoDup L_u
  }.
End SectionIOLTS.

(* Definição 7*)
Section SectionIOTS.

  Fixpoint elem_reaches_another_with_all_labels (s : state) (ll : set label) (p : LTS) : Prop :=
  match ll with
  | []      =>  True
  | l :: t  =>  ind_has_reachability_to_some_other s [l] p /\
                         elem_reaches_another_with_all_labels s t p
  end.

  Fixpoint every_elem_reaches_some_other (ls : set state) (ll : set label) (p : LTS) : Prop :=
  match ls with
  | []      =>  True
  | h :: t  =>  elem_reaches_another_with_all_labels h ll p /\
                                    every_elem_reaches_some_other t ll p
  end.

  Definition valid_iots (p : IOLTS) : Prop :=
      exists (ls : set state),
          ind_der_LTS ls p.(lts) /\
          every_elem_reaches_some_other ls p.(L_i) p.(lts).

  Record IOTS : Type := mkIOTS {
      iolts                   : IOLTS
    ; input_actions_activated : valid_iots iolts
  }.
End SectionIOTS.

Ltac exists_reachability :=
apply seq_reachability_r1; right ; left; split ; split ;
unfold not ; intros ; try (inversion H) ;
try reflexivity;
split; simpl; unfold not; try intro; try inversion H.

Ltac empty_reachability_left := left; reflexivity.

(* Definição 8*)
Inductive ind_quiescent : state -> IOLTS -> Prop :=
| quiescent_r1 : forall (s : state) (p : IOLTS),
                      (forall (s' : state) (l : label),
                          In l p.(L_u) /\ In s' p.(lts).(Q) ->
                          ~ ind_transition s (event l) s' p.(lts)) -> ind_quiescent s p
| quiescent_r2 : forall (s : state) (p : IOLTS),
                      (forall (s' : state),
                          In s' p.(lts).(Q) ->
                          ~ ind_transition s tau s' p.(lts)) -> ind_quiescent s p.

Inductive ind_quiescent_traces : list label -> IOLTS -> Prop :=
| quiescent_trace_r1  : forall (ll : list label) (p : IOLTS) (ls : set state),
                                ind_traces_LTS ll p.(lts) /\
                                    ind_after_LTS ll ls p.(lts) /\
                                        (exists (s : state), In s ls /\ 
                                            ind_quiescent s p) ->  ind_quiescent_traces ll p.

(* Definição 9*)
Section SectionSuspensionIOLTS.
  Definition delta := "delta".

  Record s_IOLTS : Type := mksIOLTS {
      s_iolts               : IOLTS
    ; Ts                    :  list (state * label * state)
    ; Q_del                 :=  s_iolts.(lts).(Q)
    ; L_del                 :=  set_union string_dec s_iolts.(lts).(L) [delta]
    ; Li_del                :=  s_iolts.(L_i)
    ; Lu_del                :=  set_union string_dec s_iolts.(L_u) [delta]
    ; T_del                 :=  s_iolts.(lts).(T) ++ Ts
    ; delta_not_in_L        : ~ In delta s_iolts.(lts).(L)
    ; valid_del_transitions : forall (s s' : state) (l : label), 
                                        In (s, l, s') Ts -> s = s' /\ l = delta /\ In s Q_del
    ; Ts_complete_correct   : forall (s : state), In (s, delta, s) Ts <-> In s Q_del /\ ind_quiescent s s_iolts
  }.
End SectionSuspensionIOLTS.

Ltac all_delta_trans := intros s s' l A;
    repeat(inversion A as [B|B];
             [inversion B; split; [reflexivity | split; [reflexivity | t_elem_in_list]] | ];
           clear A; rename B into A); inversion A.
           
Ltac all_quiescent_trans_incl := intros B;
    repeat(inversion B as [C|C];
      [inversion C ;
        split;
        [t_elem_in_list
        |apply quiescent_r1; intros s' l D; destruct D as [D E];
         repeat(inversion D as [F|F];
           [repeat(inversion E as [G|G];
             [subst l;
              subst s';
              unfold not;
              intro H';
              inversion H' as [I J K L M];
              destruct M as [N [O [P Q]]];
              repeat(inversion Q as [R|R];
               [inversion R |]; clear Q; rename R into Q); inversion Q
             |]; clear E; rename G into E); inversion E
           |]; clear D; rename F into D); inversion D
        ]
      |]; clear B; rename C into B); inversion B.

Inductive ind_s_traces : state -> list label -> s_IOLTS -> Prop :=
| s_traces_r1 : forall (s : state) (t : list label) (p : s_IOLTS),
                   ind_traces s t p.(s_iolts).(lts) -> ind_s_traces s t p.

Inductive ind_s_traces_LTS : list label -> s_IOLTS -> Prop :=
| s_traces_LTS_r1 : forall (t : list label) (p : s_IOLTS),
                   ind_traces_LTS t p.(s_iolts).(lts) -> ind_s_traces_LTS t p.
