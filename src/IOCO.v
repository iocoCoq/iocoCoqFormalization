Require Import IOTS.
Require Import LTS.
Require Import Bool BinPos BinNat PeanoNat Nnat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Coq.Lists.List.ListNotations.
Require Import String.

Fixpoint out_labels (ll : set label) (l_u : set label) : set label := 
match ll with
| []      =>  []
| h :: t  =>  if in_dec string_dec h l_u then set_add string_dec h (out_labels t l_u) 
                                         else out_labels t l_u
end.

Fixpoint in_labels (ll : set label) (l_i : set label) : set label := 
match ll with
| []      =>  []
| h :: t  =>  if in_dec string_dec h l_i then set_add string_dec h (in_labels t l_i) 
                                         else in_labels t l_i
end.
(*
Fixpoint f_out (ls : set state) (p : s_IOLTS) : set label :=
match ls with
| []      =>  []
| h :: t  =>  match out_labels (f_init h p.(T_del)) p.(Lu_del) with
              | [] =>  set_union string_dec [delta] (f_out t p)
              | a  =>  set_union string_dec a (f_out t p)
              end
end.

Definition ind_ioco (i s : s_IOLTS) : Prop := 
  forall (t : list label),
    ind_s_traces_LTS t s ->
      incl (f_out (f_after i.(s_iolts).(lts).(q0) t i.(T_del)) i)
           (f_out (f_after s.(s_iolts).(lts).(q0) t s.(T_del)) s).

*)