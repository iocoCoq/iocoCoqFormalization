Require Import LTS.
Require Import IOTS.
Require Import BE_trans_set_creator.
Require Import BE_syntax.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import String.

Local Open Scope string_scope.

Definition event_to_str (e : Event) : string :=
  match e with
  | InternalEvent => "τ"
  | ExternalEvent n => n
  end.

Fixpoint process_behaviour_to_str (B : ProcessBehaviour) : string :=
  match B with
  | Prefix e B' => "(" ++ event_to_str e ++ ";" ++ process_behaviour_to_str B' ++ ")"
  | Choice (Values Bs) =>
    let fix expand_choice (l : list ProcessBehaviour) : string :=
       match l with
       | nil => "STOP"
       | B' :: nil => process_behaviour_to_str B'
       | B' :: tl => process_behaviour_to_str B' ++ " [] " ++ expand_choice tl
       end
    in "( " ++ expand_choice Bs ++ ")"
  | Parallel B1 g B2 =>
    "(" ++ process_behaviour_to_str B1 ++ " |[" ++ (concat ", " g) ++ "]| " ++
    process_behaviour_to_str B2 ++ ")"
  | Hide B' g =>
    "(HIDE { " ++ (concat ", " g) ++ " } IN " ++ process_behaviour_to_str B' ++ ")"
  | ProcessInstantiation p => p
  end.

Fixpoint generate_dot {State Event : Type} (lts : set (State * Event * State))
  (state_to_str : State -> string) (event_to_str : Event -> string) : string :=
  match lts with
  | nil => ""
  | (P, e, Q) :: tl =>
    " <" ++ state_to_str P ++ "> -> <" ++ state_to_str Q ++ ">" ++
    " [label=<" ++ event_to_str e ++ ">];" ++ (generate_dot tl state_to_str event_to_str)
  end.

Definition style_initial_state {State : Type} (q0 : State) (state_to_str : State -> string) : string :=
  "<" ++ state_to_str q0 ++ "> [style=bold, color=red];".

Definition generate_dot_behaviour_expressions
  (start_process : ProcessName) (ctx : BehaviourExpressions) (i : nat): string :=
  match createBehaviourTransSet ctx start_process i with
  | Some lts =>
    "digraph " ++ start_process ++ "_LTS { "
      ++
      match getProcessBehaviour start_process ctx with
      | Some B => style_initial_state B process_behaviour_to_str
      | _ => ""
      end
      ++
      (generate_dot lts process_behaviour_to_str event_to_str)
      ++ " }"
  | _ => ""
  end.

Definition digit_to_str (n : nat) : string :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end.

Fixpoint nat_to_str' (n i : nat) : string :=
  match i with
  | 0 => "0"
  | S i' => if Nat.ltb n 9
            then digit_to_str n
            else nat_to_str' (Nat.div n 10) i' ++ digit_to_str (Nat.modulo n 10)
  end.

Definition nat_to_str (n : nat) : string := nat_to_str' n n.

Definition transition_label_to_str (l : transition_label) : string :=
  match l with
  | event e => e
  | tau => "τ"
  end.

Definition generate_dot_lts (lts : LTS) : string :=
  "digraph LTS { "
    ++ style_initial_state lts.(q0) nat_to_str
    ++ (generate_dot lts.(T) nat_to_str transition_label_to_str)
    ++ " }".

Definition iolts_transition_label_to_str (Li : set label)
    (l : transition_label) : string :=
  match l with
  | event e =>
      if set_mem string_dec e Li
      then "?" ++ e
      else "!" ++ e
  | tau => "τ"
  end.

Definition generate_dot_IOLTS (iolts : IOLTS) : string :=
  "digraph IOLTS { "
  ++ style_initial_state iolts.(sc_lts).(lts).(q0) nat_to_str
  ++ (generate_dot iolts.(sc_lts).(lts).(T) nat_to_str
      (iolts_transition_label_to_str iolts.(L_i)))
  ++ " }".

Definition generate_dot_s_IOLTS (s_iolts : s_IOLTS) : string :=
  "digraph s_IOLTS { "
  ++ style_initial_state s_iolts.(iolts).(sc_lts).(lts).(q0) nat_to_str
  ++ (generate_dot s_iolts.(iolts).(sc_lts).(lts).(T) nat_to_str
      (iolts_transition_label_to_str s_iolts.(iolts).(L_i)))
  ++ generate_dot (map (fun x => (x, "δ", x)) s_iolts.(Ts)) nat_to_str id
  ++ " }".
Local Close Scope string_scope.