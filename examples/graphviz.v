Require Import BE_ltacs.
Require Import BE_syntax.
Require Import BE_trans_set_creator.
Import BE_syntax.BehaviourExpressionsNotations.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import String.

Local Open Scope string_scope.
Definition USER :=
  "USER" ::=
    "coffee";;("decaf";; "ready";; "drink";; "USER" []  "trad";; "ready";; "drink";; "USER")
    [] "tea";;("black";; "ready";; "drink";; "USER" []  "green";; "ready";; "drink";; "USER")
    [] "chocolate";; "ready";; "drink";; "USER".

Definition MACHINE :=
  "MACHINE" ::=
    "coffee";;("decaf";; "ready";; "MACHINE" []  "trad";; "ready";; "MACHINE")
    [] "chocolate";; "ready";; "MACHINE".

Definition SYSTEM :=
  "SYSTEM" ::=
    "MACHINE" |[ ["coffee"; "decaf"; "trad"; "tea"; "black"; "green"; "chocolate"; "ready"] ]| "USER".

Definition vending_machine_ctx: BehaviourExpressions.
Proof.
  create_behaviour_expressions [USER; MACHINE; SYSTEM].
Defined.

(* Uncomment this to see generated DOT strings.
Compute (generate_dot "USER" vending_machine_ctx 100).
Compute (generate_dot "MACHINE" vending_machine_ctx 100).
Compute (generate_dot "SYSTEM" vending_machine_ctx 100).
*)