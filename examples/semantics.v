Require Import ltacs.
Require Import BE_semantics.
Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.
Require Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import String.

Local Open Scope string_scope.
Local Open Scope list_scope.

(* Examples *)
Definition B := "a";; "B".
Definition B_ctx : BehaviourExpressions.
Proof.
  create_behaviour_expressions ["B" ::= B].
Defined.

Example example1 :
  sosStarR B_ctx B [ExternalEvent "a"] "B".
Proof.
  eapply sos_star_transitive_rule.
  - apply sos_prefix_rule.
  - apply sos_star_reflexivity_rule.
Qed.

Definition P := "but";; ("liq";; STOP [] "choc";; STOP).
Definition P_ctx : BehaviourExpressions.
Proof.
  create_behaviour_expressions ["P" ::= P].
Defined.

Example example2 :
  sosStarR P_ctx P [ExternalEvent "but"; ExternalEvent "liq"] STOP.
Proof.
  eapply sos_star_transitive_rule.
  - apply sos_prefix_rule.
  - eapply sos_star_transitive_rule.
    + eapply sos_choice_rule.
      * simpl. right. left. reflexivity.
      * apply sos_prefix_rule.
    + apply sos_star_reflexivity_rule.
Qed.

Example example3 : traceR P_ctx [ExternalEvent "but"; ExternalEvent "liq"] "P".
Proof.
  eapply trace_rule.
  - reflexivity.
  - apply example2.
Qed.

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