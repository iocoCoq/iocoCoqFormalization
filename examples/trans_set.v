Require Import ltacs.
Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.
Require Import BE_trans_set.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import BE_semantics.
Require Import String.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition P := "P" ::= "but";; ("liq";; "liq";; STOP [] "choc";; "but";; STOP).
Definition P_trans : BehaviourTransSet := [
  ("but";; ("liq";; "liq";; STOP [] "choc";; "but";; STOP),
   ExternalEvent "but",
   "liq";; "liq";; STOP [] "choc";; "but";; STOP) ;
  ("liq";; STOP,
   ExternalEvent "liq",
   STOP) ;
  ("but";; STOP,
   ExternalEvent "but",
   STOP) ;
  ("liq";; "liq";; STOP [] "choc";; "but";; STOP,
   ExternalEvent "choc",
   "but";; STOP) ;
  ("liq";; "liq";; STOP [] "choc";; "but";; STOP,
   ExternalEvent "liq",
   "liq";; STOP) ].
Definition P_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [P]. Defined.

Example example1 : BehaviourTransSetR P_ctx P_trans "P".
Proof. behaviour_trans_set_valid. Qed.

Definition v := "v" ::= "V".
Definition v_ctx : BehaviourExpressions.
Proof.
  create_behaviour_expressions [ v; "V" ::= "but";; ("liq";; "V" [] I;; "V") ].
Defined.
Definition v_trans : BehaviourTransSet := [
  (ProcessInstantiation "V",
   InternalEvent,
   "but";; ("liq";; "V" [] I;; "V"));
  ("but";; ("liq";; "V" [] I;; "V"),
   ExternalEvent "but",
   "liq";; "V" [] I;; "V");
  ("liq";; "V" [] I;; "V", InternalEvent, ProcessInstantiation "V");
  ("liq";; "V" [] I;; "V", ExternalEvent "liq", ProcessInstantiation "V")
].

Example example2 : BehaviourTransSetR v_ctx v_trans "v".
Proof. behaviour_trans_set_valid. Qed.

Definition Q :=
  "Q" ::= HIDE ["liq"; "but"] IN ("but";; ("liq";; STOP [] I;; STOP)).
Definition Q_trans : BehaviourTransSet := [
  (HIDE ["liq"; "but"] IN ("but";; ("liq";; STOP [] I;; STOP)),
   InternalEvent,
   HIDE ["liq"; "but"] IN ("liq";; STOP [] I;; STOP));
  (HIDE ["liq"; "but"] IN ("liq";; STOP [] I;; STOP),
   InternalEvent,
   HIDE ["liq"; "but"] IN STOP)
].
Definition Q_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [Q]. Defined.

Example example3 : BehaviourTransSetR Q_ctx Q_trans "Q".
Proof. behaviour_trans_set_valid. Qed.

Definition R :=
  "R" ::=
    "but";; I;; "liq";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; "liq";; STOP.
Definition R_trans : BehaviourTransSet := [
  ("but";; I;; "liq";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; "liq";; STOP,
   ExternalEvent "but",
   I;; "liq";; STOP |[ ["but"; "liq"] ]| "choc";; "liq";; STOP);
  (I;; "liq";; STOP |[ ["but"; "liq"] ]| "choc";; "liq";; STOP,
   ExternalEvent "choc",
   I;; "liq";; STOP |[ ["but"; "liq"] ]| "liq";; STOP);
  (I;; "liq";; STOP |[ ["but"; "liq"] ]| "choc";; "liq";; STOP,
   InternalEvent,
   "liq";; STOP |[ ["but"; "liq"] ]| "choc";; "liq";; STOP);
  ("liq";; STOP |[ ["but"; "liq"] ]| "choc";; "liq";; STOP,
   ExternalEvent "choc",
   "liq";; STOP |[ ["but"; "liq"] ]| "liq";; STOP);
  (I;; "liq";; STOP |[ ["but"; "liq"] ]| "liq";; STOP,
   InternalEvent,
   "liq";; STOP |[ ["but"; "liq"] ]| "liq";; STOP);
  ("liq";; STOP |[ ["but"; "liq"] ]| "liq";; STOP,
   ExternalEvent "liq",
   STOP |[ ["but"; "liq"] ]| STOP)
].
Definition R_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [R]. Defined.

Example example4 : BehaviourTransSetR R_ctx R_trans "R".
Proof. behaviour_trans_set_valid. Qed.

Definition AUX := "AUX" ::= "choc";; "AUX".
Definition P' := "P'" ::= HIDE ["liq"; "but"] IN ("AUX").
Definition P'_trans : BehaviourTransSet := [
  (HIDE ["liq"; "but"] IN ("AUX"),
   InternalEvent,
   HIDE ["liq"; "but"] IN ("choc";; "AUX"));
  (HIDE ["liq"; "but"] IN ("choc";; "AUX"),
   ExternalEvent "choc",
   HIDE ["liq"; "but"] IN ("AUX"))
].
Definition P'_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [AUX; P']. Defined.

Example example5 : BehaviourTransSetR P'_ctx P'_trans "P'".
Proof. behaviour_trans_set_valid. Qed.

Definition P'' := "P''" ::= HIDE ["choc"] IN ("AUX").
Definition P''_trans : BehaviourTransSet := [
  (HIDE ["choc"] IN ("AUX"), InternalEvent, HIDE ["choc"] IN ("choc";; "AUX"));
  (HIDE ["choc"] IN ("choc";; "AUX"), InternalEvent, HIDE ["choc"] IN ("AUX"))
].
Definition P''_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [AUX; P'']. Defined.

Example example6 : BehaviourTransSetR P''_ctx P''_trans "P''".
Proof. behaviour_trans_set_valid. Qed.

Definition P'''_AUX := "P'''_AUX" ::= "choc";; "P'''_AUX".
Definition P''' := "P'''" ::= HIDE ["but"; "liq"] IN "P'''_AUX".
Definition P'''_trans : BehaviourTransSet := [
  (HIDE ["but"; "liq"] IN "P'''_AUX",
   InternalEvent,
   HIDE ["but"; "liq"] IN "choc";; "P'''_AUX");
  (HIDE ["but"; "liq"] IN "choc";; "P'''_AUX",
   ExternalEvent "choc",
   HIDE ["but"; "liq"] IN "P'''_AUX") ].
Definition P'''_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [P'''_AUX; P''']. Defined.

Example example7 : BehaviourTransSetR P'''_ctx P'''_trans "P'''".
Proof. behaviour_trans_set_valid. Qed.

Definition S :=
  "S" ::=
    "choc";; "but";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; I;; STOP.
Definition S_trans : BehaviourTransSet := [
  ("choc";; "but";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; I;; STOP,
   ExternalEvent "choc",
   "but";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; I;; STOP);
  ("but";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; I;; STOP,
   ExternalEvent "but",
   STOP |[ ["but"; "liq"] ]| "choc";; I;; STOP);
  (STOP |[ ["but"; "liq"] ]| "choc";; I;; STOP,
   ExternalEvent "choc",
   STOP |[ ["but"; "liq"] ]| I;; STOP);
  (STOP |[ ["but"; "liq"] ]| I;; STOP,
   InternalEvent,
   STOP |[ ["but"; "liq"] ]| STOP)
].
Definition S_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [S]. Defined.

Example example8: BehaviourTransSetR S_ctx S_trans "S".
Proof. behaviour_trans_set_valid. Qed.

Definition T :=
  "T" ::=
    "but";; STOP |[ ["but"; "liq"] ]| ("T'" [] "but";; STOP [] "choc";; "T''").
Definition T' := "T'" ::= "but";; "choc";; "T'".
Definition T'' := "T''" ::= HIDE ["liq"] IN "liq";; "but";; STOP.

Definition T_trans : BehaviourTransSet := [
  ("but";; STOP |[ ["but"; "liq"] ]| ("T'" [] "but";; STOP [] "choc";; "T''"),
   ExternalEvent "but",
   STOP |[ ["but"; "liq"] ]| STOP);
  ("but";; STOP |[ ["but"; "liq"] ]| ("T'" [] "but";; STOP [] "choc";; "T''"),
   InternalEvent,
   "but";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; "T'");
  ("but";; STOP |[ ["but"; "liq"] ]| ("T'" [] "but";; STOP [] "choc";; "T''"),
   ExternalEvent "choc",
   "but";; STOP |[ ["but"; "liq"] ]| "T''");

  ("but";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; "T'",
   ExternalEvent "but",
   STOP |[ ["but"; "liq"] ]| "choc";; "T'");
  ("but";; STOP |[ ["but"; "liq"] ]| "T''",
   InternalEvent,
   "but";; STOP |[ ["but"; "liq"] ]| HIDE ["liq"] IN "liq";; "but";; STOP);

  (STOP |[ ["but"; "liq"] ]| "choc";; "T'",
   ExternalEvent "choc",
   STOP |[ ["but"; "liq"] ]| "T'");
  ("but";; STOP |[ ["but"; "liq"] ]| HIDE ["liq"] IN "liq";; "but";; STOP,
   InternalEvent,
   "but";; STOP |[ ["but"; "liq"] ]| HIDE ["liq"] IN "but";; STOP);

  (STOP |[ ["but"; "liq"] ]| "T'",
   InternalEvent,
   STOP |[ ["but"; "liq"] ]| "but";; "choc";; "T'");
  ("but";; STOP |[ ["but"; "liq"] ]| HIDE ["liq"] IN "but";; STOP,
   ExternalEvent "but",
   STOP |[ ["but"; "liq"] ]| HIDE ["liq"] IN STOP)
].
Definition T_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [T; T'; T'']. Defined.

Example example9: BehaviourTransSetR T_ctx T_trans "T".
Proof. behaviour_trans_set_valid. Qed.

Definition U := "U" ::= "U".
Definition U_trans : BehaviourTransSet := [
  (ProcessInstantiation "U", InternalEvent, ProcessInstantiation "U")
].
Definition U_ctx : BehaviourExpressions.
Proof. create_behaviour_expressions [U]. Defined.

Example example10: BehaviourTransSetR U_ctx U_trans "U".
Proof. behaviour_trans_set_valid. Qed.
