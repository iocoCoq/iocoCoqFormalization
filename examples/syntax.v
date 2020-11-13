Require Import BE_ltacs.
Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import String.

Local Open Scope string_scope.
(* Abstract syntax examples *)
Definition LTSp :=
  [ DefineProcess "p"
    (Prefix (ExternalEvent "but") (Prefix (ExternalEvent "liq") stop)) ].
Definition LTSq := 
  [ DefineProcess "q"
    (Prefix (ExternalEvent "but")
    (Choice (Values
      [Prefix (ExternalEvent "liq") stop; Prefix (ExternalEvent "choc") stop]))) ].
Definition LTSr :=
  [ DefineProcess "r" 
    (Choice (Values
      [Prefix (ExternalEvent "but") (Prefix (ExternalEvent "liq") stop);
       Prefix (ExternalEvent "but") (Prefix (ExternalEvent "but")
             (Prefix (ExternalEvent "choc") stop))]))].
Definition LTSu := [
(DefineProcess "U"
  (Prefix (ExternalEvent "but")
    (Choice (Values
      [Prefix (ExternalEvent "liq") (ProcessInstantiation "U");
       Prefix (ExternalEvent "choc") (ProcessInstantiation "U")]))))].
Definition LTSv := [
(DefineProcess "V"
  (Prefix (ExternalEvent "but")
    (Choice (Values
      [Prefix (ExternalEvent "liq") (ProcessInstantiation "V");
       Prefix InternalEvent (ProcessInstantiation "V")]))))].

(* Concrete syntax examples *)
Definition LTSp' := [ "p" ::= "but";; "liq";; STOP ].
Definition LTSq' := [ "q" ::= "but";; ("liq";; STOP [] "choc";; STOP) ].
Definition LTSr' :=
  [ "r" ::= "but";; "liq";; STOP [] "but";; "but";; "choc";; STOP ].
Definition LTSu' :=
  [ "u" ::= "U"; "U" ::= "but";; ("liq";; "U" [] "choc";; "U") ].
Definition LTSv' := [ "v" ::= "V"; "V" ::= "but";; ("liq";; "V" [] I;; "V") ].
Definition HideExample := [
  "q'" ::= HIDE ["liq"; "but"] IN ("but";; ("liq";; STOP [] "choc";; STOP))
].
Definition ParallelExample := [
  "r'" ::= "but";; "liq";; STOP |[ ["but"; "liq"] ]| "but";; "choc";; STOP
].
Definition InterleavingExample := [
  "r''" ::= "but";; "liq";; STOP ||| "but";; "but";; "choc";; STOP
].

(* Invalid BehaviourExpressions *)
Definition invalid : BehaviourExpressions.
Proof.
  Fail
    create_behaviour_expressions
      ["Q" ::= HIDE ["liq"; "but"] IN ("but";; ("liq";; STOP [] "choc";; "Q"))].
Abort.

Definition invalid : BehaviourExpressions.
Proof.
  Fail
    create_behaviour_expressions
      ["Q" ::= "but";; STOP;
       "Q" ::= "liq";; STOP].
Abort.

Definition invalid : BehaviourExpressions.
Proof.
  Fail
    create_behaviour_expressions
      ["Q" ::= "but";; "R";
       "L" ::= "liq";; STOP].
Abort.

Definition invalid : BehaviourExpressions.
Proof.
  Fail create_behaviour_expressions
    ["P'" ::= HIDE ["but"; "liq"] IN "choc";; "P'"].
Abort.

Definition invalid : BehaviourExpressions.
Proof.
  Fail create_behaviour_expressions
    ["P_AUX" ::= "choc";; "P''";
     "P''" ::= HIDE ["but"; "liq"] IN "P_AUX"].
Abort.

Definition invalid : BehaviourExpressions.
Proof.
  Fail create_behaviour_expressions
    ["Q'" ::= "but";; STOP |[ ["but"] ]| "but";; "Q'"].
Abort.

Definition invalid : BehaviourExpressions.
Proof.
  Fail create_behaviour_expressions
    ["Q_AUX''" ::= "choc";; "Q'";
     "Q'" ::= "liq";; "Q''";
     "Q''" ::= "but";; "Q_AUX''" |[ ["but"] ]| "but";; "Q_AUX''"].
Abort.
