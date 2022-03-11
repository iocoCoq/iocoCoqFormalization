Require Import BE_ltacs.
Require Import String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import LTS.

Local Open Scope string.

Definition fig2_r : LTS.
Proof.
  solve_LTS_rules
          [0;1;2;3;4;5]
          ["but";"liq";"choc"]
          [(0, event "but",1);(1,event "liq",3);
            (0, event "but",2);(2, event "but",4);(4, event "choc",5)]
          0.
Defined.

Local Close Scope string.