Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Reserved Notation "ctx # p '//' e '-->' q" (at level 99).
Inductive sosR : BehaviourExpressions -> ProcessBehaviour -> Event ->
    ProcessBehaviour -> Prop :=
  | sos_prefix_rule (ctx : BehaviourExpressions) (a : Event) 
        (B : ProcessBehaviour) :
      ctx # a;; B // a --> B
  | sos_choice_rule (ctx : BehaviourExpressions) (mi : Event)
        (B B' : ProcessBehaviour) (Bs : set ProcessBehaviour) :
      In B Bs ->
      (ctx # B // mi --> B') ->
      ctx # (Choice (Values Bs)) // mi --> B'
  | sos_parallel_async_left_rule (ctx : BehaviourExpressions) (mi : EventName)
        (B1 B2 B1' : ProcessBehaviour) (G : set EventName) :
      ~ In mi G ->
      (ctx # B1 // mi --> B1') ->
      ctx # (B1 |[ G ]| B2) // mi --> (B1' |[ G ]| B2)
  | sos_parallel_async_right_rule (ctx : BehaviourExpressions) (mi : EventName)
        (B1 B2 B2' : ProcessBehaviour) (G : set EventName) :
      ~ In mi G ->
      (ctx # B2 // mi --> B2') ->
      ctx # (B1 |[ G ]| B2) // mi --> (B1 |[ G ]| B2')
  | sos_parallel_internal_left_rule (ctx : BehaviourExpressions)
        (B1 B2 B1' : ProcessBehaviour) (G : set EventName) :
      (ctx # B1 // I --> B1') ->
      ctx # (B1 |[ G ]| B2) // I --> (B1' |[ G ]| B2)
  | sos_parallel_internal_right_rule (ctx : BehaviourExpressions)
        (B1 B2 B2' : ProcessBehaviour) (G : set EventName) :
      (ctx # B2 // I --> B2') ->
      ctx # (B1 |[ G ]| B2) // I --> (B1 |[ G ]| B2')
  | sos_parallel_sync_rule (ctx : BehaviourExpressions) (mi : EventName)
        (B1 B2 B1' B2' : ProcessBehaviour) (G : set EventName) :
      In mi G ->
      (ctx # B1 // mi --> B1') ->
      (ctx # B2 // mi --> B2') ->
      ctx # (B1 |[ G ]| B2) // mi --> (B1' |[ G ]| B2')
  | sos_hide_in_rule (ctx : BehaviourExpressions) (a : EventName)
        (B B' : ProcessBehaviour) (G : set EventName) :
      In a G ->
      (ctx # B // a --> B') ->
      ctx # (HIDE G IN B) // I --> (HIDE G IN B')
  | sos_hide_not_in_rule (ctx : BehaviourExpressions) (mi : EventName)
        (B B' : ProcessBehaviour) (G : set EventName) :
      ~ In mi G ->
      (ctx # B // mi --> B') ->
      ctx # (HIDE G IN B) // mi --> (HIDE G IN B')
  | sos_hide_internal_rule (ctx : BehaviourExpressions)
        (B B' : ProcessBehaviour) (G : set EventName) :
      (ctx # B // I --> B') ->
      ctx # (HIDE G IN B) // I --> (HIDE G IN B')
  | sos_process_instantiation_rule (ctx : BehaviourExpressions)
         (P : ProcessName) (B : ProcessBehaviour) :
      In (P ::= B) ctx.(definitions) ->
      ctx # P // I --> B
  where "ctx # p '//' e '-->' q" := (sosR ctx p e q).

Reserved Notation "ctx # p '///' e '-->' q" (at level 99).
Inductive sosStarR : BehaviourExpressions -> ProcessBehaviour ->
    list Event -> ProcessBehaviour -> Prop :=
  | sos_star_reflexivity_rule (ctx : BehaviourExpressions)
        (B : ProcessBehaviour) :
      ctx # B /// nil --> B
  | sos_star_transitive_rule (ctx : BehaviourExpressions) (a : Event)
        (B1 B2 B3 : ProcessBehaviour) (t : list Event) :
      (ctx # B1 // a --> B2) -> (ctx # B2 /// t --> B3) ->
      ctx # B1 /// (a :: t) --> B3
  where "ctx # p '///' e '-->' q" := (sosStarR ctx p e q).

Inductive traceR:
    BehaviourExpressions -> list Event -> ProcessName -> Prop :=
  | trace_rule (ctx : BehaviourExpressions) (t : list Event)
      (P : ProcessName) (B B' : ProcessBehaviour) :
    Some B = getProcessBehaviour P ctx -> sosStarR ctx B t B' -> traceR ctx t P.
