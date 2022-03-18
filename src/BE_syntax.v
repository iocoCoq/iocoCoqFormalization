Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import String.

Declare Scope behaviour_exp_scope.

Definition EventName := string.
Definition ProcessName := string.

Inductive Event :=
  | InternalEvent : Event
  | ExternalEvent : EventName -> Event.

Inductive ProcessBehaviour :=
  | Prefix : Event -> ProcessBehaviour -> ProcessBehaviour
  | Choice : ChoiceSet -> ProcessBehaviour
  | Parallel : ProcessBehaviour -> set EventName -> ProcessBehaviour ->
                ProcessBehaviour
  | Hide : ProcessBehaviour -> set EventName -> ProcessBehaviour
  | ProcessInstantiation : ProcessName -> ProcessBehaviour
  with ChoiceSet :=
    | Values : set ProcessBehaviour -> ChoiceSet.

Inductive ProcessDefinition :=
| DefineProcess : ProcessName -> ProcessBehaviour -> ProcessDefinition.

Definition stop := Choice (Values nil).

(* ============================== Syntax facts ============================== *)

Theorem EventDec :
  forall (e1 e2 : Event), {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
  apply string_dec.
Defined.

Theorem ProcessBehaviourDec :
  forall B1 B2 : ProcessBehaviour, {B1 = B2} + {B1 <> B2}
with ChoiceSetDec :
  forall Bs1 Bs2 : ChoiceSet, {Bs1 = Bs2} + {Bs1 <> Bs2}.
Proof.
  - decide equality.
    + apply EventDec.
    + apply (list_eq_dec string_dec).
    + apply (list_eq_dec string_dec).
    + apply string_dec.
  - decide equality. decide equality.
Defined.

(* ============================ Syntax Notations ============================ *)

Module BehaviourExpressionsNotations.
Open Scope behaviour_exp_scope.

Definition string_to_process_instantiation (process_name : string)
    : ProcessBehaviour :=
  ProcessInstantiation process_name.
Coercion string_to_process_instantiation : string >-> ProcessBehaviour.
Coercion ProcessInstantiation : ProcessName >-> ProcessBehaviour.

Definition string_to_external_event(event_name : string): Event :=
  ExternalEvent event_name.
Coercion string_to_external_event : string >-> Event.
Coercion ExternalEvent : EventName >-> Event.

Notation "'STOP'" := stop : behaviour_exp_scope.
Notation "'I'" := InternalEvent : behaviour_exp_scope.
Notation "x ;; y" :=
  (Prefix x y) (at level 55, right associativity) : behaviour_exp_scope.
Notation "x [] y [] .. [] z" :=
  (Choice (Values
    (set_add ProcessBehaviourDec x
      (set_add ProcessBehaviourDec y ..
        (set_add ProcessBehaviourDec z nil) ..))))
   (at level 65, y at next level, no associativity) : behaviour_exp_scope.
Notation "x |[ g ]| y" :=
  (Parallel x g y) (at level 75, right associativity) : behaviour_exp_scope.
Notation "x '|||' y" :=
  (Parallel x nil y) (at level 75, right associativity) : behaviour_exp_scope.
Notation "'HIDE' g 'IN' x" :=
  (Hide x g) (at level 85, right associativity) : behaviour_exp_scope.
Notation "x ::= y" :=
  (DefineProcess x y) (at level 95, no associativity) : behaviour_exp_scope.

End BehaviourExpressionsNotations.

Section BehaviourExpressionsDefinition.
(* ============================ Helper functions ============================ *)
Fixpoint allProcessNames (definitions : list ProcessDefinition) :=
  match definitions with
  | nil => nil
  | (DefineProcess name _) :: tl => name :: (allProcessNames tl)
  end.

Fixpoint allInstancesAreDefined' (names : list ProcessName)
    (B : ProcessBehaviour) : Prop :=
  match B with
  | Prefix _ B' => allInstancesAreDefined' names B'
  | Choice (Values Bs) =>
    (fix expand_choice (l : list ProcessBehaviour) :=
       match l with
       | nil => True
       | B' :: tl => allInstancesAreDefined' names B' /\ expand_choice tl
       end) Bs
  | Parallel B1 _ B2 =>
      allInstancesAreDefined' names B1 /\ allInstancesAreDefined' names B2
  | Hide B' _ => allInstancesAreDefined' names B'
  | ProcessInstantiation P => In P names
  end.

Fixpoint allInstancesAreDefined
    (names : list ProcessName) (definitions : list ProcessDefinition) : Prop :=
match definitions with
| nil => True
| (DefineProcess _ B) :: tl =>
    allInstancesAreDefined' names B /\ allInstancesAreDefined names tl
end.

Local Open Scope type_scope.
Definition ProcessInstance := bool * ProcessName.
Definition ProcessInstanceConnection := ProcessName * bool * ProcessName.
Local Close Scope type_scope.

Lemma ProcessInstance_dec :
  forall (p1 p2 : ProcessInstance), {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
  - apply string_dec.
  - apply Bool.bool_dec.
Defined.

Lemma ProcessInstanceConnection_dec :
  forall (p1 p2 : ProcessInstanceConnection), {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
  - apply string_dec.
  - decide equality.
    + apply Bool.bool_dec.
    + apply string_dec.
Defined.

Fixpoint allProcessInstances (can_recur : bool) (B : ProcessBehaviour)
    : set ProcessInstance :=
  match B with
  | Prefix _ B' => allProcessInstances can_recur B'
  | Choice (Values Bs) =>
    (fix expand_choice (l : list ProcessBehaviour) :=
       match l with
       | nil => nil
       | B' :: tl => set_union
                       ProcessInstance_dec
                       (allProcessInstances can_recur B')
                       (expand_choice tl)
       end) Bs
  | Parallel B1 _ B2 => set_union
                          ProcessInstance_dec
                          (allProcessInstances false B1)
                          (allProcessInstances false B2)
  | Hide B' _ => allProcessInstances false B'
  | ProcessInstantiation P => [(can_recur, P)]
  end.

Fixpoint allProcessInstancesConnections (defs : list ProcessDefinition)
    : set ProcessInstanceConnection :=
  match defs with
  | nil => nil
  | (DefineProcess P B) :: tl =>
      map (fun p => (P, fst p, snd p)) (allProcessInstances true B)
      ++
      allProcessInstancesConnections tl
  end.

Fixpoint expandConnectionsFromStart (start : set ProcessInstanceConnection)
  (cur : ProcessInstanceConnection) :=
  match cur, start with
  | _, nil => [cur]
  | (P1, can_recur, P2), (P3, can_recur', P4) :: tl =>
    let new_tl := expandConnectionsFromStart tl cur in
    if string_dec P2 P3
    then set_add
           ProcessInstanceConnection_dec
           (P1, andb can_recur can_recur', P4)
           new_tl
    else new_tl
  end.

Definition connProd (a b : set ProcessInstanceConnection) :=
  fold_right
    (set_union ProcessInstanceConnection_dec)
    nil
    (map (expandConnectionsFromStart a) b).

Fixpoint apply_f_n_times {A : Type} (n : nat) (f : A -> A) (a : A) :=
  match n with
    | 0    => a
    | S n' => f (apply_f_n_times n' f a)
  end.

Definition allConnectedPairs (defs : list ProcessDefinition) :=
  let start_connections := allProcessInstancesConnections defs in
  let iterations := S (Nat.log2 (List.length defs)) in
    apply_f_n_times iterations (fun x => connProd x x) start_connections.

Definition allConnectedPairs2 (defs : list ProcessDefinition) :=
  let start_connections := allProcessInstancesConnections defs in
  let iterations := List.length defs in
    apply_f_n_times iterations (connProd start_connections) start_connections.

(* ==================== BehaviourExpressions definition ===================== *)
Local Open Scope type_scope.
Record BehaviourExpressions : Type := mkBehaviourExpressions {
    definitions : list ProcessDefinition
  ; well_formed_unique_process_names : NoDup (allProcessNames definitions)
  ; well_formed_instances_defined : allInstancesAreDefined
                                      (allProcessNames definitions)
                                      definitions
  ; well_formed_process_names : Forall (fun s => s <> EmptyString)
                                       (allProcessNames definitions)
  ; well_formed_only_allowed_recursions : forall (P : ProcessName),
      ~ In (P, false, P) (allConnectedPairs definitions)
}.
Local Close Scope type_scope.

Fixpoint getProcessBehaviour' (P : ProcessName) (def : list ProcessDefinition)
    : option ProcessBehaviour :=
  match def with
  | nil => None
  | (DefineProcess P' B) :: def' => if eqb P P'
                                    then Some B
                                    else getProcessBehaviour' P def'
  end.

Definition getProcessBehaviour (P : ProcessName) (ctx : BehaviourExpressions)
  := getProcessBehaviour' P ctx.(definitions).


(* ==================== BehaviourExpressions Facts ========================== *)

Lemma allProcessNames_app:
  forall (l l' : list ProcessDefinition),
    allProcessNames (l ++ l') = allProcessNames l ++ allProcessNames l'.
Proof.
  induction l.
  - reflexivity.
  - intros. simpl. destruct a. rewrite IHl. apply app_comm_cons.
Qed.

Lemma getProcessBehaviour_in :
  forall (P : ProcessName) (ctx : BehaviourExpressions) (B : ProcessBehaviour),
    In (DefineProcess P B) ctx.(definitions) <->
    Some B = getProcessBehaviour P ctx.
Proof.
  split.
  - intros. pose proof ctx.(well_formed_unique_process_names).
    apply in_split in H. destruct H as [p [s]]. rewrite H in H0.
    unfold getProcessBehaviour. rewrite H. clear H. induction p.
    + simpl. rewrite eqb_refl. reflexivity.
    + simpl. destruct a. rewrite allProcessNames_app in H0.
      destruct (P =? p0)%string eqn:H'.
      * apply eqb_eq in H'. subst. simpl in H0. inversion H0. elim H2.
        apply in_or_app. right. left. reflexivity.
      * clear H'. apply IHp. rewrite allProcessNames_app. simpl in H0.
        inversion H0. simpl. apply H3.
  - intros. unfold getProcessBehaviour in H.
    induction (definitions ctx).
    + inversion H.
    + simpl in H. destruct a. destruct ((P =? p)%string) eqn:H'.
      * inversion H. apply eqb_eq in H'. subst. left. trivial.
      * right. apply IHl. apply H.
Qed.
End BehaviourExpressionsDefinition.

