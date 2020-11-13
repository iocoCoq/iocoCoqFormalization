Require Import BE_semantics.
Require Import BE_syntax.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Lists.ListSet.
Require Import list_helper.

Local Open Scope type_scope.
(* Define a transition from a behaviour state to another using an Event *)
Definition BehaviourTrans := ProcessBehaviour * Event * ProcessBehaviour.
Local Close Scope type_scope.

Definition from (t : BehaviourTrans) := fst (fst t).
Definition to (t : BehaviourTrans) := snd t.
Definition transLabel (t : BehaviourTrans) := snd (fst t).

Definition BehaviourTransSet := set BehaviourTrans.

Theorem BehaviourTransDec :
  forall t1 t2 : BehaviourTrans, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  - apply ProcessBehaviourDec.
  - decide equality.
    + apply EventDec.
    + apply ProcessBehaviourDec.
Defined.

Fixpoint targetBehaviours (T : BehaviourTransSet) : set ProcessBehaviour :=
  match T with
  | nil => nil
  | (_, _, B) :: T' => set_add ProcessBehaviourDec B (targetBehaviours T')
  end.

Fixpoint transFromB (B : ProcessBehaviour) (T : BehaviourTransSet)
    : BehaviourTransSet :=
  match T with
  | nil                => nil
  | (B', e, B'') :: T' => if ProcessBehaviourDec B B'
                          then (B, e, B'') :: transFromB B T'
                          else transFromB B T'
  end.

Lemma transFromB_id :
  forall (B : ProcessBehaviour) (T : BehaviourTransSet),
    (forall t, In t T -> from t = B) ->
    transFromB B T = T.
Proof.
  intros B T H. induction T.
  - reflexivity.
  - simpl. assert (eq_a : from a = B). { apply H. left. trivial. }
    unfold from in eq_a. destruct a, p. simpl in eq_a. symmetry in eq_a.
    destruct (ProcessBehaviourDec B p); [| easy].
    subst. apply f_equal. apply IHT. intros t H'. apply H. right. trivial.
Qed.

Lemma targetBehaviours_NoDup : forall T, NoDup (targetBehaviours T).
Proof.
  induction T.
  - simpl. apply NoDup_nil.
  - simpl. destruct a, p. apply set_add_nodup. apply IHT.
Qed.

Inductive BehaviourTransSetR' : BehaviourExpressions -> BehaviourTransSet ->
    set ProcessBehaviour -> set ProcessBehaviour -> Prop :=
  | behaviour_trans_empty_rule (ctx : BehaviourExpressions)
        (visited : set ProcessBehaviour) :
      BehaviourTransSetR' ctx nil nil visited
  | behaviour_trans_inductive_rule
        (ctx : BehaviourExpressions)
        (T : BehaviourTransSet)
        (B : ProcessBehaviour)
        (Bs visited : set ProcessBehaviour) :
      let T' := transFromB B T in
      let visited' := B :: visited in
      let to_visit := set_union
        ProcessBehaviourDec
        Bs
        (set_diff' ProcessBehaviourDec (targetBehaviours T') visited') in
      let T'' :=
        set_diff' BehaviourTransDec T T' in
      (forall (e : Event) (B' : ProcessBehaviour),
        (ctx # B // e --> B') <-> In (B,e,B') T') ->
      BehaviourTransSetR'
        ctx
        T''
        to_visit
        visited' ->
      BehaviourTransSetR' ctx T (B :: Bs) visited.

Inductive BehaviourTransSetR :
  BehaviourExpressions -> BehaviourTransSet -> ProcessName -> Prop :=
  | behaviour_trans_set (ctx : BehaviourExpressions) (T : BehaviourTransSet)
      (P : ProcessName) (B : ProcessBehaviour) :
      Some B = getProcessBehaviour P ctx ->
      NoDup T ->
      BehaviourTransSetR' ctx T [B] [] ->
      BehaviourTransSetR ctx T P.

Lemma transFromB_from :
  forall (B : ProcessBehaviour) (T : BehaviourTransSet),
    forall x, In x (transFromB B T) -> from x = B.
Proof.
  intros B T x.
  induction T.
  - easy.
  - intros H. simpl in H. destruct a, p. destruct (ProcessBehaviourDec B p);
    auto. destruct H; auto. unfold from. rewrite <- H. trivial.
Qed.

Lemma transFromB_subset :
  forall (B : ProcessBehaviour) (T : BehaviourTransSet),
    forall x, In x (transFromB B T) -> In x T.
Proof.
  intros.
  induction T; trivial.
  simpl. simpl in H. destruct a, p.
  destruct (ProcessBehaviourDec B p).
  - simpl in H. destruct H; subst.
    + left. reflexivity.
    + right. apply IHT. apply H.
  - right. apply IHT. apply H.
Qed.

Lemma transFromBNotEmpty :
  forall (B : ProcessBehaviour) (T : BehaviourTransSet),
    (transFromB B T) <> [] ->
    exists (e : Event) (B' : ProcessBehaviour), In (B, e, B') T.
Proof.
  intros.
  induction T.
  - simpl in H. easy.
  - simpl in H. simpl. destruct a, p. destruct (ProcessBehaviourDec B p).
    + exists e, p0. destruct e0. left. reflexivity.
    + apply IHT in H. destruct H as [e' [B']]. exists e', B'. right. apply H.
Qed.
