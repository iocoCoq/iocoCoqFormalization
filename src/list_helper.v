Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Lists.ListSet.

(* Equiv definition, notation and tactics *)
Definition Equiv {A : Type} (l1 l2 : list A) := forall x, In x l1 <-> In x l2.
Notation "x [=] y" := (Equiv x y) (at level 50).

Lemma Equiv_sym {A : Type} (x y : list A) : x [=] y -> y [=] x.
Proof.
  intros H k. split; intros H'; apply H; apply H'.
Qed.

Lemma Equiv_trans {A : Type} (x y z : list A) : x [=] y -> y [=] z -> x [=] z.
Proof.
  intros H1 H2 k. split.
  - intros H. apply H2. apply H1. apply H.
  - intros H. apply H1. apply H2. apply H.
Qed.

Lemma Equiv_app {A : Type} (x x' y y' : list A) :
  x [=] x' ->
  y [=] y' ->
  (x ++ y) [=] (x' ++ y').
Proof.
  intros H1 H2 k. split; intros H; apply in_app_iff in H; apply in_app_iff.
  destruct H; [left; apply H1 | right; apply H2]; easy.
  destruct H; [left; apply H1 | right; apply H2]; easy.
Qed.

Lemma Equiv_eqLength :
  forall {A : Type} (x y : list A),
    x [=] y ->
    NoDup x ->
    NoDup y ->
    List.length x = List.length y.
Proof.
  intros A x.
  induction x; intros y H.
  - destruct y; auto.
    assert (In a []). { apply H. left. reflexivity. } easy.
  - assert (in_y : In a y). { apply H. left. reflexivity. }
    apply in_split in in_y. destruct in_y as [y1 [y2 y_eq]]. rewrite y_eq.
    intros NoDup_x NoDup_y.
    apply NoDup_cons_iff in NoDup_x. destruct NoDup_x as [nin_a_x NoDup_x].
    apply NoDup_remove in NoDup_y. destruct NoDup_y as [NoDup_y nin_a_y].
    rewrite y_eq in H.
    assert (x_equiv : x [=] (y1 ++ y2)).
    { intros k. split.
      - intros H'. assert (H'' : In k (a :: x)). { right. auto. }
        apply H in H''. apply in_app_iff in H''. apply in_app_iff.
        repeat destruct H'' as [H'' | H'']; auto.
        subst. easy.
      - intros H'.
        assert (H'' : In k (y1 ++ a :: y2)).
        { apply in_app_iff in H'. apply in_app_iff. destruct H'; auto.
          right. right. auto. }
        apply H in H''. destruct H'' as [H'' | H'']; auto. subst. easy. }
    rewrite app_length. simpl. rewrite <- plus_n_Sm. apply f_equal.
    rewrite <- app_length. apply IHx; auto.
Qed.

Section Equivb.
  Variable A : Type.
  Hypothesis Aeq_dec : forall (x y : A), {x = y} + {x <> y}.

  Definition equivb (l1 l2 : list A) : bool :=
    andb
      (forallb (fun x => set_mem Aeq_dec x l2) l1)
      (forallb (fun x => set_mem Aeq_dec x l1) l2).

  Lemma equivb_Equiv : forall (l1 l2 : list A),
    l1 [=] l2 <-> equivb l1 l2 = true.
  Proof.
    intros l1 l2. split.
    - intros H. unfold Equiv in H. apply andb_true_intro. split;
      apply forallb_forall; intros x H'; apply H in H'; apply set_mem_correct2;
      apply H'.
    - intros H. unfold equivb in H. apply andb_prop in H. destruct H as [H H'].
      unfold Equiv. intros x. split; intro H'';
      [ eapply forallb_forall in H | eapply forallb_forall in H']; try (apply H'');
      eapply set_mem_correct1; [ apply H | apply H' ].
Qed.

End Equivb.

Lemma Equiv_dec:
  forall {A : Type} (l1 l2: list A),
    (forall (x y : A), { x = y } + { x <> y}) ->
    { l1 [=] l2} + {~ (l1 [=] l2) }.
Proof.
  intros A l1 l2 Aeq_dec. pose proof (equivb_Equiv A Aeq_dec l1 l2).
  apply Bool.iff_reflect in H. destruct H as [H | H]; auto.
Qed.

Ltac symmetry_eqv_H H := apply Equiv_sym in H.
Ltac symmetry_eqv_goal := apply Equiv_sym.

Tactic Notation "symmetry_eqv" := symmetry_eqv_goal.
Tactic Notation "symmetry_eqv" "in" constr(x) := symmetry_eqv_H x.

Ltac rewrite_eqv_H H1 H2 :=
  (eapply Equiv_trans in H2; [| symmetry_eqv in H1; apply H1] ||
   symmetry_eqv in H2; eapply Equiv_trans in H2;
   [| symmetry_eqv in H1; apply H1]; symmetry_eqv in H2).

Ltac rewrite_eqv_goal H :=
  eapply Equiv_trans; [| symmetry_eqv in H; apply H].

Tactic Notation "rewrite_eqv" constr(H1) "in" constr(H2) :=
  rewrite_eqv_H H1 H2.

Tactic Notation "rewrite_eqv" "<-" constr(H1) "in" constr(H2) :=
  symmetry_eqv in H1; rewrite_eqv_H H1 H2; symmetry_eqv in H1.

Tactic Notation "rewrite_eqv" constr(H) :=
  rewrite_eqv_goal H.

Tactic Notation "rewrite_eqv" "<-" constr(H) :=
  symmetry_eqv in H; rewrite_eqv_goal H; symmetry_eqv in H.

(* custom version for set_diff *)
Fixpoint set_diff' {A : Type} (A_dec : forall a b, {a = b} + {a <> b})
  (x y : set A) : set A :=
  match x with
  | nil => nil
  | a1 :: x1 =>
    if set_mem A_dec a1 y
    then set_diff' A_dec x1 y
    else a1 :: (set_diff' A_dec x1 y)
  end.

(* set_diff' facts:
   There are all the original set_diff facts.
   The exception is set_diff'_nodup, which here has a "stronger" version *)
Lemma set_diff'_intro :
  forall {A: Type} (A_dec: forall a b, {a = b} + {a <> b}) (a : A) (x y: set A),
    In a x -> ~ set_In a y -> set_In a (set_diff' A_dec x y).
Proof.
  intros A A_dec a x y H H'. induction x.
  - inversion H.
  - simpl in H. destruct H.
    + subst. simpl. eapply set_mem_complete2 in H'. rewrite H'. left. trivial.
    + simpl. apply set_mem_ind.
      * intros _. auto.
      * simpl. right. auto.
Qed.

Lemma set_diff'_elim1 :
  forall {A : Type} (A_dec: forall a b, {a = b} + {a <> b}) (x y:set A) (a : A),
    In a (set_diff' A_dec x y) -> In a x.
Proof.
  intros A A_dec x y a H. induction x.
  - inversion H.
  - simpl in H. destruct (set_mem A_dec a0 y).
    + right. apply IHx. apply H.
    + destruct H.
      * left. trivial.
      * right. auto.
Qed.

Lemma set_diff'_elim2 :
  forall {A : Type} (A_dec: forall a b, {a = b} + {a <> b}) (x y: set A) (a: A),
    set_In a (set_diff' A_dec x y) -> ~ set_In a y.
Proof.
  intros A A_dec x y a H. induction x.
  - inversion H.
  - simpl in H. destruct (set_mem A_dec a0 y) eqn:H'.
    + auto.
    + apply set_mem_complete1 in H'. simpl in H. destruct H; subst; auto.
Qed.

Lemma set_diff'_iff :
  forall {A : Type} (A_dec: forall a b, {a = b} + {a <> b}) (x y: set A) (a: A),
    In a (set_diff' A_dec x y) <-> In a x /\ ~ In a y.
Proof.
  intros A A_dec x y a. split.
  - intros H. split.
    + apply set_diff'_elim1 in H. apply H.
    + apply set_diff'_elim2 in H. apply H.
  - intros H. destruct H as [H H']. induction x.
    + inversion H.
    + destruct H.
      * subst. eapply set_mem_complete2 in H'. simpl. rewrite H'. left. trivial.
      * simpl. apply set_mem_ind; auto. right. auto.
Qed.

Lemma set_diff'_nodup :
  forall {A : Type} (A_dec: forall a b, {a = b} + {a <> b}) (x y: set A),
    NoDup x -> NoDup (set_diff' A_dec x y).
Proof.
  intros A A_dec x y H. induction x.
  - apply NoDup_nil.
  - simpl. apply set_mem_ind.
    + inversion H. auto.
    + inversion H. apply NoDup_cons.
      * intro H'. apply set_diff'_elim1 in H'. easy.
      * auto.
Qed.

Lemma set_diff'_trivial :
  forall {A : Type} (A_dec: forall a b, {a = b} + {a <> b}) (a: A) (x: set A),
    ~ set_In a (set_diff' A_dec x x).
Proof.
  intros A A_dec a x. intros H.
  assert (H' : In a (set_diff' A_dec x x)). { trivial. }
  apply set_diff'_elim1 in H. apply set_diff'_elim2 in H'. easy.
Qed.

Lemma set_diff'_app :
  forall {A : Type} {A_dec : forall x y, {x = y} + {x <> y}} (x y : set A),
    set_diff' A_dec (x ++ y) y = set_diff' A_dec x y.
Proof.
  intros A A_dec x y. induction x.
  - simpl. remember y as y' eqn:Hy.
    assert (H:set_diff' A_dec y' y' = set_diff' A_dec y' y). { subst. trivial. }
    assert (In_y' : forall x, In x y' -> In x y). { subst. trivial. }
    rewrite H. clear H Hy. induction y'; trivial. simpl. apply set_mem_ind2.
    + intros _. apply IHy'. intros x H. apply In_y'. right. apply H.
    + intros In_y. elim In_y. apply In_y'. left. trivial.
  - simpl. destruct (set_mem A_dec a y).
    + apply IHx.
    + rewrite IHx. trivial.
Qed.

Lemma set_diff'_subset :
  forall {A : Type} (A_dec : forall x y, {x = y} + {x <> y}) (x y : set A)
    (a :  A),
    (In a y -> In a x) ->
    In a x <-> In a (set_diff' A_dec x y) \/ In a y.
Proof.
  intros A A_dec x y a H. split.
  - intros H'. destruct (In_dec A_dec a y).
   + right. apply i.
   + left. apply set_diff'_intro; auto.
  - intros H'. destruct H' as [H' | H'].
    + apply set_diff'_elim1 in H'. apply H'.
    + auto.
Qed.

Lemma set_diff'_eqv :
  forall {A : Type} (A_dec : forall x y, {x = y} + {x <> y}) (x y z : set A),
  x [=] y ->
  set_diff' A_dec x z [=] set_diff' A_dec y z.
Proof.
  intros A A_dec x y z H. intros k. split;
  intros H'; apply set_diff'_iff in H'; destruct H' as [H' H''];
  apply set_diff'_iff; split; auto; apply H; auto.
Qed.

(* partition extra facts *)
Lemma partition_intro1 :
  forall {A : Type} (a : A) (l : list A) (f : A -> bool),
    In a l -> f a = false -> In a (snd (partition f l)).
Proof.
  intros. induction l.
  - inversion H.
  - destruct H as [H | H].
    + subst. destruct (partition f l) eqn:H'. erewrite partition_cons2; auto.
      * simpl. left. reflexivity.
      * rewrite H'. reflexivity.
    + simpl. destruct (partition f l); destruct (f a0); simpl; try right;
      simpl in IHl; apply IHl; apply H.
Qed.

Lemma partition_elim1 :
  forall {A : Type} (a : A) (l : list A) (f : A -> bool),
    In a (snd (partition f l)) -> In a l /\ f a = false.
Proof.
  intros. induction l.
  - inversion H.
  - simpl in H. destruct (partition f l) eqn:H'. destruct (f a0) eqn:H''.
    + simpl in H. apply IHl in H. destruct H. split; auto. right. apply H.
    + simpl in H. destruct H.
      * subst. split; auto. left. reflexivity.
      * apply IHl in H. destruct H. split; auto. right. apply H.
Qed.

Lemma partition_intro2 :
  forall {A : Type} (a : A) (l : list A) (f : A -> bool),
    In a l -> f a = true -> In a (fst (partition f l)).
Proof.
  intros. induction l.
  - inversion H.
  - destruct H as [H | H].
    + subst. destruct (partition f l) eqn:H'. erewrite partition_cons1; auto.
      * simpl. left. reflexivity.
      * rewrite H'. reflexivity.
    + simpl. destruct (partition f l); destruct (f a0); simpl; try right;
      simpl in IHl; apply IHl; apply H.
Qed.

Lemma partition_elim2 :
  forall {A : Type} (a : A) (l : list A) (f : A -> bool),
    In a (fst (partition f l)) -> In a l /\ f a = true.
Proof.
  intros. induction l.
  - inversion H.
  - simpl in H. destruct (partition f l) eqn:H'. destruct (f a0) eqn:H''.
    + simpl in H. destruct H.
      * subst. split; auto. left. reflexivity.
      * apply IHl in H. destruct H. split; auto. right. apply H.
    + simpl in H. apply IHl in H. destruct H. split; auto. right. apply H.
Qed.

(* NoDup extra facts*)
Lemma NoDup_dec :
  forall {A : Type} (l : list A),
  (forall a1 a2 : A, { a1 = a2 } + { a1 <> a2 }) ->
   { NoDup l } + { ~ NoDup l }.
Proof.
  intros A l Aeq_dec. induction l as [| h l' H].
  - left. apply NoDup_nil.
  - inversion H.
    + pose proof (in_dec Aeq_dec h l') as H'. inversion H'.
      * right. intros H''. inversion H''. auto.
      * left. apply NoDup_cons; auto.
    + right. intros H'. inversion H'. auto.
Qed.

Lemma NoDup_app :
  forall {A : Type} (l1 l2 : list A),
    NoDup (l1 ++ l2) <->
    NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> ~ In x l2).
Proof.
  split.
  - generalize dependent l2. induction l1.
    + intros. split; auto. apply NoDup_nil.
    + intros l2 H. inversion H. apply IHl1 in H3.
      destruct H3 as [NoDup_l1 [NoDup_l2 NoDup_inter]].
      repeat split; trivial.
      * apply NoDup_cons; trivial. unfold not. intros In_l1. elim H2.
        apply in_or_app. left. apply In_l1.
      * intros x' In_a_l1. destruct In_a_l1 as [x'_a | In_l1]; auto.
        subst. unfold not. intros In_l2. elim H2. apply in_or_app. right.
        apply In_l2.
  - generalize dependent l2. induction l1.
    + intros l2 H. destruct H as [_ [NoDup_l2 _]]. apply NoDup_l2.
    + intros l2 H. destruct H as [NoDup_a_l1 [NoDup_l2 NoDup_inter]].
      rewrite <- app_comm_cons. apply NoDup_cons.
      * unfold not. intros In_app. apply in_app_or in In_app.
        destruct In_app as [In_l1 | In_l2].
        { inversion NoDup_a_l1. auto. }
        { apply NoDup_inter with (x := a); auto. left. trivial. }
      * apply IHl1. inversion NoDup_a_l1. repeat split; auto. intros x' In_l1.
        apply NoDup_inter. right. apply In_l1.
Qed.

Lemma NoDup_partition :
  forall {A : Type} (l : list A) (f : A -> bool),
    NoDup l <-> NoDup (fst (partition f l)) /\ NoDup (snd (partition f l)).
Proof.
  split.
  - induction l.
    + intros H. split; apply NoDup_nil.
    + simpl. intros H. destruct (partition f l) eqn:Hp. simpl in IHl.
      inversion H. apply IHl in H3. destruct H3 as [Hl0 Hl1];
      apply elements_in_partition with (x := a) in Hp. destruct (f a);
      simpl; split; auto; apply NoDup_cons; auto; unfold not; intros H';
      elim H2; apply Hp; [left | right]; auto.
  - induction l.
    + intros H. apply NoDup_nil.
    + simpl. destruct (partition f l) eqn:Hp. destruct (f a) eqn:Hf; simpl in *;
      intros H; destruct H as [Hl0 Hl1]; [inversion Hl0 | inversion Hl1];
      apply NoDup_cons; try (apply IHl; split; auto); unfold not; intros H';
      elim H1.
      * assert (l0_eq : l0 = fst (partition f l)). { rewrite Hp. trivial. }
        rewrite l0_eq. apply partition_intro2; auto.
      * assert (l1_eq : l1 = snd (partition f l)). { rewrite Hp. trivial. }
        rewrite l1_eq. apply partition_intro1; auto.
Qed.

Lemma NoDup_app2 :
  forall {A : Type} (x y : set A),
    NoDup (y ++ x) -> NoDup (x ++ y).
Proof.
  intros A x. induction x.
  - intros y. simpl. rewrite app_nil_r. auto.
  - intros y H. apply NoDup_remove in H. destruct H. simpl. apply NoDup_cons.
    + intros H'. apply in_app_iff in H'. elim H0. apply in_app_iff.
      destruct H'; auto.
    + apply IHx. apply H.
Qed.

(* set_add extra facts*)
Lemma set_add_elim3 :
  forall {A : Type} (A_dec : forall x y, {x = y} + {x <> y}) (a: A) (x : set A),
    ~ In a x ->
    set_add A_dec a x = x ++ [a].
Proof.
  intros A A_dec a x H.
  induction x; trivial.
  simpl. destruct A_dec.
  - elim H. subst. left. trivial.
  - apply f_equal. apply IHx. intros H'. elim H. right. trivial.
Qed.

Lemma set_add_elim4 :
  forall {A : Type} (A_dec : forall x y, {x = y} + {x <> y}) (a: A) (x : set A),
    In a x ->
    set_add A_dec a x = x.
Proof.
  intros A A_dec a x H.
  induction x.
  - inversion H.
  - destruct H.
    + subst. simpl. destruct A_dec; easy.
    + simpl. destruct A_dec; trivial. apply f_equal. apply IHx; auto.
Qed.

(* set_union extra facts*)
Lemma set_union_elim2 :
  forall {A : Type} (A_dec : forall x y, {x = y} + {x <> y}) (x y : set A),
    exists z,
      set_union A_dec x y = x ++ z /\
      (forall k, In k z <-> In k y /\ ~ In k x)  /\
      NoDup z.
Proof.
  intros A A_dec x y. induction y;
  [exists []; rewrite app_nil_r; split; [| split]; try easy; apply NoDup_nil |].
  simpl. destruct IHy as [z [union_eq [H NoDup_z]]].
  destruct (In_dec A_dec a (set_union A_dec x y)).
  - assert (In_a : In a (set_union A_dec x y)). { auto. }
    apply set_add_elim4 with (A_dec0 := A_dec) in i. rewrite i. exists z.
    split; auto. split; auto.
    intros k. split.
    + intros H'. apply H in H'. destruct H' as [H' H'']. split; auto.
    + intros H'. destruct H' as [H' H'']. destruct H' as [H' | H'].
      * subst. rewrite union_eq in In_a. apply in_app_iff in In_a.
        destruct In_a; easy.
      * apply H. split; auto.
  - assert (In_a : ~ In a (set_union A_dec x y)). { auto. }
    apply set_add_elim3 with (A_dec0 := A_dec) in n. exists (z ++ [a]).
    rewrite n. rewrite union_eq. rewrite app_assoc. split; auto. split.
    intros k. split.
    + intros H'. apply in_app_iff in H'. destruct H' as [H' | H'].
      * apply H in H'. destruct H'; split; auto.
      * destruct H' as [H'|]; [| easy]. split; auto. subst. intros H'.
        elim In_a. apply set_union_intro1. apply H'.
    + intros H'. apply in_app_iff. simpl. destruct H' as [H' H''].
      destruct H' as [H' | H']; auto. left. apply H; auto.
    + assert (H' : ~ In a z).
      { intros F. elim In_a. rewrite union_eq. apply in_app_iff. auto. }
      apply NoDup_app2. simpl. apply NoDup_cons; auto.
Qed.

Lemma set_union_eqLength :
  forall {A : Type} (A_dec : forall x y, {x = y} + {x <> y}) (x y z : list A),
  y [=] z ->
  List.length (set_union A_dec x y) = List.length (set_union A_dec x z).
Proof.
  intros A A_dec x y z H.
  pose proof (set_union_elim2 A_dec x y) as Hy.
  pose proof (set_union_elim2 A_dec x z) as Hz.
  destruct Hy as [y' [y_eq [Hy NoDup_y']]].
  destruct Hz as [z' [z_eq [Hz NoDup_z']]].
  assert (H' : y' [=] z').
  { intros k. split;
    intros H'; [apply Hz; apply Hy in H' | apply Hy; apply Hz in H'];
    destruct H' as [H' H'']; split; auto; apply H; apply H'. }
  apply Equiv_eqLength in H'; auto. rewrite y_eq. rewrite z_eq.
  do 2 rewrite app_length. rewrite H'. trivial.
Qed.

(* existsb extra facts *)
Lemma existsb_false:
  forall (A : Type) (f : A -> bool) (l : list A),
    existsb f l = false <-> ~ exists x : A, In x l /\ f x = true.
Proof.
  intros. split.
  - intros H. pose proof (existsb_exists f l) as H'. apply iff_sym in H'.
    apply Bool.iff_reflect in H'. rewrite H in H'. inversion H'. auto.
  - intros H. pose proof (existsb_exists f l) as H'. apply iff_sym in H'.
    apply Bool.iff_reflect in H'. inversion H'.
    + unfold not in H. destruct H. apply H1.
    + reflexivity.
Qed.
