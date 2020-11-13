Require Import Coq.Lists.List.
Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.
Require Import BE_trans_set.
Require Import BE_semantics.

Ltac elem_in_list :=
  simpl; repeat (try (left; reflexivity); right); fail 0 "Unable to find elem".

Ltac expand_In H := repeat (destruct H as [H | H]); inversion H.

Ltac list_has_no_dup_with_error f :=
  apply NoDup_nil ||
  let H := fresh "H" in
    apply NoDup_cons;
      [ unfold not; intros H; expand_In H;
        match type of H with
        | ?x = _ => f x
        end |
        list_has_no_dup_with_error f ].

Ltac list_has_no_dup :=
  list_has_no_dup_with_error ltac:(fun x => fail 0 x "is a duplicate in list").

Ltac create_behaviour_expressions expressions :=
  refine (mkBehaviourExpressions expressions _ _ _ _);
  [ list_has_no_dup_with_error
    ltac:(fun x => fail 0 "The process" x "is defined twice") |

    simpl; repeat split; (elem_in_list ||
      match goal with
      | |- _ = ?x \/ _ => fail 0 "Invalid reference to" x
      end) |

    let H := fresh "H" in
    repeat (apply Forall_cons; [unfold not; intros H; inversion H | ]);
    (apply Forall_nil || fail 0 "Invalid process name") |

    let H := fresh "H" in
    intros; unfold not; intros H; expand_In H; subst; inversion H;
    match type of H with
    | (?P, _, _) = _ => fail 0 "Invalid recursion in" P
    end ].

(* For a given behaviour B this proves:
  forall e, B'
    (ctx # B // e --> B') -> In (B, e, B') T',
  where H is (ctx # B // e --> B')
        f is the fail function for the cases where the transation is not in T'
*)
Ltac transation_set_complete H f :=
  match type of H with
  | _ # _ ;; _ // _ --> _ => inversion H; (elem_in_list || f ())
  | _ # Choice _ // _ --> _ =>
    let Hbs' := fresh "Hbs'" in
    let H' := fresh "H'" in
      inversion H as [|? ? ? ? ? Hbs' H'| | | | | | | | | ];
      repeat (destruct Hbs' as [Hbs' | Hbs'];
              [subst; transation_set_complete H' f | try contradiction Hbs'])
  | _ # STOP // _ --> _ =>
    let Hbs' := fresh "Hbs'" in
      inversion H as [|? ? ? ? ? Hbs' ?| | | | | | | | | ];
      (contradiction Hbs' || f ())
  | _ # HIDE _ IN _ // I --> _ =>
    let H' := fresh "H'" in
    let Ih := fresh "Ih" in
      inversion H as
        [| | | | | | | ? ? ? ? ? Ih H' | | ? ? ? ? H' |];
      [ transation_set_complete H'
          ltac:(fun _ => (subst; expand_In Ih) || f () ) |
        transation_set_complete H' f ]
  | _ # HIDE _ IN _ // _ --> _ =>
    let H' := fresh "H'" in
    let Ih := fresh "Ih" in
      inversion H as
        [| | | | | | | ? ? ? ? ? Ih H' | ? ? ? ? ? Ih H' | ? ? ? ? H' |];
      [ transation_set_complete H'
          ltac:(fun _ => (subst; expand_In Ih) || f ()) |
        transation_set_complete H'
          ltac:(fun _ => (subst; elim Ih; elem_in_list) || f ()) |
        transation_set_complete H' f ]
  | _ # HIDE _ IN _ // _ --> _ =>
    let H' := fresh "H'" in
    let Ih := fresh "Ih" in
      inversion H as
        [| | | | | | | | ? ? ? ? ? Ih H' | |];
      transation_set_complete H'
        ltac:(fun _ => (subst; elim Ih; elem_in_list) || f ())
  | _ # _ |[ _ ]| _ // I --> _ =>
    let H' := fresh "H'" in
      inversion H as [| | | |? ? ? ? ? H'|? ? ? ? ? H'| | | | |];
      transation_set_complete H' f
  | _ # _ |[ _ ]| _ // _ --> _ =>
    let H' := fresh "H'" in
    let H'' := fresh "H''" in
    let Ih := fresh "Ih" in
      inversion H as [| |
          ? ? ? ? ? ? Ih H' |
          ? ? ? ? ? ? Ih H'|
          ? ? ? ? ? H'|
          ? ? ? ? ? H'|
          ? ? ? ? ? ? ? Ih H' H''|
          | | |];
      [ transation_set_complete H'
          ltac:(fun _ => (subst; elim Ih; elem_in_list) || f ()) |
        transation_set_complete H'
          ltac:(fun _ => (subst; elim Ih; elem_in_list) || f ()) |
        transation_set_complete H' f |
        transation_set_complete H' f |
        transation_set_complete H'
          ltac:(fun _ => (subst; transation_set_complete H''
            ltac:(fun _ => subst; expand_In Ih || f ()) || f ())) ]
  | _ # _ |[ _ ]| _ // _ --> _ =>
    let H' := fresh "H'" in
    let H'' := fresh "H''" in
    let Ih := fresh "Ih" in
      inversion H as [| |
          ? ? ? ? ? ? Ih H' |
          ? ? ? ? ? ? Ih H'| | |
          ? ? ? ? ? ? ? Ih H' H''|
          | | |];
      [ transation_set_complete H'
          ltac:(fun _ => (subst; elim Ih; elem_in_list) || f ()) |
        transation_set_complete H'
          ltac:(fun _ => (subst; elim Ih; elem_in_list) || f ()) |
        transation_set_complete H'
          ltac:(fun _ => (subst; transation_set_complete H''
            ltac:(fun _ => subst; expand_In Ih || f ()) || f ())) ]
  | _ # _ // _ --> _ =>
    let Ih := fresh "Ih" in
      inversion H as [| | | | | | | | | | ? ? ? Ih];
      expand_In Ih;
      (elem_in_list || f ())
  | _ => f ()
  end || fail 0 "Transation set has missing transations".

Ltac try_all l f :=
  match l with
  | nil => fail 0
  | ?b :: ?tl => f b || try_all tl f
  end.

(*
  try to prove a goal of the form:
    ctx # B // e --> B'
  where ctx B, e and B' are valid instances
*)
Ltac transation_set_correct :=
  match goal with
  | |- _ # _;; _ // _ --> _ => apply sos_prefix_rule
  | |- _ # Choice (Values ?Bs) // _ --> _ =>
    try_all Bs
      ltac:(fun b =>
        apply sos_choice_rule with (B := b);
        [elem_in_list | transation_set_correct])
  | |- _ # _ |[ _ ]| ?B2 // _ --> _ |[ _ ]| ?B2 =>
    let H := fresh "H" in
      apply sos_parallel_async_left_rule;
      [unfold not; intros H; expand_In H | transation_set_correct ]
  | |- _ # ?B1 |[ _ ]| _ // _ --> ?B1 |[ _ ]| _ =>
    let H := fresh "H" in
      apply sos_parallel_async_right_rule;
      [unfold not; intros H; expand_In H | transation_set_correct ]
  | |- _ # _ |[ _ ]| ?B2 // I --> _ |[ _ ]| ?B2 =>
    apply sos_parallel_internal_left_rule; transation_set_correct
  | |- _ # ?B1 |[ _ ]| _ // I --> ?B1 |[ _ ]| _ =>
    apply sos_parallel_internal_right_rule; transation_set_correct
  | |- _ # _ |[ _ ]| _ // _ --> _ |[ _ ]| _ =>
    apply sos_parallel_sync_rule;
    [elem_in_list | transation_set_correct | transation_set_correct ]
  | |- _ # HIDE ?G IN _ // I --> _ =>
    try_all G
      ltac:(fun mi =>
        apply sos_hide_in_rule with (a := mi);
        [elem_in_list | transation_set_correct])
  | |- _ # HIDE _ IN _ // _ --> _ =>
    let H := fresh "H" in
      apply sos_hide_not_in_rule;
      [unfold not; intros H; expand_In H | transation_set_correct]
  | |- _ # HIDE _ IN _ // I --> _ =>
    apply sos_hide_internal_rule; transation_set_correct
  | |- _ # _ // _ --> _ =>
    eapply sos_process_instantiation_rule; elem_in_list
  end || fail 0 "This transation is not valid".

Ltac transations_correct_and_complete :=
  let H := fresh "H" in
    intros; simpl; split; intros H;
    [ transation_set_complete H ltac:(fun _ => fail 0) |
      expand_In H; transation_set_correct ].

Ltac behaviour_trans_set_valid :=
  eapply behaviour_trans_set; [ reflexivity | list_has_no_dup | ];
  repeat
    (apply behaviour_trans_inductive_rule;
     [ transations_correct_and_complete | simpl ]);
  apply behaviour_trans_empty_rule.
