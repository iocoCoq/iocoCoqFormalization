Require Import Coq.Lists.List.
Require Import BE_syntax.
Import BE_syntax.BehaviourExpressionsNotations.
Require Import BE_trans_set.
Import Coq.Lists.List.ListNotations.
Require Import BE_semantics.
Require Import IOTS.
Require Import LTS.
(* -------------------- List_ltacs --------------------*)

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

Ltac disjoint_sets :=
  unfold is_disjoint;
  repeat (apply Forall_cons; [ unfold not; intros H; expand_In H; fail |]);
  (apply Forall_nil + fail "Sets not disjoint").

Ltac proof_Equiv := 
  unfold list_helper.Equiv; intros x; split; intros H; expand_In H; elem_in_list.

(* -------------------- LTS_ltacs --------------------*)

Ltac solve_transition_valid :=
  repeat split; elem_in_list.

Ltac solve_list_not_empty :=
  unfold not ; intros H ; inversion H.

Ltac solve_LTS_rules Q L T q0 := apply (mkLTS Q L T q0) ;
  repeat (
    match goal with
    | |- In _ _ => elem_in_list
    | |- _ <> nil => solve_list_not_empty
    | |- each_transition_is_valid _ _ _ => solve_transition_valid
    | |- NoDup _ => list_has_no_dup
    end
  ) ; fail "One or more contextual rules were not fulfilled".

Ltac proof_ind_init_fst_branch_loop ls H :=
match ls with
| ?h :: ?t  =>  inversion H as [A|A];
                [subst; exists h; elem_in_list |];
                clear H; rename A into H;
                proof_ind_init_fst_branch_loop t H
| _ =>  inversion H
end.

Ltac proof_ind_init_fst_branch ls :=
  intros H;
  proof_ind_init_fst_branch_loop ls H.

Ltac proof_ind_init_snd_branch :=
  intros H;
  destruct H;
  repeat(inversion H as [A|A];
         [ inversion A; elem_in_list |];
         clear H; rename A into H); inversion H.

Ltac proof_ind_init ls :=
  try apply init_LTS_r1;
  apply init_r1;
  split;
  [proof_ind_init_fst_branch ls
  |proof_ind_init_snd_branch  ].

Ltac expand_transition _Ht :=
  let s := fresh "s" in
  let s' := fresh "s'" in
  let l := fresh "l" in
  let p := fresh "p" in
  let H := fresh "H" in
    inversion _Ht as [ s s' l p H | s s' p H]; expand_In H.

Ltac expand_empty_reachability H :=
  let H1 := fresh "H'" in
  let H2 := fresh "H'" in
    inversion H as [ | ? ? ? ? H1 H2];
    [| expand_transition H1; expand_empty_reachability H2]; subst.

Ltac expand_one_step_reachability H :=
  let H_empty1 := fresh "H_empty1" in
  let H_trans := fresh "H_trans" in
  let H_empty2 := fresh "H_empty2" in
    inversion H as [? ? ? ? ? ? H_empty1 H_trans H_empty2];
    expand_empty_reachability H_empty1; expand_transition H_trans;
    expand_empty_reachability H_empty2; clear H_empty1 H_trans H_empty2.

Ltac expand_s_seq_reachability H :=
  let H_empty := fresh "H_empty" in
  let H_one_step := fresh "H_one_step" in
  let H_seq := fresh "H_seq" in
  let H_Ts := fresh "H_Ts" in
    match type of H with
    | ind_s_seq_reachability _ [ ] _ _ =>
        inversion H as [ ? ? ? H_empty | |]; expand_empty_reachability H_empty
    | ind_s_seq_reachability _ (s_event _ :: _) _ _ =>
        inversion H as [| ? ? ? ? ? ? H_one_step H_seq |];
        expand_one_step_reachability H_one_step;
        expand_s_seq_reachability H_seq; clear H_seq H_one_step
    | ind_s_seq_reachability _ (delta :: _) _ _ =>
        inversion H as [| | ? ? ? ? H_Ts H_seq ]; expand_In H_Ts;
        expand_s_seq_reachability H_seq; clear H_Ts H_one_step
    | ind_s_seq_reachability _ _ _ _ => idtac
    | _ => fail "Invalid Hypothesis format"
    end.

Ltac expand_out_one_state H x H_In_x_so :=
  let H_In_Ts := fresh "H_In_Ts" in
  let H_neq_In_Ts := fresh "H_neq_In_Ts" in
  let H_neq_In_so := fresh "H_neq_In_so" in
  let H_so := fresh "H_so" in
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
    inversion H as [? ? H_In_Ts | ? ? ? H_neq_In_Ts H_neq_In_so H_so];
    [ expand_In H_In_Ts; clear H_In_Ts; subst; expand_In H_In_x_so |
      (destruct H_neq_In_Ts; elem_in_list) +
      (destruct x; [ | destruct H_neq_In_so; apply H_In_x_so ];
       clear H_neq_In_Ts H_neq_In_so; subst;
       apply H_so in H_In_x_so; destruct H_In_x_so as [? [H1 H2]];
       expand_In H1; subst; expand_transition H2; subst; clear H1 H2)
    ].


Ltac proof_absurd_transition H :=
  expand_transition H; fail "Unable to proof invalid transition".

Ltac proof_absurd_empty_reachability _Haer :=
  let s := fresh "s" in
  let si := fresh "si" in
  let s' := fresh "s'" in
  let p := fresh "p" in
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
    inversion _Haer as [| s si s' p H1 H2]; expand_transition H1;
    subst; proof_absurd_empty_reachability H2.

Ltac proof_absurd_transition_seq _Hts :=
  let s := fresh "s" in
  let s' := fresh "s'" in
  let si := fresh "si" in
  let l1 := fresh "l1" in
  let l2 := fresh "l2" in
  let ll := fresh "ll" in
  let p := fresh "p" in
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
   inversion _Hts as [s s' l1 p H1 | s s' si l1 l2 ll p H1 H2];
   subst; expand_transition H1; subst; proof_absurd_transition_seq H2.

(* ainda nao vi esses ltacs *)

Ltac proof_absurd_different_hyp _Hd :=
  (unfold not in _Hd; exfalso; apply _Hd; reflexivity) + (idtac).

Ltac tr_not_in_list_hyp Hyp :=
  let Hyp' := fresh "Hyp'" in
    repeat(inversion Hyp as [Hyp'|Hyp']; [inversion Hyp'|]; clear Hyp; rename Hyp' into Hyp); inversion Hyp.

Ltac core_transition _Ht3 _Ht4 _Ht5 _Ht6 := 
  repeat(inversion _Ht4 as [_Aux|_Aux];
    [(inversion _Aux; fail) + (subst); tr_not_in_list_hyp _Ht6 |];
   clear _Ht4; rename _Aux into _Ht4); (inversion _Ht4; fail) + (idtac).

Ltac proof_incl H :=
  let aux := fresh "aux" in
    repeat(inversion H as [aux|aux]; [inversion aux; fail |]; clear H; rename aux into Hs).

Ltac proof_incl_goal :=
  simpl; unfold incl; intros Hlabel Hincl; apply Hincl.

Ltac loop_tactics ltac Hyp :=
  let Hyp' := fresh "Hyp'" in
    repeat(
            inversion Hyp as [Hyp'|Hyp'];
            [ subst; ltac |];
            clear Hyp; rename Hyp' into Hyp);
    inversion Hyp.

(* -------------------- IOTS_ltacs --------------------*)

Ltac solve_IOLTS_rules lts Li Lu := apply (mkIOLTS lts Li Lu) ;
  repeat (
    match goal with
    | |- is_disjoint _ _ => disjoint_sets
    | |- list_helper.Equiv _ _ => proof_Equiv
    | |- NoDup _ => list_has_no_dup
    end
  ) ; fail "One or more contextual rules were not fulfilled".

Ltac all_delta_trans := intros s s' l A;
    repeat(inversion A as [B|B];
             [inversion B; split; [reflexivity | split; [reflexivity | elem_in_list]] | ];
           clear A; rename B into A); inversion A.
(*
Ltac all_quiescent_trans_incl := intros B;
    repeat(inversion B as [C|C];
      [inversion C ;
        split;
        [elem_in_list
        |apply quiescent_r1; intros s' l D; destruct D as [D E];
         repeat(inversion D as [F|F];
           [repeat(inversion E as [G|G];
             [subst l;
              subst s';
              unfold not;
              intro H';
              inversion H' as [I J K L M];
              destruct M as [N [O [P Q]]];
              repeat(inversion Q as [R|R];
               [inversion R |]; clear Q; rename R into Q); inversion Q
             |]; clear E; rename G into E); inversion E
           |]; clear D; rename F into D); inversion D
        ]
      |]; clear B; rename C into B); inversion B.
*)
(* -------------------- BE_ltacs --------------------*)

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
