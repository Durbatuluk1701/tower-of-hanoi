From Stdlib Require Import List Lia.
Import ListNotations.
(** Making Meaningful Specifications: 

  Lets explore Inductive propositions with an example: The Tower of Hanoi

  What are our objectives:
  - Create a version of the Tower of Hanoi game that is *correct*
    (what does correctness mean here?)
    (*
      - The player should not be allowed to make *invalid* moves
      - The system should allow *all* valid moves
    *)
  - Prove interesting properties about the game
    (what are they?)
    (*
      You can *always win* (but what does this really mean?)
      (*
        To be precise, for any *valid* tower of hanoi game, you can always
        move the entire stack to another 'peg'
      *)
    *)

  What are the rules of Tower of Hanoi:
  (*
    1. Only one 'disk' can move at a time
    2. You may only move the upper 'disk'
    3. disks may only be placed on top of other disks *larger* than themselves
  *)
*)

Definition state : Type :=
  list nat * list nat * list nat.

Inductive game : state -> state -> Prop :=
  | valid_move_12 : forall h1 l1 l2 l3,
    (match l2 with
    | nil => True
    | h2 :: _ => h1 < h2 
    end) ->
    game ((h1 :: l1), l2, l3) (l1, (h1 :: l2), l3)
  | valid_move_13 : forall h1 l1 l2 l3,
    match l3 with
    | nil => True
    | h3 :: _ => h1 < h3
    end ->
    game ((h1 :: l1), l2, l3) (l1, l2, (h1 :: l3))
  | valid_move_23 : forall l1 h2 l2 l3,
    match l3 with
    | nil => True
    | h3 :: _ => h2 < h3
    end ->
    game (l1, (h2 :: l2), l3) (l1, l2, (h2 :: l3))
  (* reverse moves *)
  | valid_move_21 : forall l1 h2 l2 l3,
    match l1 with
    | nil => True
    | h1 :: _ => h2 < h1
    end ->
    game (l1, (h2 :: l2), l3) ((h2 :: l1), l2, l3)
  | valid_move_31 : forall l1 l2 h3 l3,
    match l1 with
    | nil => True
    | h1 :: _ => h3 < h1
    end ->
    game (l1, l2, (h3 :: l3)) ((h3 :: l1), l2, l3)
  | valid_move_32 : forall l1 l2 h3 l3,
    match l2 with
    | nil => True
    | h2 :: _ => h3 < h2
    end ->
    game (l1, l2, (h3 :: l3)) (l1, (h3 :: l2), l3).

Inductive play : state -> state -> Prop :=
  | play_refl : forall s, play s s
  | play_step : forall s1 s2 s3,
      game s1 s2 -> 
      play s2 s3 ->
      play s1 s3.


Definition won (s : state) :=
  match s with
  | (nil, nil, _) => true
  | (_, _, _) => false
  end.

Definition two_peg_game : state := ([1;2], [], []).
Definition three_peg_game : state := ([1;2;3], [], []).

Ltac step :=
  try (eapply play_refl);
  (eapply play_step; [ econstructor; lia | ]).

Example two_peg_test_game : 
  exists done, 
    play two_peg_game done /\ won done = true.
Proof.
  exists ([],[],[1;2]).
  split; [ | reflexivity ].
  unfold two_peg_game.
  repeat step.
Qed.

Example three_peg_test_game : 
  exists done, 
    play three_peg_game done /\ won done = true.
Proof.
  eexists; split; [ unfold three_peg_game | ].
  eapply play_step; [ econstructor; lia | ].
  eapply play_step; [ econstructor; lia | ].
  eapply play_step; [ econstructor; lia | ].
  eapply play_step; [ econstructor; lia | ].
  (* stuck bouncing *)
  eapply play_step; [ eapply valid_move_31; lia | ].
  eapply play_step; [ eapply valid_move_32; lia | ].
  eapply play_step; [ eapply valid_move_13; lia | ].
  eapply play_step; [ eapply valid_move_21; lia | ].
  eapply play_step; [ eapply valid_move_31; lia | ].
  eapply play_step; [ eapply valid_move_23; lia | ].
  eapply play_step; [ eapply valid_move_12; lia | ].
  eapply play_step; [ eapply valid_move_13; lia | ].
  eapply play_step; [ eapply valid_move_23; lia | ].
  eapply play_refl.
  reflexivity.
Qed.

Ltac invc H := inversion H; subst; clear H.

Lemma canT_always_win : 
  ~ (forall start, exists done, play start done /\ won done = true).
Proof.
  intros HC.
  destruct (HC ([0],[0],[0])) as (done & Hplay & Hwin).
  invc Hplay; simpl in Hwin.
  - congruence.
  - invc H; try lia.
Qed.

Inductive sorted {X : Type} (lt : X -> X -> Prop) : list X -> Prop :=
  | sorted_nil : sorted lt []
  | sorted_single : forall x, sorted lt [x]
  | sorted_cons : forall x y rst,
    lt x y ->
    sorted lt (y :: rst) ->
    sorted lt (x :: y :: rst).
Ltac app_nils H :=
  try (eapply app_eq_nil in H; destruct H; subst);
  symmetry in H; eapply app_eq_nil in H; destruct H; subst.


Fixpoint In {X : Type} (x : X) (xs : list X) : Prop :=
  match xs with
  | nil => False
  | h :: t => x = h \/ In x t
  end.
Theorem In_app_iff : forall {X} (x : X) l1 l2,
  In x (l1 ++ l2) <-> (In x l1 \/ In x l2).
Proof.
  induction l1; destruct l2; simpl in *; 
  try (erewrite app_nil_r in *);
  try (erewrite IHl1 in *); subst;
  simpl in *;
  intuition; eauto.
Qed.

Lemma sorted_works : forall h l,
  sorted lt (h :: l) <-> (forall x, In x l -> h < x /\ sorted lt l).
Proof.
  split.
  - 
    intros Hsort.
    remember (h :: l) as L.
    generalize dependent l.
    generalize dependent h.
    induction Hsort; intros h l [= ->] ?x Hin; subst;
    simpl in Hin; intuition; subst; eauto.
    erewrite H.
    exact (proj1 (IHHsort _ _ eq_refl _ H0)).
  - generalize dependent h.
    induction l; intros; simpl in *; eauto using sorted.
    econstructor.
    * eapply (proj1 (H _ (or_introl eq_refl))).
    * eapply (proj2 (H _ (or_introl eq_refl))).
Qed.

Theorem sorted_app : forall l1 l2,
  sorted lt (l1 ++ l2) <->
  (
    sorted lt l1 
    /\ sorted lt l2 
    /\ (forall x, In x l1 -> forall y, In y l2 -> x < y)
  ).
Proof.
  split; intros.
  - remember (l1 ++ l2) as L.
    generalize dependent l2.
    generalize dependent l1.
    induction H; intros.
    * app_nils HeqL; 
      split; [ eauto using sorted | split; [ eauto using sorted 
        | intros ?x Hin1 ?y Hin2; simpl in Hin1, Hin2; subst;
          intuition ]
      ].
    * destruct l1, l2; simpl in *; try congruence;
      injection HeqL; intros; subst;
      try (app_nils H; try congruence);
      (split; [ eauto using sorted | split; [ eauto using sorted 
        | intros ?x Hin1 ?y Hin2; simpl in Hin1, Hin2; subst;
          intuition ]
      ]).
    * destruct l1; simpl in *; subst.
      + (split; [ eauto using sorted | split; [ eauto using sorted 
          | intros ?x Hin1 ?y Hin2; simpl in Hin1, Hin2; subst;
            intuition ]
        ]).
      + injection HeqL; intros; subst.
        destruct (IHsorted _ _ H1) as (? & ? & ?).
        split.
        -- destruct l1; eauto using sorted.
          econstructor; eauto.
          injection H1; intros; subst; eauto.
        -- split; [ eauto using sorted | ].
          intros x [-> | Hin1] ?y Hin2; eauto.
          destruct l1; simpl in *.
          ** destruct l2; try congruence.
            injection H1; intros; subst.
            simpl in Hin2; intuition; subst; eauto.
            erewrite H.
            eapply sorted_works in H3; destruct H3; eauto.
          ** injection H1; intros; subst.
            erewrite H; eauto.
  - destruct H as (? &? &?).
    generalize dependent l2.
    generalize dependent l1.
    induction l1; intros; simpl in *; eauto.
    invc H; simpl in *.
    * erewrite sorted_works; intuition.
    * econstructor; eauto.
Qed.

Inductive NoDup {X : Type} : list X -> Prop :=
  | nodup_nil : NoDup []
  | nodup_single : forall x, NoDup [x]
  | nodup_cons : forall x xs,
    ~ (In x xs) ->
    NoDup xs ->
    NoDup (x :: xs).

Lemma NoDup_app_unfold : forall {X} (l1 l2 : list X),
  NoDup (l1 ++ l2) <-> (
    NoDup l1 /\ NoDup l2 /\
    (forall x, In x l1 -> ~ (In x l2)) /\
    (forall x, In x l2 -> ~ (In x l1))
  ).
Proof.
  split; intros.
  - remember (l1 ++ l2) as L.
    generalize dependent l2.
    generalize dependent l1.
    induction H; intros.
    * app_nils HeqL.
      repeat (split; eauto using NoDup).
    * destruct l1, l2; simpl in *; try congruence;
      injection HeqL; intros; subst; clear HeqL;
      repeat (split; eauto using NoDup);
      app_nils H; eauto using NoDup; try congruence.
    * destruct l1; simpl in *; subst.
      + repeat (split; eauto using NoDup).
      + injection HeqL; intros; subst; clear HeqL.
        destruct (IHNoDup _ _ eq_refl) as (?&?&?&?).
        erewrite In_app_iff in *.
        repeat (split; eauto using NoDup).
        -- intros ? [HC | HC]; subst; eauto.
        -- intros ? Hin [HC | HC]; subst.
          ** eauto.
          ** eapply H4 in Hin; eauto.
  - destruct H as (? &? &? &?).
    generalize dependent l2.
    generalize dependent l1.
    induction l1; intros; simpl in *; eauto.
    invc H.
    * eauto using NoDup.
    * econstructor.
      + intros HC.
        erewrite In_app_iff in HC.
        destruct HC; eauto.
        eapply H2 in H; eauto.
      + 
        assert (forall x, In x l1 -> ~ In x l2) by eauto.

        eapply (IHl1 H6 _ H0 H).
        intros x Hinl2 Hinl1.
        eapply H2 in Hinl2.
        eauto.
Qed.

Lemma NoDup_app : forall {X} (l1 l2 : list X),
  NoDup (l1 ++ l2) <-> NoDup (l2 ++ l1).
Proof.
  intros.
  erewrite NoDup_app_unfold.
  erewrite NoDup_app_unfold.
  tauto.
Qed.

Inductive valid_state : state -> Prop :=
  | valid_all : forall l1 l2 l3,
    sorted lt l1 ->
    sorted lt l2 ->
    sorted lt l3 ->
    List.length (l1 ++ l2 ++ l3) <> 0 ->
    (* make sure none of the same elements appear *)
    NoDup (l1 ++ l2 ++ l3) ->
    valid_state (l1, l2, l3).

Inductive steps_to_win : state -> state -> nat -> Prop :=
  | winning_state : forall st, 
    won st = true -> steps_to_win st st 0
  | take_a_step : forall st st' st'' n,
    game st st' ->
    steps_to_win st' st'' n ->
    steps_to_win st st'' (S n).

Theorem steps_to_win_iff_play_won : forall st st',
  (exists n, steps_to_win st st' n) <->
  (play st st' /\ won st' = true).
Proof.
  split; intros.
  - destruct H; 
    induction H; try (destruct IHsteps_to_win); split; eauto using play.
  - destruct H.
    induction H; eauto using steps_to_win.
    destruct (IHplay H0).
    exists (S x); eauto using steps_to_win.
Qed.

Ltac simpl_nd :=
  repeat (erewrite app_nil_l in *);
  repeat (erewrite app_nil_r in *);
  simpl in *;
  repeat (repeat (match goal with
  | [ h : NoDup (?l ++ ?l2) |- NoDup (?l2 ++ ?l) ] =>
    exact (proj1 (NoDup_app _ _) h)
  | [ h : _ ++ _ = nil |- _ ] => 
    eapply app_eq_nil in h as [? ?]; subst; simpl in *;
      eauto using NoDup; try congruence
  | [ h : nil = _ ++ _ |- _ ] => 
    app_nils h; simpl in *; subst;
      eauto using NoDup; try congruence
  | [ h : NoDup (_ :: _) |- _ ] => 
    let Heq_x := fresh "Heq_x" in
    let Heq_xs := fresh "Heq_xs" in
    let Hin := fresh "Hin" in
    let HND := fresh "HND" in
    inversion h as 
      [ | ?x [Heq_x Heq_nil] | ?x ?xs Hin HND [Heq_x Heq_xs]];
    subst; clear h; [ 
      app_nils Heq_nil; simpl in *; subst;
        eauto using NoDup; try congruence
      | 
    ]
  | [ h : NoDup (_ ++ (_ :: _)) |- _ ] =>
    erewrite NoDup_app in h; simpl in h
  | [ h : NoDup (_ ++ (_ :: _) ++ _) |- _ ] =>
    erewrite NoDup_app in h; simpl in h
  | [ h : NoDup (_ ++ _ ++ (_ :: _)) |- _ ] =>
    erewrite NoDup_app in h;
    erewrite <- app_assoc in h;
    erewrite NoDup_app in h;
    try (erewrite <- app_assoc in h); simpl in h
  | [ h : context [ In _ (_ ++ _) ] |- _ ] => 
    erewrite In_app_iff in h; simpl in *
  | [ |- NoDup (_ ++ _ ++ (_ :: _)) ] => 
    erewrite NoDup_app;
    erewrite <- app_assoc;
    erewrite NoDup_app;
    try (erewrite <- app_assoc); simpl
  | [ |- NoDup (_ ++ (_ :: _)) ] => 
    erewrite NoDup_app; simpl
  | [ |- NoDup (_ :: _) ] => 
    let HC := fresh "HC" in
    econstructor; [ intros HC; simpl in HC | ]
  | [ h : NoDup ((_ ++ _) ++ _) |- _ ] =>
    erewrite <- app_assoc in h
  | [ |- NoDup ((_ ++ _) ++ _) ] =>
    erewrite <- app_assoc
  end); intuition); eauto using NoDup.

Theorem game_preserves_valid_states : forall start,
  valid_state start ->
  forall next,
    game start next ->
    valid_state next.
Proof.
  intros.
  induction H0; invc H.
  - destruct l2; (econstructor; [ 
      invc H4; eauto using sorted
      | eauto using sorted 
      | eauto using sorted
      | intros HC; simpl in HC;
        repeat (erewrite length_app in *; simpl in *);
        lia
      | simpl_nd
    ]).
  - destruct l3; (econstructor; [ 
      invc H4; eauto using sorted
      | eauto using sorted 
      | eauto using sorted
      | intros HC; simpl in HC;
        repeat (erewrite length_app in *; simpl in *);
        lia
      | simpl_nd
    ]).
  - destruct l3; (econstructor; [ 
      eauto using sorted
      | invc H5; eauto using sorted 
      | eauto using sorted
      | intros HC; simpl in HC;
        repeat (erewrite length_app in *; simpl in *);
        lia
      | simpl_nd
    ]).
  - destruct l1; (econstructor; [ 
      eauto using sorted
      | invc H5; eauto using sorted 
      | eauto using sorted
      | intros HC; simpl in HC;
        repeat (erewrite length_app in *; simpl in *);
        lia
      | simpl_nd
    ]).
  - destruct l1; (econstructor; [ 
      eauto using sorted
      | eauto using sorted 
      | invc H6; eauto using sorted
      | intros HC; simpl in HC;
        repeat (erewrite length_app in *; simpl in *);
        lia
      | simpl_nd
    ]).
    erewrite app_assoc.
    erewrite NoDup_app.
    eauto.
  - destruct l2; (econstructor; [ 
      eauto using sorted
      | eauto using sorted 
      | invc H6; eauto using sorted
      | intros HC; simpl in HC;
        repeat (erewrite length_app in *; simpl in *);
        lia
      | simpl_nd
    ]).
    (* erewrite app_assoc. *)
    erewrite NoDup_app.
    erewrite <- app_assoc.
    eauto.
Qed.

Theorem valid_state_can_move : forall start,
  valid_state start ->
  exists next, game start next.
Proof.
  intros start Hvs.
  invc Hvs.
  destruct l1, l2, l3;
  try (eexists; econstructor; lia).
  * simpl in *; lia.
  * 
    assert (n < n0 \/ n = n0 \/ n > n0) by lia.
    assert (n < n1 \/ n = n1 \/ n > n1) by lia.
    assert (n0 < n1 \/ n0 = n1 \/ n0 > n1) by lia.
    destruct H4 as [?|[?|?]], H5 as [?|[?|?]], H6 as [?|[?|?]];
    try (eexists; econstructor; lia); subst.
    invc H3.
    - destruct l1; simpl in *; congruence.
    - repeat (erewrite In_app_iff in *; simpl in *).
      exfalso; eauto.
Qed.

Definition even_ind (P : nat -> Prop) (n : nat) 
  (P0 : P 0) (P1 : P 1) (PSS : forall n, P n -> P (S (S n))) :=
  fix F n :=
    match n with
    | 0 => P0
    | 1 => P1
    | S (S n') => PSS n' (F n')
    end.

Lemma NoDup_app_triple : forall {X} (l1 l2 l3 : list X),
  NoDup (l1 ++ l2 ++ l3) <-> NoDup (l1 ++ l3 ++ l2).
Proof.
  intros.
  repeat (erewrite NoDup_app_unfold).
  setoid_rewrite In_app_iff.
  setoid_rewrite or_comm at 1.
  setoid_rewrite or_comm at 2.
  tauto.
Qed.

Theorem valid_state_reorder : forall l1 l2 l3,
  valid_state (l1, l2, l3) <-> valid_state (l1, l3, l2).
Proof.
  split; intros H; invc H; econstructor; eauto;
  repeat (erewrite length_app in *;
    try (erewrite PeanoNat.Nat.add_assoc in *);
    try (lia)
  ); eapply NoDup_app_triple; eauto.
Qed.

Lemma game_never_changes_elements : forall l1 l2 l3 l1' l2' l3',
  game (l1, l2, l3) (l1', l2', l3') ->
  (forall x, (In x l1 \/ In x l2 \/ In x l3) <-> 
    (In x l1' \/ In x l2' \/ In x l3')).
Proof.
  intros l1 l2 l3 l1' l2' l3' Hgame.
  remember (l1, l2, l3) as S.
  remember (l1', l2', l3') as F.
  generalize dependent l3'.
  generalize dependent l2'.
  generalize dependent l1'.
  generalize dependent l3.
  generalize dependent l2.
  generalize dependent l1.
  induction Hgame;
  intros ?l1 ?l2 ?l3 [= ] ?l1' ?l2' ?l3' [= ] x; subst;
  simpl; intuition.
Qed.

(* Lemma game_smallest_bounce_around : forall l1 l2 l3 l1' l2' l3',
  valid_state (l1, l2, l3) ->
  game (l1, l2, l3) (l1', l2', l3') ->
  forall a,
    (forall x, (In x l1 \/ In x l2 \/ In x l3) -> a < x) ->
    game (a :: l1, l2, l3) (a :: l1', l2', l3').
Proof.
Admitted. *)
Ltac solve_valid Hax :=
  try (match goal with
  | [ |- match ?x with _ => _ end ] => 
    destruct x; [ eauto; exact I |  ] 
  end); eauto; eapply Hax; simpl; intuition.

Theorem smallest_bounce_around_12 : forall l1 l2 l3 l1' l2' l3',
  valid_state (l1, l2, l3) ->
  play (l1, l2, l3) (l1', l2', l3') ->
  forall a,
    (forall x, (In x l1 \/ In x l2 \/ In x l3) -> a < x) ->
    play (a :: l1, l2, l3) (l1', a :: l2', l3').
Proof.
  intros l1 l2 l3 l1' l2' l3' Hvalid Hplay.
  remember (l1, l2, l3) as S.
  remember (l1', l2', l3') as F.
  generalize dependent Hvalid.
  generalize dependent l3'.
  generalize dependent l2'.
  generalize dependent l1'.
  generalize dependent l3.
  generalize dependent l2.
  generalize dependent l1.
  induction Hplay. 
  - intros l1 l2 l3 [= ->] l1' l2' l3' [= -> -> ->] Hvalid a Hax.
    econstructor.
    eapply valid_move_12.
    * destruct l2'; eauto; eapply Hax; simpl; eauto.
    * econstructor.
  - intros l1 l2 l3 [= ->] l1' l2' l3' [= ->] Hvalid a Hax.
    destruct s2 as [[l1'' l2''] l3''].
    pose proof (game_never_changes_elements _ _ _ _ _ _ H) as HInSame.
    remember (l1, l2, l3) as S.
    remember (l1'', l2'', l3'') as F.
    pose proof (game_preserves_valid_states _ Hvalid _ H) as Hvalid'.
    induction H; injection HeqS; injection HeqF; intros; subst;
    clear HeqS HeqF;
    pose proof (IHHplay _ _ _ eq_refl _ _ _ eq_refl Hvalid' a).
    * econstructor; [ eapply valid_move_13; solve_valid Hax | ].
      econstructor; [ eapply valid_move_12; solve_valid Hax | ].
      econstructor; [ eapply valid_move_31; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_12; solve_valid Hax | ].
      econstructor; [ eapply valid_move_13; solve_valid Hax | ].
      econstructor; [ eapply valid_move_21; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_23; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_13; solve_valid Hax | ].
      econstructor; [ eapply valid_move_21; solve_valid Hax | ].
      econstructor; [ eapply valid_move_31; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_12; solve_valid Hax | ].
      econstructor; [ eapply valid_move_31; solve_valid Hax | ].
      econstructor; [ eapply valid_move_21; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_32; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
Qed.

Theorem smallest_bounce_around_13 : forall l1 l2 l3 l1' l2' l3',
  valid_state (l1, l2, l3) ->
  play (l1, l2, l3) (l1', l2', l3') ->
  forall a,
    (forall x, (In x l1 \/ In x l2 \/ In x l3) -> a < x) ->
    play (a :: l1, l2, l3) (l1', l2', a :: l3').
Proof.
  intros l1 l2 l3 l1' l2' l3' Hvalid Hplay.
  remember (l1, l2, l3) as S.
  remember (l1', l2', l3') as F.
  generalize dependent Hvalid.
  generalize dependent l3'.
  generalize dependent l2'.
  generalize dependent l1'.
  generalize dependent l3.
  generalize dependent l2.
  generalize dependent l1.
  induction Hplay. 
  - intros l1 l2 l3 [= ->] l1' l2' l3' [= -> -> ->] Hvalid a Hax.
    econstructor.
    eapply valid_move_13.
    * destruct l3'; eauto; eapply Hax; simpl; eauto.
    * econstructor.
  - intros l1 l2 l3 [= ->] l1' l2' l3' [= ->] Hvalid a Hax.
    destruct s2 as [[l1'' l2''] l3''].
    pose proof (game_never_changes_elements _ _ _ _ _ _ H) as HInSame.
    remember (l1, l2, l3) as S.
    remember (l1'', l2'', l3'') as F.
    pose proof (game_preserves_valid_states _ Hvalid _ H) as Hvalid'.
    induction H; injection HeqS; injection HeqF; intros; subst;
    clear HeqS HeqF;
    pose proof (IHHplay _ _ _ eq_refl _ _ _ eq_refl Hvalid' a).
    * econstructor; [ eapply valid_move_13; solve_valid Hax | ].
      econstructor; [ eapply valid_move_12; solve_valid Hax | ].
      econstructor; [ eapply valid_move_31; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_12; solve_valid Hax | ].
      econstructor; [ eapply valid_move_13; solve_valid Hax | ].
      econstructor; [ eapply valid_move_21; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_23; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_13; solve_valid Hax | ].
      econstructor; [ eapply valid_move_21; solve_valid Hax | ].
      econstructor; [ eapply valid_move_31; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_12; solve_valid Hax | ].
      econstructor; [ eapply valid_move_31; solve_valid Hax | ].
      econstructor; [ eapply valid_move_21; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
    * econstructor; [ eapply valid_move_32; solve_valid Hax | ].
      eapply H0; simpl in *; intros; eapply Hax; intuition.
Qed.

Ltac nd_other :=
  simpl_nd;
  repeat (erewrite app_nil_l in *);
  repeat (erewrite app_nil_r in *);
  simpl in *;
  repeat (match goal with
  | [ h : NoDup (?l ++ ?l2) |- _ ] =>
    pose proof (proj1 (NoDup_app_unfold _ _) h) as (? & ? & ? & ?);
      clear h
  | [ h : context [In _ (_ ++ _)] |- _ ] =>
    setoid_rewrite In_app_iff in h
  | [ h : _ ++ _ = nil |- _ ] => 
    eapply app_eq_nil in h as [? ?]; subst; simpl in *;
      eauto using NoDup; try congruence
  | [ h : nil = _ ++ _ |- _ ] => 
    app_nils h; simpl in *; subst;
      eauto using NoDup; try congruence
  | [ h : NoDup (_ :: _) |- _ ] => 
    invc h; simpl in *; eauto using NoDup
  end; simpl in *; subst; try (simple congruence 1)).

Lemma valid_state_cons : forall a l1 l2 l3,
  valid_state (a :: l1, l2, l3) ->
  valid_state (l1, l2, l3) \/ (l1 = nil /\ l2 = nil /\ l3 = nil).
Proof.
  intros a l1 l2 l3 Hvalid.
  remember (a :: l1, l2, l3) as S.
  generalize dependent l3.
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent a.
  induction Hvalid; intros a ?l1 ?l2 ?l3 [= -> -> ->].
  destruct (length (l0 ++ l4 ++ l5)) eqn:LEN. 
  - repeat (rewrite length_app in *).
    assert (length l0 = 0) by lia.
    assert (length l4 = 0) by lia.
    assert (length l5 = 0) by lia.
    destruct l0, l4, l5; simpl in *; try congruence.
    eauto.
  - left; econstructor; [
      eauto using sorted
      | eauto using sorted
      | eauto using sorted
      | simpl_nd; congruence
      | simpl_nd
    ]; invc H; eauto using sorted.
Qed.

Theorem shiftable_columns_12 : forall l1 l1' l2 l3,
  valid_state (l1 ++ l1', l2, l3) ->
  (forall x, In x l1 -> 
    (forall y, In y l2 -> x < y) 
    /\ (forall y, In y l3 -> x < y) 
  ) ->
  play (l1 ++ l1', l2, l3) (l1', l1 ++ l2, l3).
Proof.
  induction l1; simpl in *; intros.
  - eauto using play.
  - 
    assert (forall x : nat, In x l1 -> (forall y : nat, In y l2 -> x < y) /\ (forall y : nat, In y l3 -> x < y)) by eauto.
    destruct (H0 _ (or_introl eq_refl)).
    destruct (valid_state_cons _ _ _ _ H) as [Hvalid' | (Hl1 &Hl2 &Hl3)].
    * pose proof (IHl1 _ _ _ Hvalid' H1).
      eapply smallest_bounce_around_12; eauto.
      intros.
      intuition.
      invc H.
      eapply sorted_works; eauto.
    * subst.
      eapply app_eq_nil in Hl1.
      destruct Hl1; subst.
      simpl.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
Qed.

Theorem shiftable_columns_13 : forall l1 l1' l2 l3,
  valid_state (l1 ++ l1', l2, l3) ->
  (forall x, In x l1 -> 
    (forall y, In y l2 -> x < y) 
    /\ (forall y, In y l3 -> x < y) 
  ) ->
  play (l1 ++ l1', l2, l3) (l1', l2, l1 ++ l3).
Proof.
  induction l1; simpl in *; intros.
  - eauto using play.
  - 
    assert (forall x : nat, In x l1 -> (forall y : nat, In y l2 -> x < y) /\ (forall y : nat, In y l3 -> x < y)) by eauto.
    destruct (H0 _ (or_introl eq_refl)).
    destruct (valid_state_cons _ _ _ _ H) as [Hvalid' | (Hl1 &Hl2 &Hl3)].
    * pose proof (IHl1 _ _ _ Hvalid' H1).
      eapply smallest_bounce_around_13; eauto.
      intros.
      intuition.
      invc H.
      eapply sorted_works; eauto.
    * subst.
      eapply app_eq_nil in Hl1.
      destruct Hl1; subst.
      simpl.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
Qed.

Fixpoint init_list (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S n' => init_list n' ++ [n]
  end.
Lemma In_init_list_max : forall n x,
  In x (init_list n) ->
  x <= n.
Proof.
  induction n; simpl in *; intros; intuition; subst; eauto.
  erewrite In_app_iff in H; simpl in *; intuition; try lia.
Qed.
Lemma NoDup_init_list : forall n,
  NoDup (init_list n).
Proof.
  induction n; eauto using NoDup; simpl.
  eapply NoDup_app_unfold; intuition; eauto using NoDup;
  simpl in *; intuition; subst;
  match goal with
  | [ h : In _ _ |- _ ] =>
    pose proof (In_init_list_max n (S n) h); lia
  end.
Qed.
Lemma sorted_init_list : forall n,
  sorted lt (init_list n).
Proof.
  induction n; simpl in *; eauto using sorted.
  erewrite sorted_app; intuition; eauto using sorted.
  simpl in *; intuition; subst.
  pose proof (In_init_list_max n x H).
  lia.
Qed.

Definition start_game_n_disks (n : nat) : state := (init_list n, [], []).

Theorem valid_state_start_game : forall n,
  valid_state (start_game_n_disks n).
Proof.
  induction n; simpl.
  - econstructor; repeat (rewrite app_nil_r); eauto using sorted, NoDup.
  - econstructor; repeat (rewrite app_nil_r); eauto using sorted, NoDup.
    * eapply sorted_init_list.
    * intros HC; simpl in *; rewrite length_app in *; simpl in *; lia.
    * eapply NoDup_init_list.
Qed.

Theorem winnable_from_start : forall n,
  exists end_st, 
    play (start_game_n_disks n) end_st /\ won end_st = true.
Proof.
  intros.
  pose proof (valid_state_start_game n).
  unfold start_game_n_disks in *.
  exists (nil, nil, (init_list n)).
  split.
  - 
    pose proof (shiftable_columns_13 (init_list n) nil nil nil). 
    rewrite app_nil_r in H0.
    eapply H0; eauto; intros; split; intros ?x [].
  - reflexivity.
Qed.
Print Assumptions winnable_from_start.