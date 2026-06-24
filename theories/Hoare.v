From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality FunctionalExtensionality.
From mathcomp Require Import ssrbool eqtype choice.
From mathcomp Require Import finmap.
From IncLogic Require Import Imp Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.

Ltac inv H := inversion H; clear H; subst.

Definition swap_xy :=
    ASSIGN "t" (VAR "x");; ASSIGN "x" (VAR "y");; ASSIGN "y" (VAR "t").


Lemma swap_xy_correct:
  forall s, exists s',
  star red (swap_xy, s) (SKIP, s') /\ s' "x" = s "y" /\ s' "y" = s "x".
Proof.
  intros. econstructor; split.
- eapply star_step. apply red_seq_step. apply red_assign.
  eapply star_step. apply red_seq_done.
  eapply star_step. apply red_seq_step. apply red_assign.
  eapply star_step. apply red_seq_done.
  eapply star_step. apply red_assign.
  apply star_refl.
- cbn [aeval]. split.
  + rewrite (update_other "y"); [|intros H; discriminate H].
    rewrite update_same.
    rewrite update_other; [reflexivity | intros H; discriminate H].
  + rewrite update_same.
    rewrite update_other; [|intros H; discriminate H].
    apply update_same.
Qed.


Definition slow_add :=
  WHILE (LESSEQUAL (CONST 1) (VAR "x")) DO
        (ASSIGN "x" (MINUS (VAR "x") (CONST 1)) ;;
         ASSIGN "y" (PLUS  (VAR "y") (CONST 1))) END.

Lemma slow_add_correct:
  forall (s : store),
  s "x" >= 0 ->
  exists s' : store, star red (slow_add, s) (SKIP, s') /\ s' "y" = s "y" + s "x".
Proof.
Admitted.

Definition assertion : Type := store -> Prop.

Definition postassertion : Type := result -> Prop.

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp) (v: Z) : assertion :=
  fun s => aeval a s = v.

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : assertion :=
  fun s => beval b s = false.

(** The assertion written "[ P[x <- a] ]" in the literature.
    Substituting [a] for [x] in [P] amounts to evaluating [P] in
    stores where the variable [x] is equal to the value of expression [a]. *)

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

Notation "P [ x ↦ a ]" := (aupdate x a P) (at level 10).

Example aupdate_example:
  (aequal (VAR "y") 5 [ "y" ↦ (PLUS (VAR "y") (CONST 2)) ])
  (update "y" 3%Z (finmap.fmap0 : store)).
Proof.
  unfold aupdate, aequal. cbn [aeval]. rewrite !update_same. reflexivity.
Qed.

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

Definition paimp (P Q: postassertion) : Prop :=
  forall r, P r -> Q r.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P --* Q" := (paimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

Ltac Tauto :=
  let s := fresh "s" in
  unfold aand, aor, aimp in *;
  intro s;
  repeat (match goal with [ H: (forall (s': store), _) |- _ ] => specialize (H s) end);
  intuition auto.

(** The rules of weak Hoare logic *)

(** Here are the base rules for Hoare logic.
    They define a relation [Hoare P c Q], where
-   [P] is the precondition, assumed to hold "before" executing [c];
-   [c] is the program or program fragment we reason about;
-   [Q] is the postcondition, guaranteed to hold "after" executing [c].

  This is a "weak" logic, meaning that it does not guarantee termination
  of the command [c].  What is guaranteed is that if [c] terminates,
  then its final store satisfies postcondition [Q]. *)

Reserved Notation "⦃ P ⦄ c ⦃ Q ⦄" (at level 90, c at next level).

Definition aforall {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => forall (a: A), P a s.

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

Inductive WeakHoareRes: assertion -> com -> postassertion -> Prop :=
| Hoare_skip_r: forall P,
  (* ------------------ *)
  ⦃ P ⦄ SKIP ⦃ P ⦄
| Hoare_assign_r: forall P x a,
  (* ------------------------------ *)
    ⦃ aupdate x a P ⦄ ASSIGN x a ⦃ P ⦄
| Hoare_nondet: forall x Q,
      ⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄ NONDET x ⦃ Q ⦄
| Hoare_seq_ok: forall P Q R c1 c2,
    ⦃ P ⦄ c1 ⦃ Q ⦄ ->
    ⦃ Q ⦄ c2 ⦃ R ⦄ ->
    (* ------------------ *)
    ⦃ P ⦄ (c1 ;; c2) ⦃ R ⦄
| Hoare_seq_err: forall P c1 c2,
    WeakHoareRes P c1 (fun r => match r with RError _ => True | _ => False end) ->
    (* ------------------ *)
    WeakHoareRes P (c1 ;; c2) (fun r => match r with RError _ => True | _ => False end)
| Hoare_consequence_res: forall P Q P' Q' c,
    ⦃ P ⦄ c ⦃ Q ⦄ ->
    P' -->> P ->
    Q -->> Q' ->
    (* -------------*)
    ⦃ P' ⦄ c ⦃ Q' ⦄
| Hoare_choice_res: forall P Q c1 c2,
    ⦃ P ⦄ c1 ⦃ Q ⦄ ->
    ⦃ P ⦄ c2 ⦃ Q ⦄ ->
    (* ---------------------- *)
    ⦃ P ⦄ (c1 ⊕ c2) ⦃ Q ⦄
| Hoare_cstar_ress: forall INV c, 
    ⦃ INV ⦄ c ⦃ INV ⦄ ->
    (* ------------------ *)
    ⦃ INV ⦄ (CSTAR c) ⦃ INV ⦄
where "⦃ P ⦄ c ⦃ Q ⦄" :=
  (WeakHoareRes P c (fun r => match r with
                          | RNormal s => Q s
                          | RError _ => False
                          end)).

Lemma Hoare_consequence_pre: forall P P' Q c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      P' -->> P ->
      ⦃ P' ⦄ c ⦃ Q ⦄.
Proof.
  intros. apply Hoare_consequence_res with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_consequence_post: forall P Q Q' c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      Q -->> Q' ->
      ⦃ P ⦄ c ⦃ Q' ⦄.
Proof.
  intros. apply Hoare_consequence_res with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Example Hoare_swap_xy: forall m n,
  ⦃ (aequal (VAR "x") m //\\ aequal (VAR "y") n) ⦄ swap_xy ⦃ (aequal (VAR "x") n //\\ aequal (VAR "y") m) ⦄.
Proof.
  intros.
  eapply Hoare_consequence_pre.
- unfold swap_xy. eapply Hoare_seq_ok. apply Hoare_assign_r.
  eapply Hoare_seq_ok. apply Hoare_assign_r. apply Hoare_assign_r.
- unfold aequal, aupdate, aand, aimp; cbn [aeval].
  intros s [Hx Hy].
  rewrite (update_other "y"); [|intros H; discriminate H].
  rewrite update_same. rewrite update_same.
  rewrite update_other; [|intros H; discriminate H].
  rewrite update_other; [|intros H; discriminate H].
  rewrite update_same.
  split; assumption.
Qed.

(** * Soundness of Hoare logic *)

(** We give a semantic interpretation to the statements [Hoare P c Q]
    of Hoare logic.  The interpretation is the relation [triple P c Q]
    defined below in terms of IMP's natural semantics
    (the relation [cexec s c s']). *)

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s r, cexec s c r -> P s -> (exists s', r = RNormal s' /\ Q s').

Notation "⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄" := (triple P c Q) (at level 90, c at next level).

Lemma triple_skip: forall P,
     ⦃⦃ P ⦄⦄ SKIP ⦃⦃ P ⦄⦄.
Proof.
  unfold triple; intros. exists s. inversion H; subst. auto.
Qed.


Lemma triple_assign: forall P x a,
      ⦃⦃ aupdate x a P ⦄⦄ ASSIGN x a ⦃⦃ P ⦄⦄.
Proof.
  unfold triple, aupdate; intros P x a s r EXEC PRE.
  inversion EXEC; subst.
  eexists. split; [ reflexivity | exact PRE ].
Qed.

Lemma Hoare_nondet_inv: forall x P Q,
  ⦃ P ⦄ NONDET x ⦃ Q ⦄ -> (P -->> aforall (fun n => aupdate x (CONST n) Q)).
Proof.
  intros x P Q H.
  remember (NONDET x) as c eqn:Hc.
  remember (fun r : result => match r with
                              | RNormal s => Q s
                              | RError _ => False
                              end) as Po eqn:HPo.
  revert Q HPo. revert x Hc.
  induction H; intros xg Hc Qg HPo; try discriminate Hc.
  - (* Hoare_nondet *)
    injection Hc as Hxx; subst xg.
    assert (HQeq : Q = Qg).
    { apply functional_extensionality. intros s.
      change (Q s) with ((fun r : result => match r with
                                            | RNormal s => Q s
                                            | RError _ => False
                                            end) (RNormal s)).
      rewrite HPo. reflexivity. }
    subst Q. unfold aimp. auto.
  - (* Hoare_consequence_res *)
    assert (HQeq : Q' = Qg).
    { apply functional_extensionality. intros s.
      change (Q' s) with ((fun r : result => match r with
                                             | RNormal s => Q' s
                                             | RError _ => False
                                             end) (RNormal s)).
      rewrite HPo. reflexivity. }
    subst Q'.
    intros s HP's n.
    apply H1.
    refine (IHWeakHoareRes xg Hc Q _ s _ n).
    + reflexivity.
    + apply H0. exact HP's.
Qed.

Lemma triple_nondet: forall x Q,
    ⦃⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄⦄ NONDET x ⦃⦃ Q ⦄⦄.
Proof.
  unfold triple, aforall, aupdate.
  intros x Q s r EXEC PRE.
  inversion EXEC; subst.
  eexists. split; [ reflexivity | ].
  cbn. apply PRE.
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      ⦃⦃ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ Q ⦄⦄ c2 ⦃⦃ R ⦄⦄ ->
      ⦃⦃ P ⦄⦄ c1;;c2 ⦃⦃ R ⦄⦄.
Proof.
  unfold triple; intros P Q R c1 c2 H1 H2 s r EXEC PRE.
  inversion EXEC; subst.
  - (* cexec_seq: c1 normal, c2 normal *)
    match goal with
    | E1 : cexec s c1 (RNormal ?s'),
      E2 : cexec ?s' c2 (RNormal ?s'') |- _ =>
      destruct (H1 s (RNormal s') E1 PRE) as (sx & EQ1 & QSx);
      inversion EQ1; subst sx;
      destruct (H2 s' (RNormal s'') E2 QSx) as (sy & EQ2 & RSy);
      inversion EQ2; subst sy;
      exists s''; split; [ reflexivity | exact RSy ]
    end.
  - (* cexec_seq_error: c1 errors *)
    match goal with
    | E1 : cexec s c1 (RError ?se) |- _ =>
      destruct (H1 s (RError se) E1 PRE) as (? & EQ & _); discriminate
    end.
  - (* cexec_seq_error_right: c1 normal, c2 errors *)
    match goal with
    | E1 : cexec s c1 (RNormal ?s'),
      E2 : cexec ?s' c2 (RError ?se) |- _ =>
      destruct (H1 s (RNormal s') E1 PRE) as (sx & EQ1 & QSx);
      inversion EQ1; subst sx;
      destruct (H2 s' (RError se) E2 QSx) as (? & EQ & _); discriminate
    end.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      ⦃⦃ atrue b //\\ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ afalse b //\\ P ⦄⦄ c2 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ P ⦄⦄ IF b THEN c1 ELSE c2 END ⦃⦃ Q ⦄⦄.
Proof.
  unfold triple, aand, atrue, afalse.
  intros P Q b c1 c2 H1 H2 s r EXEC PRE.
  inversion EXEC; subst.
  - (* choice_left: cexec s (ASSUME b ;; c1) r *)
    match goal with E : cexec s (ASSUME b ;; c1) r |- _ => inversion E; subst end.
    + (* SEQ normal *)
      match goal with EA : cexec s (ASSUME b) _ |- _ => inversion EA; subst end.
      eapply H1; eauto.
    + (* SEQ error left: ASSUME b errors — impossible *)
      match goal with EA : cexec s (ASSUME b) (RError _) |- _ => inversion EA end.
    + (* SEQ error right *)
      match goal with EA : cexec s (ASSUME b) _ |- _ => inversion EA; subst end.
      eapply H1; eauto.
  - (* choice_right: cexec s (ASSUME (NOT b) ;; c2) r *)
    match goal with E : cexec s (ASSUME (NOT b) ;; c2) r |- _ => inversion E; subst end.
    + match goal with EA : cexec s (ASSUME (NOT b)) _ |- _ => inversion EA; subst end.
      eapply H2; eauto.
      split; [ apply Bool.negb_true_iff; assumption | exact PRE ].
    + match goal with EA : cexec s (ASSUME (NOT b)) (RError _) |- _ => inversion EA end.
    + match goal with EA : cexec s (ASSUME (NOT b)) _ |- _ => inversion EA; subst end.
      eapply H2; eauto.
      split; [ apply Bool.negb_true_iff; assumption | exact PRE ].
Qed.

(** Helper: [P] is preserved across any number of iterations of the loop body
    [(ASSUME b ;; c)] when [c] preserves [P] under the [b]-true precondition. *)
Lemma triple_while_invariant: forall P b c s s',
  ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄ ->
  star (step_iter (ASSUME b ;; c)) s s' ->
  P s -> P s'.
Proof.
  intros P b c s s' H STAR PS.
  induction STAR as [ x | x y z STEP STAR' IH ]; [ exact PS | ].
  apply IH. clear IH.
  unfold step_iter in STEP. inversion STEP. subst.
  (* STEP gives:
       H4 : cexec x (ASSUME b) (RNormal s')
       H6 : cexec s' c (RNormal y)         (where s' is the intermediate)
     after inversion of the inner ASSUME we get beval b x = true and s' = x. *)
  match goal with EA : cexec x (ASSUME b) (RNormal ?sm) |- _ => inversion EA; subst sm end.
  match goal with EC : cexec x c (RNormal y) |- _ =>
    destruct (H x (RNormal y) EC) as (sx & EQ & PSx);
      [ split; assumption | inversion EQ; subst sx; exact PSx ]
  end.
Qed.

(** Helper: a [cexec] derivation for a [SEQ] command can be decomposed into
    its three possible shapes. *)
Lemma cexec_seq_inv:
  forall c1 c2 s r,
    cexec s (c1 ;; c2) r ->
    (exists sm sf, cexec s c1 (RNormal sm) /\ cexec sm c2 (RNormal sf) /\ r = RNormal sf)
    \/ (exists sf, cexec s c1 (RError sf) /\ r = RError sf)
    \/ (exists sm sf, cexec s c1 (RNormal sm) /\ cexec sm c2 (RError sf) /\ r = RError sf).
Proof.
  intros c1 c2 s r EXEC.
  inversion EXEC; subst.
  - left. eauto.
  - right. left. eauto.
  - right. right. eauto.
Qed.

Lemma triple_while: forall P b c,
      ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄ ->
      ⦃⦃ P ⦄⦄ WHILE b DO c END ⦃⦃ afalse b //\\ P ⦄⦄.
Proof.
  unfold triple, aand, atrue, afalse.
  intros P b c H s r EXEC PRE.
  (* WHILE b DO c END = ((ASSUME b ;; c) ★) ;; ASSUME (NOT b) *)
  apply cexec_seq_inv in EXEC.
  destruct EXEC as
    [ (sm & sf & EI & EA & ->)
    | [ (sf & EI & ->) | (sm & sf & EI & EA & ->) ] ].
  - (* SEQ normal *)
    apply cexec_cstar_iff_star in EI.
    assert (PSm : P sm) by (eapply triple_while_invariant; eauto).
    (* From EA : cexec sm (ASSUME (NOT b)) (RNormal sf) extract: sm = sf, beval (NOT b) sm = true *)
    inversion EA as [ | | | | ?se ?bv HBeval HEq | | | | | | | | | ]; subst.
    exists sf; split;
      [ reflexivity
      | split; [ apply Bool.negb_true_iff; exact HBeval | exact PSm ] ].
  - (* SEQ error left: iterated body errors *)
    apply cexec_cstar_err_iff in EI.
    destruct EI as (sm & STAR & ERR).
    assert (PSm : P sm) by (eapply triple_while_invariant; eauto).
    apply cexec_seq_inv in ERR.
    destruct ERR as
      [ (sm1 & sf1 & _ & _ & EQbad)
      | [ (sf1 & EA & _) | (sx & sf1 & EA & EC & _) ] ].
    + (* normal yields RNormal, can't equal RError *)
      discriminate EQbad.
    + (* ASSUME b errors: impossible *)
      inversion EA.
    + (* ASSUME b ok, c errors: contradicts H. EA : cexec sm (ASSUME b) (RNormal sx) *)
      inversion EA; subst sx.
      destruct (H sm (RError sf1) EC) as (? & EQc & _);
        [ split; assumption | discriminate ].
  - (* SEQ error right: ASSUME (NOT b) errors. Impossible. *)
    inversion EA.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ ->
      P' -->> P ->
      Q -->> Q' ->
      ⦃⦃ P' ⦄⦄ c ⦃⦃ Q' ⦄⦄.
Proof.
  unfold triple, aimp; intros P Q P' Q' c HT P'P QQ' s r EXEC PRE.
  destruct (HT s r EXEC (P'P s PRE)) as (s' & EQ & QSx).
  exists s'. split; [ exact EQ | apply QQ', QSx ].
Qed.

Lemma triple_assign_fwd: forall x a P,
  ⦃⦃ P ⦄⦄
  ASSIGN x a 
  ⦃⦃ aexists (fun m => aexists (fun n =>
     aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) ⦄⦄.
Proof.
Admitted.

Fixpoint modified_by (c: com) (x: ident) : Prop :=
  match c with
  | SKIP => False
  | ASSIGN y a => x = y
  | ERROR => False
  | ASSUME b => False
  | NONDET y => x = y
  |  c1 ;; c2 => modified_by c1 x \/ modified_by c2 x
  |  c1 ⊕ c2 => modified_by c1 x \/ modified_by c2 x
  |  c ★ => modified_by c x
  end.

Lemma cexec_modified:
  forall x s1 c s2,
  cexec s1 c s2 -> ~modified_by c x ->
  match s2 with
  | RNormal s => s x = s1 x
  | RError  s => s x = s1 x
  end.
Proof.
  intros x s1 c s2 EXEC.
  induction EXEC; intros NMOD; cbn in NMOD;
    try reflexivity;
    try (apply update_other; intro; apply NMOD; symmetry; assumption);
    try (rewrite IHEXEC2, IHEXEC1; tauto);
    try (apply IHEXEC; tauto).
Qed.

(** "[x] belongs to the (finite) domain of the store [s]."

    Trivially true for every variable under the old function-store model,
    but a real predicate with finmap stores. *)
Definition in_domf (x: ident) : assertion :=
  fun s => x \in domf s.

(** [x] in [domf] is preserved by any [cexec] that does not modify [x]. *)
Lemma dom_update: forall (x y: ident) v (s: store),
  (x \in domf (update y v s)) = ((x == y) || (x \in domf s))%bool.
Proof.
  intros x y v s. unfold update. rewrite dom_setf.
  apply in_fset1U.
Qed.

Lemma cexec_dom_preserved: forall x s1 c s2,
  cexec s1 c s2 -> ~modified_by c x ->
  match s2 with
  | RNormal s => (x \in domf s) = (x \in domf s1)
  | RError  s => (x \in domf s) = (x \in domf s1)
  end.
Proof.
  intros x s1 c s2 EXEC.
  induction EXEC; intros NMOD; cbn in NMOD; try reflexivity.
  - rewrite dom_update.
    assert (Hne : (x == x0) = false).
    { apply (@ssrbool.introF _ ((x == x0)%bool) (@eqP _ _ _)). intro H. apply NMOD, H. }
    rewrite Hne. reflexivity.
  - rewrite dom_update.
    assert (Hne : (x == x0) = false).
    { apply (@ssrbool.introF _ ((x == x0)%bool) (@eqP _ _ _)). intro H. apply NMOD, H. }
    rewrite Hne. reflexivity.
  - apply Decidable.not_or in NMOD. destruct NMOD as [N1 N2].
    specialize (IHEXEC1 N1). specialize (IHEXEC2 N2).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
  - apply Decidable.not_or in NMOD. destruct NMOD as [N1 _].
    apply IHEXEC. exact N1.
  - apply Decidable.not_or in NMOD. destruct NMOD as [N1 N2].
    specialize (IHEXEC1 N1). specialize (IHEXEC2 N2).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
  - apply Decidable.not_or in NMOD. apply IHEXEC, NMOD.
  - apply Decidable.not_or in NMOD. apply IHEXEC, NMOD.
  - specialize (IHEXEC1 NMOD). specialize (IHEXEC2 NMOD).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
  - apply IHEXEC. exact NMOD.
  - specialize (IHEXEC1 NMOD). specialize (IHEXEC2 NMOD).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
Qed.

Definition independent_of (P: assertion) (vars: ident -> Prop) : Prop :=
  forall (s1 s2 : store),
  (forall x, ~ vars x -> s1 x = s2 x) ->
  (P s1 <-> P s2).

Lemma triple_frame:
  forall c P Q R,
  ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ ->
  independent_of R (modified_by c) ->
  ⦃⦃ P //\\ R ⦄⦄ c ⦃⦃ Q //\\ R ⦄⦄.
Proof.
  unfold triple, aand, independent_of.
  intros c P Q R HT INDEP s r EXEC [HPs HRs].
  destruct (HT s r EXEC HPs) as (s' & -> & HQs').
  exists s'. split; [ reflexivity | split; [ exact HQs' | ] ].
  apply (INDEP s s');
    [ intros x NMOD; symmetry;
      exact (cexec_modified x s c (RNormal s') EXEC NMOD)
    | exact HRs ].
Qed.

(** Strong Hoare triples *)
Reserved Notation "⦇ P ⦈ c ⦇ Q ⦈" (at level 90, c at next level).

Definition alessthan (a: aexp) (v: Z) : assertion :=
  fun s => 0 <= aeval a s < v.

Inductive StrongHoareRes: assertion -> com -> postassertion -> Prop :=
| HOARE_skip_r: forall P,
  (* ------------------ *)
  ⦇ P ⦈ SKIP ⦇ P ⦈
| HOARE_assign_r: forall P x a,
  (* ------------------------------ *)
    ⦇ aupdate x a P ⦈ ASSIGN x a ⦇ P ⦈
| HOARE_seq_ok: forall P Q R c1 c2,
    ⦇ P ⦈ c1 ⦇ Q ⦈ ->
    ⦇ Q ⦈ c2 ⦇ R ⦈ ->
    (* ------------------ *)
    ⦇ P ⦈ (c1 ;; c2) ⦇ R ⦈
| HOARE_seq_err: forall P c1 c2,
    StrongHoareRes P c1 (fun r => match r with RError _ => True | _ => False end) ->
    (* ------------------ *)
    StrongHoareRes P (c1 ;; c2) (fun r => match r with RError _ => True | _ => False end)
| HOARE_consequence_res: forall P Q P' Q' c,
    ⦇ P ⦈ c ⦇ Q ⦈ ->
    P' -->> P ->
    Q -->> Q' ->
    (* -------------*)
    ⦇ P' ⦈ c ⦇ Q' ⦈
| HOARE_choice_res: forall P Q c1 c2,
    ⦇ P ⦈ c1 ⦇ Q ⦈ ->
    ⦇ P ⦈ c2 ⦇ Q ⦈ ->
    (* ---------------------- *)
    ⦇ P ⦈ (c1 ⊕ c2) ⦇ Q ⦈
| HOARE_cstar_ress: forall INV c a, 
    (forall v,  ⦇ INV //\\ aequal a v ⦈ c ⦇ alessthan a v //\\ INV ⦈ ) ->
    (* ------------------ *)
    ⦇ INV ⦈ (CSTAR c) ⦇ INV ⦈
where "⦇ P ⦈ c ⦇ Q ⦈" :=
  (StrongHoareRes P c (fun r => match r with
                          | RNormal s => Q s
                          | RError _ => False
                          end)).




(** Demonic total-correctness ("strong") Hoare triple: from every [P]-state,
    [c] terminates ([exists r]), never errors, and *every* result is a normal
    state satisfying [Q] *)
Definition Triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s ->
    (exists r, cexec s c r) /\
    (forall r, cexec s c r -> exists s', r = RNormal s' /\ Q s').

Notation "⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈" := (Triple P c Q) (at level 90, c at next level).

(** Termination half. *)
Lemma Triple_terminates: forall P c Q s, Triple P c Q -> P s -> exists r, cexec s c r.
Proof. intros P c Q s HT HP. apply (HT s HP). Qed.

(** Safety half is exactly the (error-aware) weak triple. *)
Lemma Triple_safe: forall P c Q, Triple P c Q -> triple P c Q.
Proof. intros P c Q HT s r EXEC HP. destruct (HT s HP) as [_ Hsafe]. exact (Hsafe r EXEC). Qed.

(** Demonic implies angelic: a unique terminating normal run reaching [Q].
    (Under nondeterminism this is strictly stronger than the old definition.) *)
Lemma Triple_func: forall P c Q s,
  Triple P c Q -> P s -> exists s', cexec s c (RNormal s') /\ Q s'.
Proof.
  intros P c Q s HT HP. destruct (HT s HP) as [[r Hr] Hsafe].
  destruct (Hsafe r Hr) as [s' [-> HQ]]. exists s'. split; [ exact Hr | exact HQ ].
Qed.

(** Assemble a demonic triple from termination + the weak (safety) triple. *)
Lemma Triple_intro: forall P c Q,
  (forall s, P s -> exists r, cexec s c r) -> triple P c Q -> Triple P c Q.
Proof.
  intros P c Q Hterm Hsafe s HP.
  split; [ apply Hterm; exact HP | intros r Hr; exact (Hsafe s r Hr HP) ].
Qed.

Lemma Triple_skip: forall P,
  ⦇⦇ P ⦈⦈ SKIP ⦇⦇ P ⦈⦈.
Proof.
  intros P. apply Triple_intro; [ | apply triple_skip ].
  intros s HP. exists (RNormal s). apply cexec_skip.
Qed.

Lemma Triple_assign: forall P x a,
      ⦇⦇ aupdate x a P ⦈⦈ ASSIGN x a ⦇⦇ P ⦈⦈.
Proof.
  intros P x a. apply Triple_intro; [ | apply triple_assign ].
  intros s PRE. exists (RNormal (update x (aeval a s) s)). apply cexec_assign.
Qed.

Lemma Triple_seq: forall P Q R c1 c2,
      ⦇⦇ P ⦈⦈ c1 ⦇⦇ Q ⦈⦈ -> ⦇⦇ Q ⦈⦈ c2 ⦇⦇ R ⦈⦈ ->
      ⦇⦇ P ⦈⦈ c1;;c2 ⦇⦇ R ⦈⦈.
Proof.
  intros P Q R c1 c2 H1 H2. apply Triple_intro.
  - intros s PRE. destruct (Triple_func _ _ _ s H1 PRE) as (sm & E1 & HQ).
    destruct (Triple_terminates _ _ _ sm H2 HQ) as [r2 E2]. destruct r2 as [sf | sf].
    + exists (RNormal sf). eapply cexec_seq; eassumption.
    + exists (RError sf). eapply cexec_seq_error_right; eassumption.
  - eapply triple_seq; [ apply (Triple_safe _ _ _ H1) | apply (Triple_safe _ _ _ H2) ].
Qed.

Lemma Triple_ifthenelse: forall P Q b c1 c2,
      ⦇⦇ atrue b //\\ P ⦈⦈ c1 ⦇⦇ Q ⦈⦈ ->
      ⦇⦇ afalse b //\\ P ⦈⦈ c2 ⦇⦇ Q ⦈⦈ ->
      ⦇⦇ P ⦈⦈ IF b THEN c1 ELSE c2 END ⦇⦇ Q ⦈⦈.
Proof.
  intros P Q b c1 c2 H1 H2. apply Triple_intro.
  - intros s PRE. destruct (beval b s) eqn:Hb.
    + assert (Hpre : (atrue b //\\ P) s) by (split; [ exact Hb | exact PRE ]).
      destruct (Triple_func _ _ _ s H1 Hpre) as (s' & EXEC & _).
      exists (RNormal s'). apply cexec_choice_left.
      apply cexec_seq with s; [ apply cexec_assume; exact Hb | exact EXEC ].
    + assert (Hpre : (afalse b //\\ P) s) by (split; [ exact Hb | exact PRE ]).
      destruct (Triple_func _ _ _ s H2 Hpre) as (s' & EXEC & _).
      exists (RNormal s'). apply cexec_choice_right.
      apply cexec_seq with s;
        [ apply cexec_assume; cbn; rewrite Hb; reflexivity | exact EXEC ].
  - apply triple_ifthenelse; [ apply (Triple_safe _ _ _ H1) | apply (Triple_safe _ _ _ H2) ].
Qed.

Lemma Triple_consequence: forall P Q P' Q' c,
      ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈ ->
      P' -->> P ->
      Q -->> Q' ->
      ⦇⦇ P' ⦈⦈ c ⦇⦇ Q' ⦈⦈.
Proof.
  intros P Q P' Q' c HT HP'P HQQ'. apply Triple_intro.
  - intros s PRE. apply (Triple_terminates _ _ _ s HT (HP'P s PRE)).
  - eapply triple_consequence; [ apply (Triple_safe _ _ _ HT) | exact HP'P | exact HQQ' ].
Qed.


Lemma Triple_while: forall P variant b c,
  (forall v,
     ⦇⦇ P //\\ atrue b //\\ aequal variant v ⦈⦈
     c
     ⦇⦇ P //\\ alessthan variant v ⦈⦈)
  ->
     ⦇⦇ P ⦈⦈ WHILE b DO c END ⦇⦇ P //\\ afalse b ⦈⦈.
Proof.
  intros P variant b c H. apply Triple_intro.
  - (* Termination: the variant gives a well-founded descent to a [¬b] state.
       Demonic [H] yields a unique decreasing successor via [Triple_func]. *)
    intros s0 PRE0.
    assert (HELP: forall n s,
                0 <= aeval variant s ->
                (Z.to_nat (aeval variant s) <= n)%nat ->
                P s ->
                exists sf,
                  cexec s (CSTAR (ASSUME b ;; c)) (RNormal sf) /\
                  P sf /\ beval b sf = false).
    { induction n as [|n IH]; intros s Hvnn Hn PS.
      - assert (Hzero : aeval variant s = 0).
        { destruct (aeval variant s) as [|p|p]; lia. }
        destruct (beval b s) eqn:Hb.
        + assert (Hpre : (P //\\ atrue b //\\ aequal variant (aeval variant s)) s).
          { split; [ exact PS | split; [ exact Hb | reflexivity ] ]. }
          destruct (Triple_func _ _ _ s (H (aeval variant s)) Hpre)
            as (s1 & _ & (_ & (Hv0 & Hlt))).
          rewrite Hzero in Hlt. lia.
        + exists s. split; [ apply cexec_cstar_done | split; assumption ].
      - destruct (beval b s) eqn:Hb.
        + assert (Hpre : (P //\\ atrue b //\\ aequal variant (aeval variant s)) s).
          { split; [ exact PS | split; [ exact Hb | reflexivity ] ]. }
          destruct (Triple_func _ _ _ s (H (aeval variant s)) Hpre)
            as (s1 & EXEC1 & (PS1 & (Hv0 & Hlt))).
          assert (Hsmaller : (Z.to_nat (aeval variant s1) <= n)%nat).
          { assert ((Z.to_nat (aeval variant s1) < Z.to_nat (aeval variant s))%nat)
              by (apply (proj1 (Z2Nat.inj_lt _ _ Hv0 Hvnn)); exact Hlt).
            lia. }
          destruct (IH s1 Hv0 Hsmaller PS1) as (s2 & EXEC2 & PS2 & Hb2).
          exists s2. split; [ | split; assumption ].
          eapply cexec_cstar_step_ok.
          * apply cexec_seq with s; [ apply cexec_assume; exact Hb | exact EXEC1 ].
          * exact EXEC2.
        + exists s. split; [ apply cexec_cstar_done | split; assumption ].
    }
    destruct (beval b s0) eqn:Hb.
    + assert (Hpre0 : (P //\\ atrue b //\\ aequal variant (aeval variant s0)) s0).
      { split; [ exact PRE0 | split; [ exact Hb | reflexivity ] ]. }
      destruct (Triple_func _ _ _ s0 (H (aeval variant s0)) Hpre0)
        as (s1 & EXEC1 & (PS1 & (Hv0 & _))).
      destruct (HELP (Z.to_nat (aeval variant s1)) s1 Hv0 (le_n _) PS1)
        as (sf & EXEC_LOOP & PSf & Hbf).
      exists (RNormal sf). apply cexec_seq with sf.
      * eapply cexec_cstar_step_ok.
        -- apply cexec_seq with s0;
             [ apply cexec_assume; exact Hb | exact EXEC1 ].
        -- exact EXEC_LOOP.
      * apply cexec_assume; cbn; rewrite Hbf; reflexivity.
    + exists (RNormal s0). apply cexec_seq with s0.
      * apply cexec_cstar_done.
      * apply cexec_assume; cbn; rewrite Hb; reflexivity.
  - (* Safety: the body never errors and preserves [P], so the weak
       partial-correctness [triple_while] applies. *)
    assert (Hbody : ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄).
    { intros s r EXEC Hpre.
      assert (Hpre' : (P //\\ atrue b //\\ aequal variant (aeval variant s)) s).
      { destruct Hpre as [Hbv HPs].
        split; [ exact HPs | split; [ exact Hbv | reflexivity ] ]. }
      destruct (Triple_safe _ _ _ (H (aeval variant s)) s r EXEC Hpre')
        as (s' & EQ & (HP' & _)).
      exists s'. split; [ exact EQ | exact HP' ]. }
    eapply triple_consequence;
      [ apply (triple_while P b c Hbody)
      | intros s HP; exact HP
      | intros s Hpost; destruct Hpost as [Hbf HPs]; split; [ exact HPs | exact Hbf ] ].
Qed.

Module Soundness.
  
  Theorem triple_soundness: forall P c Q,
    ⦃ P ⦄ c ⦃ Q ⦄ ->
    ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄.
  Proof.
  Admitted.


  (** Helper: a strong syntactic Hoare derivation is sound for partial
    correctness — every execution from a [P]-state lands in a result
    satisfying [Q].  Proved by induction on the derivation. *)
  Local Lemma Strong_partial_correctness: forall P c Q,
    StrongHoareRes P c Q ->
    forall s r, cexec s c r -> P s -> Q r.
  Proof.
    intros P c Q HSH.
    induction HSH as [
        P
      | P x a
      | P Q R c1 c2 HSH1 IH1 HSH2 IH2
      | P c1 c2 HSH IH
      | P Q P' Q' c HSH IH HP'P HQQ'
      | P Q c1 c2 HSH1 IH1 HSH2 IH2
      | INV cb a Hbody IHbody
    ]; intros sx r EXEC HP.
    - (* HOARE_skip_r *)
      inversion EXEC; subst. cbn. exact HP.
    - (* HOARE_assign_r *)
      inversion EXEC; subst. cbn. exact HP.
    - (* HOARE_seq_ok *)
      apply cexec_seq_inv in EXEC.
      destruct EXEC as
        [ (sm & sf & H1' & H2' & ->)
        | [ (sf & H1' & ->) | (sm & sf & H1' & H2' & ->) ] ].
      + specialize (IH1 sx (RNormal sm) H1' HP). cbn in IH1.
        specialize (IH2 sm (RNormal sf) H2' IH1). exact IH2.
      + specialize (IH1 sx (RError sf) H1' HP). cbn in IH1. exfalso. exact IH1.
      + specialize (IH1 sx (RNormal sm) H1' HP). cbn in IH1.
        specialize (IH2 sm (RError sf) H2' IH1). exact IH2.
    - (* HOARE_seq_err *)
      apply cexec_seq_inv in EXEC.
      destruct EXEC as
        [ (sm & sf & H1' & H2' & ->)
        | [ (sf & H1' & ->) | (sm & sf & H1' & H2' & ->) ] ].
      + specialize (IH sx (RNormal sm) H1' HP). cbn in IH. exfalso. exact IH.
      + specialize (IH sx (RError sf) H1' HP). exact IH.
      + specialize (IH sx (RNormal sm) H1' HP). cbn in IH. exfalso. exact IH.
    - (* HOARE_consequence_res *)
      apply HP'P in HP.
      specialize (IH sx r EXEC HP).
      destruct r as [s' | s']; cbn in IH |- *.
      + apply HQQ'. exact IH.
      + exact IH.
    - (* HOARE_choice_res *)
      inversion EXEC; subst.
      + eapply IH1; eassumption.
      + eapply IH2; eassumption.
    - (* HOARE_cstar_ress *)
      destruct r as [s' | s'].
      + (* RNormal: induct on the [star (step_iter cb)] chain *)
        apply cexec_cstar_iff_star in EXEC. cbn.
        revert HP. induction EXEC as [|x y z STEP STAR IHSTAR]; intros HP.
        * exact HP.
        * apply IHSTAR. unfold step_iter in STEP.
          specialize (IHbody (aeval a x) x (RNormal y) STEP (conj HP (Logic.eq_refl _))).
          cbn in IHbody. destruct IHbody as [_ HINV_y]. exact HINV_y.
      + (* RError: same chain up to the erroring iteration *)
        apply cexec_cstar_err_iff in EXEC.
        destruct EXEC as (sm & STAR & ERR).
        assert (HINV_sm : INV sm).
        { clear ERR. revert HP.
          induction STAR as [|x y z STEP STAR' IHSTAR']; intros HP.
          - exact HP.
          - apply IHSTAR'. unfold step_iter in STEP.
            specialize (IHbody (aeval a x) x (RNormal y) STEP (conj HP (Logic.eq_refl _))).
            cbn in IHbody. destruct IHbody as [_ HINV_y]. exact HINV_y. }
        specialize (IHbody (aeval a sm) sm (RError s') ERR
                          (conj HINV_sm (Logic.eq_refl _))).
        cbn in IHbody. exact IHbody.
  Qed.

  Lemma Triple_partial_soundness: forall P c Q,
    ⦇ P ⦈ c ⦇ Q ⦈ ->
    ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄.
  Proof.
    unfold triple. intros P c Q HSH s r EXEC HP.
    pose proof (Strong_partial_correctness _ _ _ HSH s r EXEC HP) as HQ.
    destruct r as [s' | s']; cbn in HQ.
    - exists s'. split; [ reflexivity | exact HQ ].
    - exfalso. exact HQ.
  Qed.


  Theorem Triple_soundness: forall P c Q,
    ⦇ P ⦈ c ⦇ Q ⦈ ->
    ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈.
  Proof.
  Admitted.

End Soundness.

Module Completness.
  (* TODO *) 
End Completness.

Module WP.
  (* TODO *) 
End WP.

Module SP.
  (* TODO *) 
End SP.