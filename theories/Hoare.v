From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality.
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
- unfold update; cbn. auto.
Qed.


Definition slow_add :=
  WHILE (LESSEQUAL (CONST 1) (VAR "x")) DO
        (ASSIGN "x" (MINUS (VAR "x") (CONST 1)) ;;
         ASSIGN "y" (PLUS  (VAR "y") (CONST 1))) END.

Lemma slow_add_correct:
  forall s,
  s "x" >= 0 ->
  exists s', star red (slow_add, s) (SKIP, s') /\ s' "y" = s "y" + s "x".
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
  (fun _ => 3).
Proof. cbv. reflexivity. Qed.

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
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

Inductive WeakHoareRes: assertion -> com -> postassertion -> Prop :=
| Hoare_skip_r: forall P,
  (* ------------------ *)
  ⦃ P ⦄ SKIP ⦃ P ⦄
| Hoare_assign_r: forall P x a,
  (* ------------------------------ *)
    ⦃ aupdate x a P ⦄ ASSIGN x a ⦃ P ⦄
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
- unfold aequal, aupdate, aand, aimp; cbn. tauto.
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

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

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

Definition independent_of (P: assertion) (vars: ident -> Prop) : Prop :=
  forall s1 s2,
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




Definition Triple (P: assertion) (c: com) (Q: assertion) :=
  forall s, P s -> exists s', cexec s c (RNormal s') /\ Q s'.

Notation "⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈" := (Triple P c Q) (at level 90, c at next level).


Lemma Triple_skip: forall P, 
  ⦇⦇ P ⦈⦈ SKIP ⦇⦇ P ⦈⦈.
Proof.
  unfold Triple; intros. exists s. split; [ apply cexec_skip | exact H ].
Qed.

Lemma Triple_assign: forall P x a,
      ⦇⦇ aupdate x a P ⦈⦈ ASSIGN x a ⦇⦇ P ⦈⦈.
Proof.
  unfold Triple, aupdate; intros P x a s PRE.
  exists (update x (aeval a s) s). split; [ apply cexec_assign | exact PRE ].
Qed.

Lemma Triple_seq: forall P Q R c1 c2,
      ⦇⦇ P ⦈⦈ c1 ⦇⦇ Q ⦈⦈ -> ⦇⦇ Q ⦈⦈ c2 ⦇⦇ R ⦈⦈ ->
      ⦇⦇ P ⦈⦈ c1;;c2 ⦇⦇ R ⦈⦈.
Proof.
  unfold Triple; intros P Q R c1 c2 H1 H2 s PRE.
  destruct (H1 s PRE) as (sm & EXEC1 & QSx).
  destruct (H2 sm QSx) as (sf & EXEC2 & RSf).
  exists sf. split; [ apply cexec_seq with sm; assumption | exact RSf ].
Qed.

Lemma Triple_ifthenelse: forall P Q b c1 c2,
      ⦇⦇ atrue b //\\ P ⦈⦈ c1 ⦇⦇ Q ⦈⦈ ->
      ⦇⦇ afalse b //\\ P ⦈⦈ c2 ⦇⦇ Q ⦈⦈ ->
      ⦇⦇ P ⦈⦈ IF b THEN c1 ELSE c2 END ⦇⦇ Q ⦈⦈.
Proof.
  unfold Triple, aand, atrue, afalse; intros P Q b c1 c2 H1 H2 s PRE.
  destruct (beval b s) eqn:Hb.
  - destruct (H1 s (conj Hb PRE)) as (s' & EXEC & QS').
    exists s'. split; [ | exact QS' ].
    apply cexec_choice_left.
    apply cexec_seq with s; [ apply cexec_assume; exact Hb | exact EXEC ].
  - destruct (H2 s (conj Hb PRE)) as (s' & EXEC & QS').
    exists s'. split; [ | exact QS' ].
    apply cexec_choice_right.
    apply cexec_seq with s;
      [ apply cexec_assume; cbn; rewrite Hb; reflexivity | exact EXEC ].
Qed.

Lemma Triple_consequence: forall P Q P' Q' c,
      ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈ ->
      P' -->> P ->
      Q -->> Q' ->
      ⦇⦇ P' ⦈⦈ c ⦇⦇ Q' ⦈⦈.
Proof.
  unfold Triple, aimp; intros P Q P' Q' c HT HP'P HQQ' s PRE.
  destruct (HT s (HP'P s PRE)) as (s' & EXEC & QS').
  exists s'. split; [ exact EXEC | apply HQQ', QS' ].
Qed.


Lemma Triple_while: forall P variant b c,
  (forall v,
     ⦇⦇ P //\\ atrue b //\\ aequal variant v ⦈⦈
     c
     ⦇⦇ P //\\ alessthan variant v ⦈⦈)
  ->
     ⦇⦇ P ⦈⦈ WHILE b DO c END ⦇⦇ P //\\ afalse b ⦈⦈.
Proof.
  unfold Triple, aand, atrue, afalse, aequal, alessthan.
  intros P variant b c H s0 PRE0.
  (* Helper: from any P-state with non-negative variant, the iterated body
     [(ASSUME b ;; c) ★] terminates in a state where [P] still holds and [b]
     is false.  Proved by induction on a nat upper bound for [Z.to_nat] of
     the variant. *)
  assert (HELP: forall n s,
              0 <= aeval variant s ->
              (Z.to_nat (aeval variant s) <= n)%nat ->
              P s ->
              exists sf,
                cexec s (CSTAR (ASSUME b ;; c)) (RNormal sf) /\
                P sf /\ beval b sf = false).
  { induction n as [|n IH]; intros s Hvnn Hn PS.
    - (* n = 0: with 0 <= variant and Z.to_nat variant <= 0 we get variant = 0 *)
      assert (Hzero : aeval variant s = 0).
      { destruct (aeval variant s) as [|p|p]; lia. }
      destruct (beval b s) eqn:Hb.
      + (* b = true: H with v=0 demands [0 <= variant s1 < 0], contradiction *)
        destruct (H 0 s) as (s1 & _ & _ & (Hv0 & Hlt)).
        { split; [ exact PS | split; [ exact Hb | exact Hzero ] ]. }
        lia.
      + exists s. split; [ apply cexec_cstar_done | split; assumption ].
    - destruct (beval b s) eqn:Hb.
      + destruct (H (aeval variant s) s) as (s1 & EXEC1 & PS1 & (Hv0 & Hlt)).
        { split; [ exact PS | split; [ exact Hb | reflexivity ] ]. }
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
  (* Main argument: case-split on initial b. The b-true case takes one
     iteration first so that the variant becomes non-negative before HELP. *)
  destruct (beval b s0) eqn:Hb.
  - destruct (H (aeval variant s0) s0) as (s1 & EXEC1 & PS1 & (Hv0 & _)).
    { split; [ exact PRE0 | split; [ exact Hb | reflexivity ] ]. }
    destruct (HELP (Z.to_nat (aeval variant s1)) s1 Hv0 (le_n _) PS1)
      as (sf & EXEC_LOOP & PSf & Hbf).
    exists sf. split.
    + apply cexec_seq with sf.
      * eapply cexec_cstar_step_ok.
        -- apply cexec_seq with s0;
             [ apply cexec_assume; exact Hb | exact EXEC1 ].
        -- exact EXEC_LOOP.
      * apply cexec_assume; cbn; rewrite Hbf; reflexivity.
    + split; [ exact PSf | exact Hbf ].
  - exists s0. split.
    + apply cexec_seq with s0.
      * apply cexec_cstar_done.
      * apply cexec_assume; cbn; rewrite Hb; reflexivity.
    + split; [ exact PRE0 | exact Hb ].
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
          specialize (IHbody (aeval a x) x (RNormal y) STEP (conj HP eq_refl)).
          cbn in IHbody. destruct IHbody as [_ HINV_y]. exact HINV_y.
      + (* RError: same chain up to the erroring iteration *)
        apply cexec_cstar_err_iff in EXEC.
        destruct EXEC as (sm & STAR & ERR).
        assert (HINV_sm : INV sm).
        { clear ERR. revert HP.
          induction STAR as [|x y z STEP STAR' IHSTAR']; intros HP.
          - exact HP.
          - apply IHSTAR'. unfold step_iter in STEP.
            specialize (IHbody (aeval a x) x (RNormal y) STEP (conj HP eq_refl)).
            cbn in IHbody. destruct IHbody as [_ HINV_y]. exact HINV_y. }
        specialize (IHbody (aeval a sm) sm (RError s') ERR
                          (conj HINV_sm eq_refl)).
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