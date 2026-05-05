From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality.
From IncLogic Require Import Imp Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.


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


(** The rules of weak Hoare logic *)

(** Here are the base rules for Hoare logic.
    They define a relation [Hoare P c Q], where
-   [P] is the precondition, assumed to hold "before" executing [c];
-   [c] is the program or program fragment we reason about;
-   [Q] is the postcondition, guaranteed to hold "after" executing [c].

  This is a "weak" logic, meaning that it does not guarantee termination
  of the command [c].  What is guaranteed is that if [c] terminates,
  then its final store satisfies postcondition [Q]. *)

Inductive Hoare: assertion -> com -> assertion -> Prop :=
| Hoare_skip: forall P,
  (* ------------------ *)
  Hoare P SKIP P
| Hoare_assign: forall P x a,
  (* ------------------------------ *)
    Hoare (aupdate x a P) (ASSIGN x a) P
| Hoare_seq: forall P Q R c1 c2,
    Hoare P c1 Q ->
    Hoare Q c2 R ->
    (* ------------------ *)
    Hoare P (c1 ;; c2) R
| Hoare_choice: forall P Q c1 c2,
    Hoare P c1 Q ->
    Hoare P c2 Q ->
    (* ---------------------- *)
    Hoare P (c1 ⊕ c2) Q
| Hoare_consequence: forall P Q P' Q' c,
    Hoare P c Q ->
    P' -->> P ->
    Q -->> Q' ->
    (* -------------*)
    Hoare P' c Q'
| Hoare_cstar: forall INV c, 
    Hoare INV c INV ->
    (* ------------------ *)
    Hoare INV (CSTAR c) INV.

Reserved Notation "'hoare' p '<<' c '>>' q"
  (at level 40, p at level 39, c at level 99, q at level 39).

Inductive HoareRes: assertion -> com -> postassertion -> Prop :=
| Hoare_skip_r: forall P,
  (* ------------------ *)
  hoare P << SKIP >> P
| Hoare_assign_r: forall P x a,
  (* ------------------------------ *)
    hoare (aupdate x a P) << ASSIGN x a >> P
| Hoare_seq_ok: forall P Q R c1 c2,
    hoare P << c1 >> Q ->
    hoare Q << c2 >> R ->
    (* ------------------ *)
    hoare P << (c1 ;; c2) >> R
| Hoare_seq_err: forall P c1 c2,
    HoareRes P c1 (fun r => match r with RError => True | _ => False end) ->
    (* ------------------ *)
    HoareRes P (c1 ;; c2) (fun r => match r with RError => True | _ => False end)
| Hoare_consequence_res: forall P Q P' Q' c,
    hoare P << c >> Q ->
    P' -->> P ->
    Q -->> Q' ->
    (* -------------*)
    hoare P' << c >> Q'
| Hoare_choice_res: forall P Q c1 c2,
    hoare P << c1 >> Q ->
    hoare P << c2 >> Q ->
    (* ---------------------- *)
    hoare P << c1 ⊕ c2 >> Q
| Hoare_cstar_ress: forall INV c, 
    hoare INV << c >> INV ->
    (* ------------------ *)
    hoare INV << CSTAR c >> INV
where "'hoare' p '<<' c '>>' q" :=
  (HoareRes p c (fun r => match r with
                          | RNormal s => q s
                          | RError => False
                          end)).


Lemma Hoare_consequence_pre: forall P P' Q c,
      hoare P << c >> Q ->
      P' -->> P ->
      hoare P' << c >> Q.
Proof.
  intros. apply Hoare_consequence_res with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_consequence_post: forall P Q Q' c,
      hoare P << c >> Q ->
      Q -->> Q' ->
      hoare P << c >> Q'.
Proof.
  intros. apply Hoare_consequence_res with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Example Hoare_swap_xy: forall m n,
  hoare (aequal (VAR "x") m //\\ aequal (VAR "y") n)
        << swap_xy >>
        (aequal (VAR "x") n //\\ aequal (VAR "y") m).
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

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

Lemma triple_skip: forall P,
     {{P}} SKIP {{P}}.
Proof.
  unfold triple; intros. exists s. inversion H; subst. auto.
Qed.


Lemma triple_assign: forall P x a,
      {{aupdate x a P}} ASSIGN x a {{P}}.
Proof.
  unfold triple, aupdate; intros P x a s r EXEC PRE.
  inversion EXEC; subst.
  eexists. split; [ reflexivity | exact PRE ].
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      {{P}} c1 {{Q}} ->
      {{Q}} c2 {{R}} ->
      {{P}} c1;;c2 {{R}}.
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
    | E1 : cexec s c1 RError |- _ =>
      destruct (H1 s RError E1 PRE) as (? & EQ & _); discriminate
    end.
  - (* cexec_seq_error_right: c1 normal, c2 errors *)
    match goal with
    | E1 : cexec s c1 (RNormal ?s'),
      E2 : cexec ?s' c2 RError |- _ =>
      destruct (H1 s (RNormal s') E1 PRE) as (sx & EQ1 & QSx);
      inversion EQ1; subst sx;
      destruct (H2 s' RError E2 QSx) as (? & EQ & _); discriminate
    end.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      {{atrue b //\\ P}} c1 {{Q}} ->
      {{afalse b //\\ P}} c2 {{Q}} ->
      {{P}} IF b THEN c1 ELSE c2 END {{Q}}.
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
      match goal with EA : cexec s (ASSUME b) RError |- _ => inversion EA end.
    + (* SEQ error right *)
      match goal with EA : cexec s (ASSUME b) _ |- _ => inversion EA; subst end.
      eapply H1; eauto.
  - (* choice_right: cexec s (ASSUME (NOT b) ;; c2) r *)
    match goal with E : cexec s (ASSUME (NOT b) ;; c2) r |- _ => inversion E; subst end.
    + match goal with EA : cexec s (ASSUME (NOT b)) _ |- _ => inversion EA; subst end.
      eapply H2; eauto.
      split; [ apply Bool.negb_true_iff; assumption | exact PRE ].
    + match goal with EA : cexec s (ASSUME (NOT b)) RError |- _ => inversion EA end.
    + match goal with EA : cexec s (ASSUME (NOT b)) _ |- _ => inversion EA; subst end.
      eapply H2; eauto.
      split; [ apply Bool.negb_true_iff; assumption | exact PRE ].
Qed.

(** Helper: [P] is preserved across any number of iterations of the loop body
    [(ASSUME b ;; c)] when [c] preserves [P] under the [b]-true precondition. *)
Lemma triple_while_invariant: forall P b c s s',
  {{atrue b //\\ P}} c {{P}} ->
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
    \/ (cexec s c1 RError /\ r = RError)
    \/ (exists sm, cexec s c1 (RNormal sm) /\ cexec sm c2 RError /\ r = RError).
Proof.
  intros c1 c2 s r EXEC.
  inversion EXEC; subst.
  - left. eauto.
  - right. left. auto.
  - right. right. eauto.
Qed.

Lemma triple_while: forall P b c,
      {{atrue b //\\ P}} c {{P}} ->
      {{P}} WHILE b DO c END {{afalse b //\\ P}}.
Proof.
  unfold triple, aand, atrue, afalse.
  intros P b c H s r EXEC PRE.
  (* WHILE b DO c END = ((ASSUME b ;; c) ★) ;; ASSUME (NOT b) *)
  apply cexec_seq_inv in EXEC.
  destruct EXEC as
    [ (sm & sf & EI & EA & ->)
    | [ (EI & ->) | (sm & EI & EA & ->) ] ].
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
      | [ (EA & _) | (sx & EA & EC & _) ] ].
    + (* normal yields RNormal, can't equal RError *)
      discriminate EQbad.
    + (* ASSUME b errors: impossible *)
      inversion EA.
    + (* ASSUME b ok, c errors: contradicts H. EA : cexec sm (ASSUME b) (RNormal sx) *)
      inversion EA; subst sx.   (* substitute sx := sm only *)
      destruct (H sm RError EC) as (? & EQc & _);
        [ split; assumption | discriminate ].
  - (* SEQ error right: ASSUME (NOT b) errors. Impossible. *)
    inversion EA.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      {{P}} c {{Q}} ->
      P' -->> P ->
      Q -->> Q' ->
      {{P'}} c {{Q'}}.
Proof.
  unfold triple, aimp; intros P Q P' Q' c HT P'P QQ' s r EXEC PRE.
  destruct (HT s r EXEC (P'P s PRE)) as (s' & EQ & QSx).
  exists s'. split; [ exact EQ | apply QQ', QSx ].
Qed.

(** Strong Hoare triples *)

Definition Triple (P: assertion) (c: com) (Q: assertion) :=
  forall s, P s -> exists s', cexec s c (RNormal s') /\ Q s'.

Notation "{{{ P }}} c {{{ Q }}}" := (Triple P c Q) (at level 90, c at next level).
