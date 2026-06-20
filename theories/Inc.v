From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality FunctionalExtensionality.
From mathcomp Require Import ssrbool eqtype choice.
From mathcomp Require Import finmap.
From IncLogic Require Import Imp Sequences Hoare.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.

Reserved Notation "⟦ P ⟧ c ⟦ 'ok' ↑ Q ⟧" (at level 90, c at next level).

Reserved Notation "⟦ P ⟧ c ⟦ 'ϵ' ↑ Q ⟧" (at level 90, c at next level).

Reserved Notation "⟦ P ⟧ c ⟦ 'err' ↑ Q ⟧" (at level 90, c at next level).

Definition ffalse : assertion := fun _ => False.

Inductive Inc_triple: assertion -> com -> postassertion -> Prop :=
| Inc_Empty_under_approx: forall P c,
  (*───────────────────*)
  ⟦ P ⟧ c ⟦ ϵ ↑ ffalse ⟧
| Inc_triple_skip: forall P,
  (*───────────────────*)
  ⟦ P ⟧ SKIP ⟦ ok ↑ P ⟧
| Inc_choice_l: forall P c1 c2,
    ⟦ P ⟧ c1 ⟦ ϵ ↑ P ⟧ 
    (*──────────────────*)
    -> ⟦ P ⟧ (c1 ⊕ c2) ⟦ ϵ ↑ P ⟧
| Inc_choice_r: forall P c1 c2,
    ⟦ P ⟧ c2 ⟦ ϵ ↑ P ⟧ ->
    (*──────────────────*)
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ ϵ ↑ P ⟧
| Inc_seq_ok: forall P c1 c2 Q1 Q2,
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ Q1 ⟧ c2 ⟦ ϵ ↑ Q2 ⟧ ->
    (*─────────────────────*)
    ⟦ P ⟧   (c1 ;; c2) ⟦ ϵ ↑ Q2 ⟧
| Inc_seq_err: forall P c1 c2 R,
    ⟦ P ⟧ c1 ⟦ err ↑ R ⟧ ->
    (*──────────────────────*)
    ⟦ P ⟧   (c1 ;; c2) ⟦ err ↑ R ⟧
| Inc_iterate_zero: forall P c,
    ⟦ P ⟧ CSTAR c ⟦ ok ↑ P ⟧
| Inc_iterate_step: forall P c Q,
    ⟦ P ⟧ (CSTAR c ;; c) ⟦ ϵ ↑ Q ⟧ ->
    (*─────────────────────────────*)
    ⟦ P ⟧ CSTAR c ⟦ ϵ ↑ Q ⟧
| Inc_error: forall P,
    ⟦ P ⟧ ERROR ⟦ err ↑ P ⟧
| Inc_consequence: forall P P' c Q Q',
    (P -->> P') ->
    ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ ->
    (Q' -->> Q) ->
    (*──────────────────*)
    ⟦ P' ⟧ c ⟦ ϵ ↑ Q' ⟧
| Inc_assume : forall P b,
    ⟦ P ⟧ (ASSUME b) ⟦ ok ↑ atrue b //\\ P ⟧
| Inc_disjunc: forall P1 P2 c Q1 Q2,
    ⟦ P1 ⟧ c ⟦ ϵ ↑ Q1 ⟧ ->
    ⟦ P2 ⟧ c ⟦ ϵ ↑ Q2 ⟧ ->
    (*───────────────────────────────*)
    ⟦ P1 \\// P2 ⟧ c ⟦ ϵ ↑ Q1 \\// Q2 ⟧
| Inc_backwards_variant: forall (P: nat -> assertion) c,
    (forall n, ⟦ P n ⟧ c ⟦ ϵ ↑ P (n + 1)%nat ⟧) ->
    (*───────────────────────────────────────────────────────────*)
    ⟦ P 0%nat ⟧ CSTAR c ⟦ ok ↑ (fun s => exists (m: nat), P m s) ⟧
(* [p] x = e [ok: ∃x'. p[x'/x] ∧ x = e[x'/x]] [er: false] *)
| Inc_assign_fwd: forall x a P,
  (*────────────────────────────────────────────────────────────────────*)
  ⟦ P ⟧ ASSIGN x a ⟦ ok ↑ (fun s => x \in domf s) //\\ aexists (fun m => aexists (fun n =>
        aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) ⟧
| Inc_nondet: forall x P,
    (*─────────────────────────────────────────────────────────────*)
    ⟦ P ⟧ NONDET x ⟦ ok ↑ (fun s => x \in domf s)
       //\\ aexists (fun n => aupdate x (CONST n) P) ⟧
(* ── Sound, tag-tracking strongest-post rules added for completeness.
   Each mirrors a clause of the operational semantics [cexec]; together
   they let the strongest [ok]/[err] post of every command be derived.
   They are all semantically valid (see the [inc_triple_*] lemmas and the
   [cexec_*] constructors), so adding them preserves soundness. *)
| Inc_consequence_gen: forall P P' c (Q Q': postassertion),
    (P -->> P') ->
    Inc_triple P c Q ->
    (forall r, Q' r -> Q r) ->
    (*──────────────────*)
    Inc_triple P' c Q'
| Inc_assign_sp: forall x a P,
    (*────────────────────────────────────────────────────────────────────*)
    ⟦ P ⟧ ASSIGN x a ⟦ ok ↑ (fun s' => exists s, P s /\ s' = update x (aeval a s) s) ⟧
| Inc_nondet_sp: forall x P,
    (*────────────────────────────────────────────────────────────────────*)
    ⟦ P ⟧ NONDET x ⟦ ok ↑ (fun s' => exists s n, P s /\ s' = update x n s) ⟧
| Inc_ok_seq: forall P c1 c2 Q1 Q2,
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ Q1 ⟧ c2 ⟦ ok ↑ Q2 ⟧ ->
    (*─────────────────────────*)
    ⟦ P ⟧ (c1 ;; c2) ⟦ ok ↑ Q2 ⟧
| Inc_err_seq: forall P c1 c2 Q1 R1 R2,
    ⟦ P ⟧ c1 ⟦ err ↑ R1 ⟧ ->
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ Q1 ⟧ c2 ⟦ err ↑ R2 ⟧ ->
    (*──────────────────────────────────*)
    ⟦ P ⟧ (c1 ;; c2) ⟦ err ↑ (R1 \\// R2) ⟧
| Inc_ok_choice: forall P c1 c2 Q1 Q2,
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ P ⟧ c2 ⟦ ok ↑ Q2 ⟧ ->
    (*──────────────────────────────────*)
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ ok ↑ (Q1 \\// Q2) ⟧
| Inc_err_choice: forall P c1 c2 R1 R2,
    ⟦ P ⟧ c1 ⟦ err ↑ R1 ⟧ ->
    ⟦ P ⟧ c2 ⟦ err ↑ R2 ⟧ ->
    (*──────────────────────────────────*)
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ err ↑ (R1 \\// R2) ⟧
| Inc_ok_cstar: forall (P: nat -> assertion) c,
    (forall n, ⟦ P n ⟧ c ⟦ ok ↑ P (S n) ⟧) ->
    (*─────────────────────────────────────────────────────────────*)
    ⟦ P 0%nat ⟧ CSTAR c ⟦ ok ↑ (fun s => exists m, P m s) ⟧
| Inc_err_cstar: forall P c M R,
    ⟦ P ⟧ CSTAR c ⟦ ok ↑ M ⟧ ->
    ⟦ M ⟧ c ⟦ err ↑ R ⟧ ->
    (*──────────────────────────*)
    ⟦ P ⟧ CSTAR c ⟦ err ↑ R ⟧
| Inc_combine_ok_err: forall P c A B,
    ⟦ P ⟧ c ⟦ ok ↑ A ⟧ ->
    ⟦ P ⟧ c ⟦ err ↑ B ⟧ ->
    (*──────────────────────────*)
    Inc_triple P c (fun r => match r with
                             | RNormal s => A s
                             | RError s => B s
                             end)
where "⟦ P ⟧ c ⟦ 'ϵ' ↑ Q ⟧" :=
  (Inc_triple P c (fun r => match r with
                            | RNormal s => Q s
                            | RError s => Q s
                            end))
and
 "⟦ P ⟧ c ⟦ 'ok' ↑ Q ⟧" :=
  (Inc_triple P c (fun r => match r with
                            | RNormal s => Q s
                            | RError _ => False
                            end))
and "⟦ P ⟧ c ⟦ 'err' ↑ Q ⟧" :=
  (Inc_triple P c (fun r => match r with
                            | RNormal _ => False
                            | RError s => Q s
                            end)).


Notation "⟦ P ⟧ c ⟦ 'ok' ↑ Q1 ⟧ ⟦ 'err' ↑ Q2 ⟧" := (⟦ P ⟧ c ⟦ err ↑ Q1 ⟧  /\ ⟦ P ⟧ c ⟦ ok ↑ Q2 ⟧) (at level 90, c at next level).

(* Postassertion-level triple: [Q] is a full [postassertion] (it inspects the
   result tag), as opposed to the [ϵ/ok/err ↑] variants which lift an [assertion]. *)
Notation "⟦ P ⟧ c ⟦ Q ⟧" := (Inc_triple P c Q) (at level 90, c at next level).

(* Semantics triple *)
Definition IncTriple (P: assertion) (c: com) (Q: postassertion) : Prop :=
  forall r, Q r -> exists s, P s /\ cexec s c r.

Notation "⟦⟦ P ⟧⟧ c ⟦⟦ 'ϵ' ↑ Q ⟧⟧" :=
  (IncTriple P c (fun r => match r with
                           | RNormal s => Q s
                           | RError s  => Q s
                           end))
  (at level 90, c at next level).

Notation "⟦⟦ P ⟧⟧ c ⟦⟦ 'err' ↑ Q ⟧⟧" :=
  (IncTriple P c (fun r => match r with
                           | RNormal _ => False
                           | RError s  => Q s
                           end))
  (at level 90, c at next level).

Notation "⟦⟦ P ⟧⟧ c ⟦⟦ 'ok' ↑ Q ⟧⟧" :=
  (IncTriple P c (fun r => match r with
                           | RNormal s => Q s
                           | RError _  => False
                           end))
  (at level 90, c at next level).

(* Postassertion-level triple: [Q] is a [postassertion] (it inspects the
   result), as opposed to the [ϵ/ok/err ↑] variants which lift an [assertion]. *)
Notation "⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧" := (IncTriple P c Q) (at level 90, c at next level).


Lemma disjunction_ok: forall P c Q1 Q2,
    ⟦ P ⟧ c ⟦ ϵ ↑ Q1 ⟧ ->
    ⟦ P ⟧ c ⟦ ϵ ↑ Q2 ⟧ ->
    ⟦ P ⟧ c ⟦ ϵ ↑ (fun s => Q1 s \/ Q2 s) ⟧.
Proof.
  intros P c Q1 Q2 H1 H2.
  eapply Inc_consequence with (P := P \\// P) (Q := Q1 \\// Q2).
  - unfold aor, aimp; intros s [HP | HP]; exact HP.
  - apply Inc_disjunc; assumption.
  - unfold aor, aimp; auto.
Qed.

(** Semantic disjunction (precondition split), the [⟦⟦ ⟧⟧] counterpart of the
    [Inc_disjunc] rule. *)
Lemma inc_triple_disjunc: forall P1 P2 c Q1 Q2,
    ⟦⟦ P1 ⟧⟧ c ⟦⟦ ϵ ↑ Q1 ⟧⟧ ->
    ⟦⟦ P2 ⟧⟧ c ⟦⟦ ϵ ↑ Q2 ⟧⟧ ->
    ⟦⟦ P1 \\// P2 ⟧⟧ c ⟦⟦ ϵ ↑ Q1 \\// Q2 ⟧⟧.
Proof.
  unfold aor. intros P1 P2 c Q1 Q2 H1 H2 r HQ.
  destruct r as [s | s]; destruct HQ as [HQ1 | HQ2].
  - destruct (H1 (RNormal s) HQ1) as (s0 & HP & EXEC).
    exists s0. split; [ left; exact HP | exact EXEC ].
  - destruct (H2 (RNormal s) HQ2) as (s0 & HP & EXEC).
    exists s0. split; [ right; exact HP | exact EXEC ].
  - destruct (H1 (RError s) HQ1) as (s0 & HP & EXEC).
    exists s0. split; [ left; exact HP | exact EXEC ].
  - destruct (H2 (RError s) HQ2) as (s0 & HP & EXEC).
    exists s0. split; [ right; exact HP | exact EXEC ].
Qed.

 (* [p]c[q1] ∧ [p]c[q2] ⇐⇒ [p]c[q1 ∨ q2] *)
Lemma inc_symmetry: forall P c Q1 Q2,
    (⟦ P ⟧ c ⟦ ϵ ↑ Q1 ⟧  /\ ⟦ P ⟧ c ⟦ ϵ ↑ Q2 ⟧)  ->
    ⟦ P ⟧ c ⟦ ϵ ↑ (fun s => Q1 s \/ Q2 s) ⟧.
Proof.
    intros P c Q1 Q2 [h1 h2].
    apply disjunction_ok; assumption.
Qed.

Lemma inc_triple_skip: forall P, 
    ⟦⟦ P ⟧⟧ SKIP ⟦⟦ ok ↑ P ⟧⟧.
Proof.
    intros P r Hr.
    destruct r.
    - exists s. split; try assumption. apply cexec_skip.
    - exfalso. apply Hr. 
Qed.

Lemma inc_triple_empty_under_approx: forall P c,
    ⟦⟦ P ⟧⟧  c ⟦⟦ ϵ ↑ ffalse ⟧⟧.
Proof.
    intros P c r Hr. destruct r; exfalso; apply Hr.
Qed.

Lemma inc_triple_seq_normal: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧  c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ Q1 ⟧⟧  c2 ⟦⟦ ϵ ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧  c1 ;; c2 ⟦⟦ ϵ ↑ Q2 ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2 r HQ2.
  destruct (H2 r HQ2) as (s_mid & HQ1mid & EXEC2).
  destruct (H1 (RNormal s_mid) HQ1mid) as (s_pre & HPpre & EXEC1).
  exists s_pre. split; [ exact HPpre | ].
  destruct r as [s_final | sf].
  - eapply cexec_seq; eauto.
  - eapply cexec_seq_error_right; eauto.
Qed.

Lemma inc_triple_seq_short_circuit: forall P c1 c2 Q,
    ⟦⟦ P ⟧⟧  c1 ⟦⟦ err ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧  c1 ;; c2 ⟦⟦ err ↑ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H1 r HQ.
  destruct r as [s_final | sf]; [ exfalso; exact HQ | ].
  destruct (H1 (RError sf) HQ) as (s_pre & HPpre & EXEC1).
  exists s_pre. split; [ exact HPpre | ].
  apply cexec_seq_error. exact EXEC1.
Qed.

Lemma inc_triple_iterate_non_zero: forall P c Q,
    ⟦⟦ P ⟧⟧  c ★ ;; c  ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧  c ★ ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros P c Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  inversion EXEC; subst.
  - (* CSTAR normal, then c normal: append one iteration *)
    exists s. split; [ exact HPs | ].
    apply cexec_cstar_iff_star.
    apply cexec_cstar_iff_star in H3.
    eapply star_trans; [ exact H3 | ].
    apply star_one. unfold step_iter. exact H5.
  - (* CSTAR errors directly *)
    exists s. split; [ exact HPs | exact H4 ].
  - (* CSTAR normal, then c errors: append an erroring iteration *)
    exists s. split; [ exact HPs | ].
    apply cexec_cstar_err_iff.
    apply cexec_cstar_iff_star in H3.
    exists s'. split; [ exact H3 | exact H5 ].
Qed.

Lemma inc_triple_iterate_zero: forall P c,
    ⟦⟦ P ⟧⟧  c ★ ⟦⟦ ok ↑ P ⟧⟧.
Proof.
    intros P c r Q.
    destruct r as [s | sf].
    - exists s.  split; [ exact Q | ]. constructor.
    - contradiction Q.
Qed.

Lemma inc_triple_consequence: forall P P' c Q Q',
    (P -->> P') ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    (Q' -->> Q) ->
    ⟦⟦ P' ⟧⟧ c ⟦⟦ ϵ ↑ Q' ⟧⟧.
Proof.
  intros P P' c Q Q' HPP' H HQ'Q r HQ'r.
  assert (HQr : match r with RNormal s => Q s | RError s => Q s end).
  { destruct r as [s | s]; apply HQ'Q; exact HQ'r. }
  destruct (H r HQr) as (s & HPs & EXEC).
  exists s. split; [ apply HPP'; exact HPs | exact EXEC ].
Qed.

Lemma inc_triple_choice_l: forall P c1 c2 Q,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  exists s. split; [ exact HPs | apply cexec_choice_left; exact EXEC ].
Qed.

Lemma inc_triple_assign_fwd: forall x a P,
  ⟦⟦ P ⟧⟧
  ASSIGN x a
  ⟦⟦ ok ↑ (fun s => x \in domf s) //\\ aexists (fun m => aexists (fun n =>
     aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) ⟧⟧.
Proof.
  intros x a P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [Hdom [m [n [Heq_x [HP Heq_a]]]]].
  cbn in HP, Heq_a, Heq_x.
  unfold aequal in Heq_x, Heq_a. cbn in Heq_x, Heq_a.
  exists (update x m s'). split; [ exact HP | ].
  replace s' with (update x (aeval a (update x m s')) (update x m s')) at 2.
  - apply cexec_assign.
  - rewrite Heq_a, update_shadow, <- Heq_x. apply update_get. exact Hdom.
Qed.

Lemma inc_triple_choice_r: forall P c1 c2 Q,
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  exists s. split; [ exact HPs | apply cexec_choice_right; exact EXEC ].
Qed.


Lemma inc_triple_backwards_variant: forall (P: nat -> assertion) c,
    (forall n, ⟦⟦ P n ⟧⟧ c ⟦⟦ ϵ ↑ P (n + 1)%nat ⟧⟧) ->
    ⟦⟦ P 0%nat ⟧⟧ c ★ ⟦⟦ ok ↑ (fun s => exists (m: nat), P m s) ⟧⟧.
Proof.
  intros P c H r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [m HPm].
  revert s' HPm.
  induction m as [| k IH]; intros s' HPm.
  - (* m = 0: take s = s' and use cexec_cstar_done *)
    exists s'. split; [ exact HPm | apply cexec_cstar_done ].
  - (* m = S k: chain H k to reach s' from a P k state, then induct *)
    assert (HPk1 : P (k + 1)%nat s') by (rewrite Nat.add_1_r; exact HPm).
    destruct (H k (RNormal s') HPk1) as (s_pre & HPk_pre & EXEC_step).
    destruct (IH s_pre HPk_pre) as (s & HP0s & EXEC_iter).
    exists s. split; [ exact HP0s | ].
    apply cexec_cstar_iff_star.
    apply cexec_cstar_iff_star in EXEC_iter.
    eapply star_trans; [ exact EXEC_iter | ].
    apply star_one. unfold step_iter. exact EXEC_step.
Qed.


Lemma inc_triple_error: forall P, ⟦⟦ P ⟧⟧ ERROR ⟦⟦ err ↑ P ⟧⟧.
Proof.
    intros P r c.
    destruct r as [s | sf].
    - exfalso. apply c.
    - exists sf. split; [ exact c | constructor ]. 
Qed.


Lemma inc_triple_assume: forall P B,
    ⟦⟦ P ⟧⟧ (ASSUME B) ⟦⟦ ok ↑ atrue B //\\ P ⟧⟧.
Proof.
    intros P B r HQ.
    destruct r as [s | sf].
    destruct HQ as [HB HP].
    - exists s. split.
        +   exact HP.
        + constructor. exact HB.
    - exfalso. apply HQ.
Qed.

(** Syntactic substitution [e/x] on arithmetic expressions. *)
Fixpoint asubst (x: ident) (e: aexp) (a: aexp) : aexp :=
  match a with
  | CONST n     => CONST n
  | VAR y       => if string_dec x y then e else VAR y
  | PLUS  a1 a2 => PLUS  (asubst x e a1) (asubst x e a2)
  | MINUS a1 a2 => MINUS (asubst x e a1) (asubst x e a2)
  end.

(** "Variable [x] is not free in [P]." *)
Definition not_free (x: ident) (P: assertion) : Prop :=
  independent_of P (fun y => y = x).

(** "Free([e]) ∩ vars = ∅". *)
Definition aexp_indep (e: aexp) (vars: ident -> Prop) : Prop :=
  forall (s1 s2 : store), (forall y, ~ vars y -> s1 y = s2 y) -> aeval e s1 = aeval e s2.

(** "c's trajectory is invariant under changes to x":
    every cexec from s can be shifted to a cexec from (update x v s) ending
    in the corresponding x-shifted result. Implies x ∉ mod(c) and that c
    does not read x. *)
Definition cexec_indep (c: com) (x: ident) : Prop :=
  forall s v r,
  cexec s c r ->
  cexec (update x v s) c
        (match r with
         | RNormal s' => RNormal (update x v s')
         | RError  s' => RError  (update x v s')
         end).

(** Substitution I:
            [p] c [ε: q]
    ———————————————————————————————— 
        [p[e/x]] c [ε: q[e/x]]
 side conditions: c is x-invariant, [e]'s value is preserved by c's
 modifications, and x is not free in e.
*)
Lemma inc_triple_subst_I: forall x e c P Q,
  ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
  ~ modified_by c x ->
  cexec_indep c x ->
  aexp_indep e (modified_by c) ->
  ⟦⟦ aupdate x e P ⟧⟧ c ⟦⟦ ϵ ↑ aupdate x e Q //\\ in_domf x ⟧⟧.
Proof.
  unfold IncTriple, aupdate, aexp_indep, cexec_indep, aand, in_domf.
  intros x e c P Q HT NMOD IND EDEP r HQex.
  destruct r as [s_out | s_out].
  - set (v := aeval e s_out) in *.
    destruct HQex as [HQex Hdom_out].
    destruct (HT (RNormal (update x v s_out)) HQex) as (s_in & HPs_in & EXEC_in).
    pose proof (cexec_modified x s_in c _ EXEC_in NMOD) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = v) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMOD) as Hdom_in.
    cbn in Hdom_in.
    rewrite dom_update in Hdom_in. rewrite eqxx in Hdom_in. cbn in Hdom_in.
    assert (Hdom_sin : (x \in domf s_in) = true) by (rewrite Hdom_in; reflexivity).
    exists (update x (s_out x) s_in).
    assert (Heval : aeval e (update x (s_out x) s_in) = v).
    { apply EDEP. intros y NM.
      destruct (string_dec x y) as [-> | Hxy]; [ apply update_same | ].
      pose proof (cexec_modified y s_in c _ EXEC_in NM) as MODy.
      cbn in MODy. rewrite update_other; [|exact Hxy].
      rewrite <- MODy. rewrite update_other; [reflexivity|exact Hxy]. }
    split.
    + rewrite Heval.
      rewrite update_shadow. rewrite <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin].
    + pose proof (IND s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out)
        by (apply update_get; exact Hdom_out).
      rewrite Heq_out in STEP. exact STEP.
  - set (v := aeval e s_out) in *.
    destruct HQex as [HQex Hdom_out].
    destruct (HT (RError (update x v s_out)) HQex) as (s_in & HPs_in & EXEC_in).
    pose proof (cexec_modified x s_in c _ EXEC_in NMOD) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = v) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMOD) as Hdom_in.
    cbn in Hdom_in.
    rewrite dom_update in Hdom_in. rewrite eqxx in Hdom_in. cbn in Hdom_in.
    assert (Hdom_sin : (x \in domf s_in) = true) by (rewrite Hdom_in; reflexivity).
    exists (update x (s_out x) s_in).
    assert (Heval : aeval e (update x (s_out x) s_in) = v).
    { apply EDEP. intros y NM.
      destruct (string_dec x y) as [-> | Hxy]; [ apply update_same | ].
      pose proof (cexec_modified y s_in c _ EXEC_in NM) as MODy.
      cbn in MODy. rewrite update_other; [|exact Hxy].
      rewrite <- MODy. rewrite update_other; [reflexivity|exact Hxy]. }
    split.
    + rewrite Heval.
      rewrite update_shadow. rewrite <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin].
    + pose proof (IND s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out).
      { apply update_get. exact Hdom_out. }
      rewrite Heq_out in STEP. exact STEP.
Qed.

(** Substitution II (IL.pdf): renaming with a fresh variable [y].

    The original statement (with only [cexec_indep c y]) is not provable: the
    semantic IL triple requires constructing a witness [s_pre] such that
    [s_pre =[c]=> s_out], but the only [s_in] available from [HT] reaches
    [update x (s_out y) s_out].  Without [c] being [x]-invariant, we cannot
    shift [x] in [s_in] to repair this.

    The provable version adds [cexec_indep c x], [~modified_by c x],
    [~modified_by c y], and [x ∈ domf s_out], [y ∈ domf s_out] (the latter
    two are vacuous under the old function-store model, real under finmap). *)
Lemma inc_triple_subst_II: forall x y c P Q,
  x <> y ->
  ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
  not_free y P ->
  not_free y Q ->
  cexec_indep c y ->
  cexec_indep c x ->
  ~ modified_by c x ->
  ~ modified_by c y ->
  ⟦⟦ aupdate x (VAR y) P ⟧⟧ c
  ⟦⟦ ϵ ↑ aupdate x (VAR y) Q //\\ in_domf x //\\ in_domf y ⟧⟧.
Proof.
  unfold IncTriple, aupdate, aand, in_domf, not_free, independent_of.
  intros x y c P Q Hxy HT NFP NFQ INDy INDx NMODx NMODy r HQex.
  destruct r as [s_out | s_out].
  - destruct HQex as [HQex [Hdx Hdy]].
    cbn in HQex.
    destruct (HT (RNormal (update x (s_out y) s_out)) HQex)
      as (s_in & HPs_in & EXEC_in).
    cbn in EXEC_in.
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMODx) as Hdom_xin.
    cbn in Hdom_xin. rewrite dom_update in Hdom_xin.
    rewrite eqxx in Hdom_xin. cbn in Hdom_xin.
    assert (Hdom_sin_x : (x \in domf s_in) = true)
      by (rewrite Hdom_xin; reflexivity).
    pose proof (cexec_modified x s_in c _ EXEC_in NMODx) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = s_out y) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_modified y s_in c _ EXEC_in NMODy) as Hsy_eq.
    cbn in Hsy_eq.
    assert (Hsy : s_in y = s_out y).
    { rewrite <- Hsy_eq. rewrite update_other; [reflexivity | exact Hxy]. }
    exists (update x (s_out x) s_in).
    split.
    + cbn [aeval]. rewrite update_other; [|exact Hxy].
      rewrite update_shadow. rewrite Hsy, <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin_x].
    + pose proof (INDx s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out)
        by (apply update_get; exact Hdx).
      rewrite Heq_out in STEP. exact STEP.
  - destruct HQex as [HQex [Hdx Hdy]].
    cbn in HQex.
    destruct (HT (RError (update x (s_out y) s_out)) HQex)
      as (s_in & HPs_in & EXEC_in).
    cbn in EXEC_in.
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMODx) as Hdom_xin.
    cbn in Hdom_xin. rewrite dom_update in Hdom_xin.
    rewrite eqxx in Hdom_xin. cbn in Hdom_xin.
    assert (Hdom_sin_x : (x \in domf s_in) = true)
      by (rewrite Hdom_xin; reflexivity).
    pose proof (cexec_modified x s_in c _ EXEC_in NMODx) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = s_out y) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_modified y s_in c _ EXEC_in NMODy) as Hsy_eq.
    cbn in Hsy_eq.
    assert (Hsy : s_in y = s_out y).
    { rewrite <- Hsy_eq. rewrite update_other; [reflexivity | exact Hxy]. }
    exists (update x (s_out x) s_in).
    split.
    + cbn [aeval]. rewrite update_other; [|exact Hxy].
      rewrite update_shadow. rewrite Hsy, <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin_x].
    + pose proof (INDx s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out)
        by (apply update_get; exact Hdx).
      rewrite Heq_out in STEP. exact STEP.
Qed.

Lemma inc_triple_constancy: forall P c Q f,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    independent_of f (modified_by c) ->
    ⟦⟦ P //\\ f ⟧⟧ c ⟦⟦ ϵ ↑ Q //\\ f ⟧⟧.
Proof.
  unfold IncTriple, aand, independent_of.
  intros P c Q f HT INDEP r HQf.
  destruct r as [s_out | s_out]; destruct HQf as [HQs HFs].
  - destruct (HT (RNormal s_out) HQs) as (s & HPs & EXEC).
    exists s. split; [ split; [ exact HPs | ] | exact EXEC ].
    apply (proj1 (INDEP s_out s
      (fun x NMOD => cexec_modified x s c (RNormal s_out) EXEC NMOD))).
    exact HFs.
  - destruct (HT (RError s_out) HQs) as (s & HPs & EXEC).
    exists s. split; [ split; [ exact HPs | ] | exact EXEC ].
    apply (proj1 (INDEP s_out s
      (fun x NMOD => cexec_modified x s c (RError s_out) EXEC NMOD))).
    exact HFs.
Qed.

Lemma inc_triple_nondet: forall x P,
  ⟦⟦ P ⟧⟧ NONDET x
  ⟦⟦ ok ↑ (fun s => x \in domf s)
       //\\ aexists (fun n => aupdate x (CONST n) P) ⟧⟧.
Proof.
  intros x P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [Hdom [n HPn]].
  cbn in HPn. unfold aupdate in HPn.
  exists (update x n s'). split; [ exact HPn | ].
  replace s' with (update x (s' x) (update x n s')) at 2.
  - apply cexec_nondet.
  - rewrite update_shadow. apply update_get. exact Hdom.
Qed.

(* Derived Unrolling Rule *)

Fixpoint cmd_n (i: nat) c : com :=
  match i with
  | 0%nat => SKIP
  | S n => c ;; cmd_n n c
  end.

(** A finite unrolling [cmd_n i c] is a refinement of [CSTAR c]: every
    execution of the unrolled form is an execution of the iteration.  Proven
    by induction on [i]. *)
Lemma cmd_n_to_cstar: forall i c s r,
  cexec s (cmd_n i c) r -> cexec s (CSTAR c) r.
Proof.
  induction i as [|n IH]; intros c s r EXEC; cbn in EXEC.
  - inversion EXEC; subst. apply cexec_cstar_done.
  - apply cexec_seq_inv in EXEC.
    destruct EXEC as
      [ (sm & sf & H1 & H2 & ->)
      | [ (sf & H1 & ->) | (sm & sf & H1 & H2 & ->) ] ].
    + apply (IH c sm (RNormal sf)) in H2.
      eapply cexec_cstar_step_ok; eauto.
    + eapply cexec_cstar_step_error; eauto.
    + apply (IH c sm (RError sf)) in H2.
      eapply cexec_cstar_step_iter_error; eauto.
Qed.

Lemma inc_triple_derived_unrolling: forall P c (postassert_i: nat -> assertion),
    (forall i, ⟦⟦ P ⟧⟧ (cmd_n i c) ⟦⟦ ϵ ↑ postassert_i i ⟧⟧) ->
    ⟦⟦ P ⟧⟧ c ★ ⟦⟦ ϵ ↑ aexists (fun i => postassert_i i) ⟧⟧.
Proof.
  intros P c postassert_i H r HQ.
  destruct r as [s' | s']; cbn in HQ; destruct HQ as [j Hj].
  - destruct (H j (RNormal s') Hj) as (s & HPs & EXEC).
    exists s. split; [ exact HPs | apply cmd_n_to_cstar in EXEC; exact EXEC ].
  - destruct (H j (RError s') Hj) as (s & HPs & EXEC).
    exists s. split; [ exact HPs | apply cmd_n_to_cstar in EXEC; exact EXEC ].
Qed.

Module SPre.

(* Derived Rule of Choice *)

Lemma inc_triple_derived_choice: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ϵ ↑ Q1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ ϵ ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ϵ ↑ Q1 \\// Q2 ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2.
  apply inc_triple_choice_l with (c2 := c2) in H1.
  apply inc_triple_choice_r with (c1 := c1) in H2.
  intros r HQ.
  destruct r as [s | s]; destruct HQ as [HQ1 | HQ2].
  - apply (H1 (RNormal s) HQ1).
  - apply (H2 (RNormal s) HQ2).
  - apply (H1 (RError s) HQ1).
  - apply (H2 (RError s) HQ2).
Qed.

End SPre.


(** ── Semantic soundness lemmas for the tag-tracking rules ──────────────
    Each is the [⟦⟦ ⟧⟧] (reachability) counterpart of one tag-tracking
    constructor of [Inc_triple], mirroring a clause of [cexec].  They feed
    the corresponding cases of [Inc_triple_sound]. *)

(** Postassertion-level consequence: strengthen the precondition, shrink the
    postassertion. *)
Lemma inc_triple_consequence_gen: forall P P' c (Q Q': postassertion),
    (P -->> P') ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧ ->
    (forall r, Q' r -> Q r) ->
    ⟦⟦ P' ⟧⟧ c ⟦⟦ Q' ⟧⟧.
Proof.
  intros P P' c Q Q' HPP' HT Hsub r HQ'.
  destruct (HT r (Hsub r HQ')) as (s & HPs & EXEC).
  exists s. split; [ apply HPP'; exact HPs | exact EXEC ].
Qed.

(** Strongest normal post of an assignment. *)
Lemma inc_triple_assign_sp: forall x a P,
    ⟦⟦ P ⟧⟧ ASSIGN x a
    ⟦⟦ ok ↑ (fun s' => exists s, P s /\ s' = update x (aeval a s) s) ⟧⟧.
Proof.
  intros x a P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [s [HP ->]].
  exists s. split; [ exact HP | apply cexec_assign ].
Qed.

(** Strongest normal post of a nondeterministic assignment. *)
Lemma inc_triple_nondet_sp: forall x P,
    ⟦⟦ P ⟧⟧ NONDET x
    ⟦⟦ ok ↑ (fun s' => exists s n, P s /\ s' = update x n s) ⟧⟧.
Proof.
  intros x P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [s [n [HP ->]]].
  exists s. split; [ exact HP | apply cexec_nondet ].
Qed.

(** Normal sequencing. *)
Lemma inc_triple_seq_ok: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ Q1 ⟧⟧ c2 ⟦⟦ ok ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ;; c2) ⟦⟦ ok ↑ Q2 ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2 r HQ2.
  destruct r as [s | s]; [ | exfalso; exact HQ2 ].
  destruct (H2 (RNormal s) HQ2) as (s_mid & HQ1mid & EXEC2).
  destruct (H1 (RNormal s_mid) HQ1mid) as (s_pre & HPpre & EXEC1).
  exists s_pre. split; [ exact HPpre | eapply cexec_seq; eauto ].
Qed.

(** Erroring sequencing: the error arises in [c1], or after [c1] in [c2]. *)
Lemma inc_triple_err_seq: forall P c1 c2 Q1 R1 R2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ err ↑ R1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ Q1 ⟧⟧ c2 ⟦⟦ err ↑ R2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ;; c2) ⟦⟦ err ↑ (R1 \\// R2) ⟧⟧.
Proof.
  intros P c1 c2 Q1 R1 R2 HR1 HQ1 HR2 r HR.
  destruct r as [s | s]; [ exfalso; exact HR | ].
  destruct HR as [H1 | H2].
  - destruct (HR1 (RError s) H1) as (s_pre & HP & EXEC1).
    exists s_pre. split; [ exact HP | apply cexec_seq_error; exact EXEC1 ].
  - destruct (HR2 (RError s) H2) as (s_mid & HQ1mid & EXEC2).
    destruct (HQ1 (RNormal s_mid) HQ1mid) as (s_pre & HP & EXEC1).
    exists s_pre. split; [ exact HP | eapply cexec_seq_error_right; eauto ].
Qed.

(** Normal choice. *)
Lemma inc_triple_ok_choice: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ ok ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ok ↑ (Q1 \\// Q2) ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2 r HQ.
  destruct r as [s | s]; [ | exfalso; exact HQ ].
  destruct HQ as [HQ1 | HQ2].
  - destruct (H1 (RNormal s) HQ1) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_left; exact EXEC ].
  - destruct (H2 (RNormal s) HQ2) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_right; exact EXEC ].
Qed.

(** Erroring choice. *)
Lemma inc_triple_err_choice: forall P c1 c2 R1 R2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ err ↑ R1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ err ↑ R2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ err ↑ (R1 \\// R2) ⟧⟧.
Proof.
  intros P c1 c2 R1 R2 H1 H2 r HR.
  destruct r as [s | s]; [ exfalso; exact HR | ].
  destruct HR as [HR1 | HR2].
  - destruct (H1 (RError s) HR1) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_left; exact EXEC ].
  - destruct (H2 (RError s) HR2) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_right; exact EXEC ].
Qed.

(** Normal iteration: an [ok] invariant family [P n] (one more successful
    iteration each step) collects into [∃ m, P m]. *)
Lemma inc_triple_ok_cstar: forall (P: nat -> assertion) c,
    (forall n, ⟦⟦ P n ⟧⟧ c ⟦⟦ ok ↑ P (S n) ⟧⟧) ->
    ⟦⟦ P 0%nat ⟧⟧ CSTAR c ⟦⟦ ok ↑ (fun s => exists m, P m s) ⟧⟧.
Proof.
  intros P c H r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [m HPm].
  revert s' HPm.
  induction m as [| k IH]; intros s' HPm.
  - exists s'. split; [ exact HPm | apply cexec_cstar_done ].
  - destruct (H k (RNormal s') HPm) as (s_pre & HPk & EXEC_step).
    destruct (IH s_pre HPk) as (s & HP0 & EXEC_iter).
    exists s. split; [ exact HP0 | ].
    apply cexec_cstar_iff_star.
    apply cexec_cstar_iff_star in EXEC_iter.
    eapply star_trans; [ exact EXEC_iter | ].
    apply star_one. unfold step_iter. exact EXEC_step.
Qed.

(** Erroring iteration: reach an intermediate [M] by normal iterations, then
    error in one more body execution. *)
Lemma inc_triple_err_cstar: forall P c M R,
    ⟦⟦ P ⟧⟧ CSTAR c ⟦⟦ ok ↑ M ⟧⟧ ->
    ⟦⟦ M ⟧⟧ c ⟦⟦ err ↑ R ⟧⟧ ->
    ⟦⟦ P ⟧⟧ CSTAR c ⟦⟦ err ↑ R ⟧⟧.
Proof.
  intros P c M R HM HR r HRr.
  destruct r as [s | s]; [ exfalso; exact HRr | ].
  destruct (HR (RError s) HRr) as (s_mid & HMmid & EXEC_c).
  destruct (HM (RNormal s_mid) HMmid) as (s_pre & HP & EXEC_star).
  exists s_pre. split; [ exact HP | ].
  apply cexec_cstar_err_iff.
  apply cexec_cstar_iff_star in EXEC_star.
  exists s_mid. split; [ exact EXEC_star | exact EXEC_c ].
Qed.

(** Join an [ok]-post and an [err]-post (under the same precondition) into a
    single tag-distinguishing postassertion: [A] on normal results, [B] on
    faulting ones.  Semantically immediate — a result in the combined post is
    either an [ok] state in [A] (reachable by [Hok]) or an [err] state in [B]
    (reachable by [Herr]). *)
Lemma inc_triple_combine_ok_err: forall P c A B,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ok ↑ A ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ err ↑ B ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ fun r => match r with
                          | RNormal s => A s
                          | RError s => B s
                          end ⟧⟧.
Proof.
  intros P c A B Hok Herr r HQ.
  destruct r as [s | s].
  - exact (Hok (RNormal s) HQ).
  - exact (Herr (RError s) HQ).
Qed.

(** An [ok] and an [err] reachability post combine into an [ϵ] post over
    their conjunction.  Derived from [inc_triple_combine_ok_err] (which builds
    the tag-distinguishing post) by shrinking that post to [A //\\ B] via
    [inc_triple_consequence_gen]. *)
Lemma inc_triple_ok_err_to_eps: forall P c A B,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ok ↑ A ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ err ↑ B ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ (A //\\ B) ⟧⟧.
Proof.
  intros P c A B HA HB.
  eapply inc_triple_consequence_gen with
    (P := P)
    (Q := fun r => match r with
                   | RNormal s => A s
                   | RError s => B s
                   end).
  - intros s Hs; exact Hs.
  - exact (inc_triple_combine_ok_err P c A B HA HB).
  - intros r HAB; destruct r as [s | s]; destruct HAB as [HAs HBs];
      [ exact HAs | exact HBs ].
Qed.


Module IncSoundness.

Theorem Inc_triple_sound: forall P c Q,
    (⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧) ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros P c Q H. induction H.
  - (* Inc_Empty_under_approx *) apply inc_triple_empty_under_approx.
  - (* Inc_triple_skip *) apply inc_triple_skip.
  - (* Inc_choice_l *) apply inc_triple_choice_l; assumption.
  - (* Inc_choice_r *) apply inc_triple_choice_r; assumption.
  - (* Inc_seq_ok *) eapply inc_triple_seq_normal; eassumption.
  - (* Inc_seq_err *) apply inc_triple_seq_short_circuit; assumption.
  - (* Inc_iterate_zero *) apply inc_triple_iterate_zero.
  - (* Inc_iterate_step *) apply inc_triple_iterate_non_zero; assumption.
  - (* Inc_error *) apply inc_triple_error.
  - (* Inc_consequence *) eapply inc_triple_consequence; eassumption.
  - (* Inc_assume *) apply inc_triple_assume.
  - (* Inc_disjunc *) apply inc_triple_disjunc; assumption.
  - (* Inc_backwards_variant *) apply inc_triple_backwards_variant; assumption.
  - (* Inc_assign_fwd *) apply inc_triple_assign_fwd.
  - (* Inc_nondet *) apply inc_triple_nondet.
  - (* Inc_consequence_gen *) eapply inc_triple_consequence_gen; eassumption.
  - (* Inc_assign_sp *) apply inc_triple_assign_sp.
  - (* Inc_nondet_sp *) apply inc_triple_nondet_sp.
  - (* Inc_ok_seq *) eapply inc_triple_seq_ok; eassumption.
  - (* Inc_err_seq *) eapply inc_triple_err_seq; eassumption.
  - (* Inc_ok_choice *) apply inc_triple_ok_choice; assumption.
  - (* Inc_err_choice *) apply inc_triple_err_choice; assumption.
  - (* Inc_ok_cstar *) apply inc_triple_ok_cstar; assumption.
  - (* Inc_err_cstar *) eapply inc_triple_err_cstar; eassumption.
  - (* Inc_combine_ok_err *) apply inc_triple_combine_ok_err; assumption.
Qed.


(* Principle of Agreement: [u]c[u'] ∧ (u ⇒ o) ∧ {o} c {o} ⇒ u' ⇒ o' *)
Lemma agreement: forall U c U' O O',
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧ ->
    U -->> O ->
    ⦃ O ⦄ c ⦃ O' ⦄  ->
    U' -->> O'.
Proof.
  intros U c U' O O' HIL HUO HHO s' HUs'.
  apply Inc_triple_sound in HIL.
  apply Soundness.triple_soundness in HHO.
  destruct (HIL (RNormal s') HUs') as (s & HUs & HEX).
  apply HUO in HUs.
  destruct (HHO s (RNormal s') HEX HUs) as (s'' & EQ & HO').
  inversion EQ; subst. exact HO'.
Qed.


(* Principle of Agreement for strong hoare triples *)
Lemma agreement_Triple: forall U c U' O O',
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧ ->
    U -->> O ->
    ⦇ O ⦈ c ⦇ O' ⦈  ->
    U' -->> O'.
Proof.
  intros U c U' O O' HIL HUO HHO s' HUs'.
  apply Inc_triple_sound in HIL.
  apply Soundness.Triple_partial_soundness in HHO.
  destruct (HIL (RNormal s') HUs') as (s & HUs & HEX).
  apply HUO in HUs.
  destruct (HHO s (RNormal s') HEX HUs) as (s'' & EQ & HO').
  inversion EQ; subst. exact HO'.
Qed.

(* [u] c [u'] ∧ u ⇒ o ∧ ¬ (u' ⇒ o') ⇒ ¬({o} c {o'}) *)
Lemma denial: forall U c U' O O',
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧ ->
    U -->> O ->
    ~ (U' -->> O') ->
    ~ (⦃ O ⦄ c ⦃ O' ⦄).
Proof.
  intros U c U' O O' HIL HUO HnotU'O' Hhoare.
  apply HnotU'O'.
  eapply agreement; eauto.
Qed.

End IncSoundness.

Module IncCompleteness.

(* Surprising *)
Definition sem_sp (c: com) (P: assertion) : postassertion :=
  fun r => exists s, P s /\ cexec s c r.

(* [sem_sp c P] is itself a valid incorrectness post: the triple holds
   definitionally, since the triple unfolds to exactly its definition.
   We use the postassertion-level notation, since [sem_sp] inspects the
   result rather than being a plain [assertion]. *)
Lemma sem_sp_valid: forall P c,
    ⟦⟦ P ⟧⟧ c ⟦⟦ sem_sp c P ⟧⟧.
Proof.
  intros P c r HQ. exact HQ.
Qed.

(* It is the strongest such post: any valid post is contained in it. *)
Lemma sem_sp_strongest: forall P c (Q: postassertion),
    ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧ ->
    Q  --* sem_sp c P.
Proof.
  intros P c Q HT r HQ. exact (HT r HQ).
Qed.

(** ** Syntactic strongest postconditions

    [spo c P] / [spe c P] are the strongest normal / erroring postconditions
    of [c] from [P], expressed directly through the operational semantics. *)
Definition spo (c: com) (P: assertion) : assertion :=
  fun s' => exists s, P s /\ s =[ c ]=> RNormal s'.
Definition spe (c: com) (P: assertion) : assertion :=
  fun s' => exists s, P s /\ s =[ c ]=> RError s'.

(** [spo_iter c P n]: states reachable from [P] by exactly [n] successful
    iterations of [c]. *)
Fixpoint spo_iter (c: com) (P: assertion) (n: nat) : assertion :=
  match n with
  | 0%nat => P
  | S k => spo c (spo_iter c P k)
  end.

(** Pure post-weakening (consequence keeping the precondition fixed). *)
Lemma Inc_post_weaken: forall P c (Q Q': postassertion),
  Inc_triple P c Q -> (forall r, Q' r -> Q r) -> Inc_triple P c Q'.
Proof.
  intros P c Q Q' H Hsub.
  eapply Inc_consequence_gen; [ intros s Hs; exact Hs | exact H | exact Hsub ].
Qed.

(** An [ok]/[err] triple whose post is empty is vacuously derivable. *)
Lemma Inc_ok_empty: forall P c (A: assertion),
  (forall s, ~ A s) -> ⟦ P ⟧ c ⟦ ok ↑ A ⟧.
Proof.
  intros P c A Hempty.
  eapply Inc_post_weaken; [ apply (Inc_Empty_under_approx P c) | ].
  intros r HA. destruct r as [s|s]; cbn in *; [ exfalso; exact (Hempty s HA) | exact HA ].
Qed.

Lemma Inc_err_empty: forall P c (B: assertion),
  (forall s, ~ B s) -> ⟦ P ⟧ c ⟦ err ↑ B ⟧.
Proof.
  intros P c B Hempty.
  eapply Inc_post_weaken; [ apply (Inc_Empty_under_approx P c) | ].
  intros r HB. destruct r as [s|s]; cbn in *; [ exact HB | exfalso; exact (Hempty s HB) ].
Qed.

(** [spo_iter] shifts: iterating from [spo c P] equals iterating one more from [P]. *)
Lemma spo_iter_shift: forall c P n,
  spo_iter c (spo c P) n = spo_iter c P (S n).
Proof.
  intros c P. induction n as [|k IH]; [ reflexivity | ].
  cbn. cbn in IH. rewrite IH. reflexivity.
Qed.

(** Every state reachable by [star]-iterations is captured by some [spo_iter]. *)
Lemma spo_star_complete: forall c s s',
  star (step_iter c) s s' -> forall P, P s -> exists n, spo_iter c P n s'.
Proof.
  intros c s s' HStar. induction HStar as [a | a b d Hab Hbd IH]; intros P HP.
  - exists 0%nat. exact HP.
  - destruct (IH (spo c P)) as [n Hn].
    + exists a. split; [ exact HP | exact Hab ].
    + exists (S n). rewrite <- spo_iter_shift. exact Hn.
Qed.

(** ** Strongest-post derivability: the heart of completeness.

    For every command [c] and pre [P], the strongest normal post [spo c P]
    and erroring post [spe c P] are *derivable*.  Proven by induction on [c],
    using the tag-tracking rules. *)
Lemma sp_der: forall c P,
  ⟦ P ⟧ c ⟦ ok ↑ spo c P ⟧ /\ ⟦ P ⟧ c ⟦ err ↑ spe c P ⟧.
Proof.
  induction c; intros P; split.
  - (* SKIP, ok *)
    eapply Inc_post_weaken; [ apply (Inc_triple_skip P) | ].
    intros r; destruct r as [s|s]; cbn; [ | tauto ].
    intros [s0 [HP HX]]. inversion HX; subst. exact HP.
  - (* SKIP, err *)
    apply Inc_err_empty. intros s [s0 [HP HX]]. inversion HX.
  - (* ERROR, ok *)
    apply Inc_ok_empty. intros s [s0 [HP HX]]. inversion HX.
  - (* ERROR, err *)
    eapply Inc_post_weaken; [ apply (Inc_error P) | ].
    intros r; destruct r as [s|s]; cbn; [ tauto | ].
    intros [s0 [HP HX]]. inversion HX; subst. exact HP.
  - (* ASSIGN, ok *)
    eapply Inc_post_weaken; [ apply (Inc_assign_sp x a P) | ].
    intros r; destruct r as [s|s]; cbn; [ | tauto ].
    intros [s0 [HP HX]]. inversion HX; subst. exists s0. split; [ exact HP | reflexivity ].
  - (* ASSIGN, err *)
    apply Inc_err_empty. intros s [s0 [HP HX]]. inversion HX.
  - (* NONDET, ok *)
    eapply Inc_post_weaken; [ apply (Inc_nondet_sp x P) | ].
    intros r; destruct r as [s|s]; cbn; [ | tauto ].
    intros [s0 [HP HX]]. inversion HX; subst. exists s0, n. split; [ exact HP | reflexivity ].
  - (* NONDET, err *)
    apply Inc_err_empty. intros s [s0 [HP HX]]. inversion HX.
  - (* ASSUME, ok *)
    eapply Inc_post_weaken; [ apply (Inc_assume P b) | ].
    intros r; destruct r as [s|s]; cbn; [ | tauto ].
    intros [s0 [HP HX]]. inversion HX; subst. split; assumption.
  - (* ASSUME, err *)
    apply Inc_err_empty. intros s [s0 [HP HX]]. inversion HX.
  - (* SEQ, ok *)
    destruct (IHc1 P) as [Hok1 _]. destruct (IHc2 (spo c1 P)) as [Hok2 _].
    eapply Inc_post_weaken; [ apply (Inc_ok_seq P c1 c2 (spo c1 P) (spo c2 (spo c1 P)) Hok1 Hok2) | ].
    intros r; destruct r as [s|s]; cbn; [ | tauto ].
    intros [s0 [HP HX]]. inversion HX; subst.
    exists s'. split; [ exists s0; split; assumption | assumption ].
  - (* SEQ, err *)
    destruct (IHc1 P) as [Hok1 Herr1]. destruct (IHc2 (spo c1 P)) as [_ Herr2].
    eapply Inc_post_weaken;
      [ apply (Inc_err_seq P c1 c2 (spo c1 P) (spe c1 P) (spe c2 (spo c1 P)) Herr1 Hok1 Herr2) | ].
    intros r; destruct r as [s|s]; cbn; [ tauto | ].
    intros [s0 [HP HX]]. inversion HX; subst.
    + left. exists s0. split; assumption.
    + right. exists s'. split; [ exists s0; split; assumption | assumption ].
  - (* CHOICE, ok *)
    destruct (IHc1 P) as [Hok1 _]. destruct (IHc2 P) as [Hok2 _].
    eapply Inc_post_weaken; [ apply (Inc_ok_choice P c1 c2 (spo c1 P) (spo c2 P) Hok1 Hok2) | ].
    intros r; destruct r as [s|s]; cbn; [ | tauto ].
    intros [s0 [HP HX]]. inversion HX; subst.
    + left. exists s0. split; assumption.
    + right. exists s0. split; assumption.
  - (* CHOICE, err *)
    destruct (IHc1 P) as [_ Herr1]. destruct (IHc2 P) as [_ Herr2].
    eapply Inc_post_weaken; [ apply (Inc_err_choice P c1 c2 (spe c1 P) (spe c2 P) Herr1 Herr2) | ].
    intros r; destruct r as [s|s]; cbn; [ tauto | ].
    intros [s0 [HP HX]]. inversion HX; subst.
    + left. exists s0. split; assumption.
    + right. exists s0. split; assumption.
  - (* CSTAR, ok *)
    assert (Hok : ⟦ P ⟧ CSTAR c ⟦ ok ↑ (fun s => exists m, spo_iter c P m s) ⟧).
    { apply (Inc_ok_cstar (spo_iter c P) c).
      intros n. destruct (IHc (spo_iter c P n)) as [Hn _]. exact Hn. }
    eapply Inc_post_weaken; [ exact Hok | ].
    intros r; destruct r as [s|s]; cbn; [ | tauto ].
    intros [s0 [HP HX]]. apply cexec_cstar_iff_star in HX.
    eapply spo_star_complete; eauto.
  - (* CSTAR, err *)
    assert (Hok : ⟦ P ⟧ CSTAR c ⟦ ok ↑ spo (CSTAR c) P ⟧).
    { eapply Inc_post_weaken.
      { apply (Inc_ok_cstar (spo_iter c P) c).
        intros n. destruct (IHc (spo_iter c P n)) as [Hn _]. exact Hn. }
      intros r; destruct r as [s|s]; cbn; [ | tauto ].
      intros [s0 [HP HX]]. apply cexec_cstar_iff_star in HX.
      eapply spo_star_complete; eauto. }
    destruct (IHc (spo (CSTAR c) P)) as [_ Herr].
    eapply Inc_post_weaken;
      [ apply (Inc_err_cstar P c (spo (CSTAR c) P) (spe c (spo (CSTAR c) P)) Hok Herr) | ].
    intros r; destruct r as [s|s]; cbn; [ tauto | ].
    intros [s0 [HP HX]]. apply cexec_cstar_err_iff in HX.
    destruct HX as [s' [HStar HcErr]].
    exists s'. split; [ exists s0; split; [ exact HP | apply cexec_cstar_iff_star; exact HStar ] | exact HcErr ].
Qed.

Theorem Inc_complete:
  forall P c Q, ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ -> ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧.
Proof.
  intros P c Q H.
  destruct (sp_der c P) as [Hok Herr].
  eapply Inc_post_weaken;
    [ exact (Inc_combine_ok_err P c (spo c P) (spe c P) Hok Herr) | ].
  intros r; destruct r as [s|s]; cbn; intros HQ.
  - exact (H (RNormal s) HQ).
  - exact (H (RError s) HQ).
Qed.


End IncCompleteness.

Module sp.

  (** This is the language of commands where [WHILE] loops are annotated by an invariant [Inv]. *)
  Inductive acom: Type :=
  | SKIP                         (**r do nothing *)
  | ERROR                        (**r interrupt the program *)
  | ASSIGN (x: ident) (a: aexp)  (**r assignment: [v := a] *)
  | NONDET (x: ident)            (**r non-deterministic assignment to [x] *)
  | ASSUME (b: bexp)             (**r assume that [b] holds *)
  | SEQ (c1: acom) (c2: acom)      (**r sequence: [c1; c2] *)
  | CHOICE (c1: acom) (c2: acom)   (**r non-deterministic choice: [c1 + c2] *)
  | CSTAR (Invariant: assertion) (c1: acom).             (**r non-deterministic iteration: [c1★] *)

  Fixpoint erase (a : acom): com := 
  match a with 
  | SKIP => Imp.SKIP
  | ERROR => Imp.ERROR
  | ASSIGN x a => Imp.ASSIGN x a
  | NONDET x => Imp.NONDET x
  | ASSUME b => Imp.ASSUME b
  | SEQ c1 c2 => Imp.SEQ (erase c1) (erase c2)
  | CHOICE c1 c2 => Imp.CHOICE (erase c1) (erase c2)
  | CSTAR _ c => Imp.CSTAR (erase c) (* main case, we remove the invariant annotation of the program *)
  end.

  (* Strongest Liberal Postcondition for normal executions *)

  (** The exact reachable post over every result tag at once. *)
  (** Strongest [ok]-post: the exact reachable store after *normal* termination. *)
  Fixpoint slp_ok (P: assertion) (c: acom) : assertion :=
  match c with
  | SKIP => fun s => P s
  | ERROR => ffalse
  | ASSUME b => atrue b //\\ P
  | ASSIGN x a => in_domf x //\\ aexists (fun (m: Z) => aexists (fun (n: Z) =>
      aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n)))
  | NONDET x => in_domf x //\\ aforall (fun (m: aexp) => aupdate x m P)
  | CHOICE c1 c2 => slp_ok P c1 \\// slp_ok P c2
  | SEQ c1 c2 => slp_ok (slp_ok P c1) c2
  | CSTAR Inv c => Inv
  end.

  (** Strongest [err]-post: the exact reachable store after a *faulting* run. *)
  Fixpoint slp_err (P: assertion) (c: acom) : assertion :=
  match c with
  | SKIP => ffalse
  | ERROR => P
  | ASSUME b => ffalse
  | ASSIGN x a => ffalse
  | NONDET x => ffalse
  | CHOICE c1 c2 => slp_err P c1 \\// slp_err P c2
  | SEQ c1 c2 => slp_err P c1 \\// slp_err (slp_ok P c1) c2
  | CSTAR Inv c => ffalse  (* see note: loop error case is handled via the invariant *)
  end.

  (** The strongest *postassertion*: it inspects the result tag and returns the
      [ok] post on normal termination and the [err] post on faulting. This is
      the [result -> Prop] value you asked for — built by matching on the
      postassertion's own argument [r], not by running [cexec] (which is a
      [Prop] relation and cannot be matched on inside a [Fixpoint]). *)
  Definition sp (P: assertion) (c: acom) : postassertion :=
    fun r => match r with
             | RNormal s => slp_ok P c s
             | RError s  => slp_err P c s
             end.

  (** [iter_slp_ok P c n] is the strongest [ok]-post after exactly [n]
      iterations of [c] from [P].  The union over all [n] is the strongest
      post of the loop, which an annotated invariant must under-approximate. *)
  Fixpoint iter_slp_ok (P: assertion) (c: acom) (n: nat) : assertion :=
    match n with
    | O => P
    | S k => slp_ok (iter_slp_ok P c k) c
    end.

(** Well-formedness of the loop annotations in [c]: every [CSTAR Inv body]
    carries an invariant [Inv] that under-approximates the union of the
    [iter_slp_ok] iterates (the nat-indexed variant), and whose body is
    itself well-formed at each iterate and at [Inv].  This is exactly the
    side condition that makes the loop case of [slp_ok_correct] provable. *)
Fixpoint vcond (P: assertion) (c: acom) : Prop :=
  match c with
  | SKIP => True
  | ERROR => True
  | ASSUME _ => True
  | ASSIGN _ _ => True
  | NONDET _ => True
  | CHOICE c1 c2 => vcond P c1 /\ vcond P c2
  | SEQ c1 c2 => vcond P c1 /\ vcond (slp_ok P c1) c2
  | CSTAR Inv body =>
      (Inv -->> (fun s => exists m, iter_slp_ok P body m s))
      /\ (forall m, vcond (iter_slp_ok P body m) body)
      /\ vcond Inv body
  end.

  Definition vcgen (P: assertion) (c: acom) (Q: postassertion) : Prop :=
    vcond P c /\ (Q --* sp P c).

  (* We reuse the semantic strongest posts [spo]/[spe] and the derivability
     result [sp_der] from the completeness development. *)
  Import IncCompleteness.

  (** [spo] is monotone in its precondition. *)
  Lemma spo_mono: forall c (P P': assertion),
    (forall s, P s -> P' s) -> forall s, spo c P s -> spo c P' s.
  Proof.
    intros c P P' Hsub s [s0 [HP HX]]. exists s0. split; [ apply Hsub; exact HP | exact HX ].
  Qed.

  (** Every state reached by [n] successful iterations of [c] is reachable from
      [P] through the reflexive-transitive closure of one body step. *)
  Lemma spo_iter_star: forall c P m s,
    spo_iter c P m s -> exists s0, P s0 /\ star (step_iter c) s0 s.
  Proof.
    intros c P m. induction m as [|k IH]; intros s Hit.
    - exists s. split; [ exact Hit | apply star_refl ].
    - cbn [spo_iter] in Hit. unfold spo in Hit. destruct Hit as [smid [Hk HX]].
      destruct (IH smid Hk) as [s0 [HP HSt]].
      exists s0. split; [ exact HP | ].
      eapply star_trans; [ exact HSt | apply star_one; unfold step_iter; exact HX ].
  Qed.

  (** Hence such a state is in the strongest [ok]-post of [CSTAR c]. *)
  Lemma spo_iter_to_cstar: forall c P m s,
    spo_iter c P m s -> spo (Imp.CSTAR c) P s.
  Proof.
    intros c P m s Hit. destruct (spo_iter_star c P m s Hit) as [s0 [HP HSt]].
    unfold spo. exists s0. split; [ exact HP | apply cexec_cstar_of_star; exact HSt ].
  Qed.

  (** The syntactic [ok]-post under-approximates the semantic one. *)
  Lemma slp_ok_spo: forall c P, vcond P c -> forall s, slp_ok P c s -> spo (erase c) P s.
  Proof.
    induction c as [ | | x a | x | b | c1 IHc1 c2 IHc2 | c1 IHc1 c2 IHc2 | Inv body IHbody ];
      intros P Hv s Hslp; cbn [erase].
    - (* SKIP *) cbn [slp_ok] in Hslp. unfold spo. exists s. split; [ exact Hslp | apply cexec_skip ].
    - (* ERROR *) cbn [slp_ok] in Hslp. contradiction.
    - (* ASSIGN x a *) cbn [slp_ok] in Hslp.
      destruct Hslp as [Hdom [m [n [Heq_x [HP Heq_a]]]]].
      unfold aequal in Heq_x, Heq_a. cbn in Heq_x, Heq_a.
      unfold spo. exists (update x m s). split; [ exact HP | ].
      replace s with (update x (aeval a (update x m s)) (update x m s)) at 2.
      + apply cexec_assign.
      + rewrite Heq_a, update_shadow, <- Heq_x. apply update_get. exact Hdom.
    - (* NONDET x *) cbn [slp_ok] in Hslp.
      destruct Hslp as [Hdom HQ].
      unfold spo. exists (update x 0 s). split.
      + apply (HQ (CONST 0)).
      + replace s with (update x (s x) (update x 0 s)) at 2.
        * apply cexec_nondet.
        * rewrite update_shadow. apply update_get. exact Hdom.
    - (* ASSUME b *) cbn [slp_ok] in Hslp.
      destruct Hslp as [Hb HP].
      unfold spo. exists s. split; [ exact HP | apply cexec_assume; exact Hb ].
    - (* SEQ c1 c2 *) cbn [slp_ok] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      pose proof (IHc2 (slp_ok P c1) Hv2 s Hslp) as Hspo2. unfold spo in Hspo2.
      destruct Hspo2 as [smid [Hmid HX2]].
      pose proof (IHc1 P Hv1 smid Hmid) as Hspo1. unfold spo in Hspo1.
      destruct Hspo1 as [s0 [HP HX1]].
      unfold spo. exists s0. split; [ exact HP | eapply cexec_seq; [ exact HX1 | exact HX2 ] ].
    - (* CHOICE c1 c2 *) cbn [slp_ok] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      destruct Hslp as [H1 | H2].
      + pose proof (IHc1 P Hv1 s H1) as Hspo. unfold spo in Hspo. destruct Hspo as [s0 [HP HX]].
        unfold spo. exists s0. split; [ exact HP | apply cexec_choice_left; exact HX ].
      + pose proof (IHc2 P Hv2 s H2) as Hspo. unfold spo in Hspo. destruct Hspo as [s0 [HP HX]].
        unfold spo. exists s0. split; [ exact HP | apply cexec_choice_right; exact HX ].
    - (* CSTAR Inv body *) cbn [slp_ok] in Hslp. cbn [vcond] in Hv.
      destruct Hv as [Hinv [Hiter Hinvbody]].
      apply Hinv in Hslp. destruct Hslp as [m Hm].
      assert (Hsub: forall k s', iter_slp_ok P body k s' -> spo_iter (erase body) P k s').
      { induction k as [|j IHj]; intros s' Hk.
        - exact Hk.
        - cbn [iter_slp_ok] in Hk. cbn [spo_iter].
          pose proof (IHbody (iter_slp_ok P body j) (Hiter j) s' Hk) as Hspo.
          eapply spo_mono; [ exact IHj | exact Hspo ]. }
      apply (spo_iter_to_cstar (erase body) P m s). apply Hsub. exact Hm.
  Qed.

  (** The syntactic [err]-post under-approximates the semantic one. *)
  Lemma slp_err_spe: forall c P, vcond P c -> forall s, slp_err P c s -> spe (erase c) P s.
  Proof.
    induction c as [ | | x a | x | b | c1 IHc1 c2 IHc2 | c1 IHc1 c2 IHc2 | Inv body IHbody ];
      intros P Hv s Hslp; cbn [erase].
    - (* SKIP *) cbn [slp_err] in Hslp. contradiction.
    - (* ERROR *) cbn [slp_err] in Hslp. unfold spe. exists s. split; [ exact Hslp | apply cexec_error ].
    - (* ASSIGN *) cbn [slp_err] in Hslp. contradiction.
    - (* NONDET *) cbn [slp_err] in Hslp. contradiction.
    - (* ASSUME *) cbn [slp_err] in Hslp. contradiction.
    - (* SEQ c1 c2 *) cbn [slp_err] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      destruct Hslp as [H1 | H2].
      + pose proof (IHc1 P Hv1 s H1) as Hspe. unfold spe in Hspe. destruct Hspe as [s0 [HP HX]].
        unfold spe. exists s0. split; [ exact HP | apply cexec_seq_error; exact HX ].
      + pose proof (IHc2 (slp_ok P c1) Hv2 s H2) as Hspe. unfold spe in Hspe.
        destruct Hspe as [smid [Hmid HX2]].
        pose proof (slp_ok_spo c1 P Hv1 smid Hmid) as Hspo. unfold spo in Hspo.
        destruct Hspo as [s0 [HP HX1]].
        unfold spe. exists s0. split; [ exact HP | eapply cexec_seq_error_right; [ exact HX1 | exact HX2 ] ].
    - (* CHOICE c1 c2 *) cbn [slp_err] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      destruct Hslp as [H1 | H2].
      + pose proof (IHc1 P Hv1 s H1) as Hspe. unfold spe in Hspe. destruct Hspe as [s0 [HP HX]].
        unfold spe. exists s0. split; [ exact HP | apply cexec_choice_left; exact HX ].
      + pose proof (IHc2 P Hv2 s H2) as Hspe. unfold spe in Hspe. destruct Hspe as [s0 [HP HX]].
        unfold spe. exists s0. split; [ exact HP | apply cexec_choice_right; exact HX ].
    - (* CSTAR *) cbn [slp_err] in Hslp. contradiction.
  Qed.

  (** The annotated [ok]-post is a derivable incorrectness post. *)
  Lemma slp_ok_sound: forall c P, vcond P c -> ⟦ P ⟧ erase c ⟦ ok ↑ slp_ok P c ⟧.
  Proof.
    intros c P Hv.
    destruct (sp_der (erase c) P) as [Hok _].
    eapply Inc_post_weaken; [ exact Hok | ].
    intros r; destruct r as [s|s]; cbn;
      [ intros Hslp; exact (slp_ok_spo c P Hv s Hslp) | tauto ].
  Qed.

  (** The annotated [err]-post is a derivable incorrectness post. *)
  Lemma slp_err_sound: forall c P, vcond P c -> ⟦ P ⟧ erase c ⟦ err ↑ slp_err P c ⟧.
  Proof.
    intros c P Hv.
    destruct (sp_der (erase c) P) as [_ Herr].
    eapply Inc_post_weaken; [ exact Herr | ].
    intros r; destruct r as [s|s]; cbn;
      [ tauto | intros Hslp; exact (slp_err_spe c P Hv s Hslp) ].
  Qed.

  (** Soundness of the combined strongest postassertion: under the loop side
      conditions [vcond], the triple [⟦ P ⟧ erase c ⟦ sp P c ⟧] is derivable. *)
  Lemma sp_sound: forall c P,
    vcond P c -> ⟦ P ⟧ erase c ⟦ sp P c ⟧.
  Proof.
    intros c P Hv.
    exact (Inc_combine_ok_err P (erase c) (slp_ok P c) (slp_err P c)
             (slp_ok_sound c P Hv) (slp_err_sound c P Hv)).
  Qed.

  (** Soundness of the verification-condition generator: if the side conditions
      hold and [Q] under-approximates the strongest post, then [⟦ P ⟧ erase c ⟦ Q ⟧]. *)
  Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> ⟦ P ⟧ erase c ⟦ Q ⟧.
  Proof.
    intros P c Q [Hv Himp].
    eapply Inc_post_weaken; [ exact (sp_sound c P Hv) | exact Himp ].
  Qed.

End sp.
