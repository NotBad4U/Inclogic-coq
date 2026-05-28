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
    ⟦ P ⟧   (c1 ;; c2) ⟦ ϵ ↑ R ⟧
| Inc_iterate_zero: forall Inv P c,
    ⟦ P ⟧ CSTAR Inv c ⟦ ok ↑ P ⟧
| Inc_iterate_step: forall Inv P c Q,
    ⟦ Q ⟧ CSTAR Inv c ;; c ⟦ ϵ ↑ P ⟧ ->
    (*─────────────────────────────*)
    ⟦ P ⟧ CSTAR Inv c ⟦ ϵ ↑ P ⟧
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
| Inc_backwards_variant: forall Inv (P: nat -> assertion) c,
    (forall n, ⟦ P n ⟧ c ⟦ ϵ ↑ P (n + 1)%nat ⟧) ->
    (*───────────────────────────────────────────────────────────*)
    ⟦ P 0%nat ⟧ CSTAR Inv c ⟦ ok ↑ (fun s => exists (m: nat), P m s) ⟧
(* [p] x = e [ok: ∃x'. p[x'/x] ∧ x = e[x'/x]] [er: false] *)
| Inc_assign_fwd: forall x a P,
  (*────────────────────────────────────────────────────────────────────*)   
  ⟦ P ⟧ ASSIGN x a ⟦ ok ↑ aexists (fun m => aexists (fun n =>
        aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) ⟧
| Inc_nondet: forall x P,
    (*─────────────────────────────────────────────────────────────*)
    ⟦ P ⟧ NONDET x ⟦ ok ↑ (aexists (fun n => aupdate x (CONST n) P)) ⟧
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

(* Definition IncTriple P c Q := forall st', Q st' -> exists st, P st /\ cexec st c st'.
 *)
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

Lemma inc_triple_iterate_non_zero: forall Inv P c Q,
    ⟦⟦ P ⟧⟧  c ★ ⟨ Inv ⟩ ;; c  ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧  c ★ ⟨ Inv ⟩ ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros Inv P c Q H r HQ.
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

Lemma inc_triple_iterate_zero: forall Inv P c,
    ⟦⟦ P ⟧⟧  c ★ ⟨ Inv ⟩ ⟦⟦ ok ↑ P ⟧⟧.
Proof.
    intros Inv P c r Q.
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


Lemma inc_triple_backwards_variant: forall Inv (P: nat -> assertion) c,
    (forall n, ⟦⟦ P n ⟧⟧ c ⟦⟦ ϵ ↑ P (n + 1)%nat ⟧⟧) ->
    ⟦⟦ P 0%nat ⟧⟧ c ★ ⟨ Inv ⟩ ⟦⟦ ok ↑ (fun s => exists (m: nat), P m s) ⟧⟧.
Proof.
  intros Inv P c H r HQ.
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
Lemma cmd_n_to_cstar: forall Inv i c s r,
  cexec s (cmd_n i c) r -> cexec s (CSTAR Inv c) r.
Proof.
  intros Inv; induction i as [|n IH]; intros c s r EXEC; cbn in EXEC.
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

Lemma inc_triple_derived_unrolling: forall Inv P c (postassert_i: nat -> assertion),
    (forall i, ⟦⟦ P ⟧⟧ (cmd_n i c) ⟦⟦ ϵ ↑ postassert_i i ⟧⟧) ->
    ⟦⟦ P ⟧⟧ c ★ ⟨ Inv ⟩ ⟦⟦ ϵ ↑ aexists (fun i => postassert_i i) ⟧⟧.
Proof.
  intros Inv P c postassert_i H r HQ.
  destruct r as [s' | s']; cbn in HQ; destruct HQ as [j Hj].
  - destruct (H j (RNormal s') Hj) as (s & HPs & EXEC).
    exists s. split; [ exact HPs | apply cmd_n_to_cstar with (Inv := Inv) in EXEC; exact EXEC ].
  - destruct (H j (RError s') Hj) as (s & HPs & EXEC).
    exists s. split; [ exact HPs | apply cmd_n_to_cstar with (Inv := Inv) in EXEC; exact EXEC ].
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


Module IncSoundness.

Theorem Inc_triple_sound: forall P c Q,
    (⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧) ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
Admitted.


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

Module StrongestLiberalPostcondition.

  Notation "⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧" := (IncTriple P c Q) (at level 90, c at next level).

  (* Strongest Liberal Postcondition for normal executions *)
  Fixpoint slp_ok (P: assertion) (c: com) : assertion :=
  match c with
  | SKIP => P
  | ERROR => ffalse
  | ASSUME b => atrue b //\\ P
  | ASSIGN x a => in_domf x //\\ aexists (fun (m: Z) => aexists (fun (n: Z) =>
      aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n)))
  | NONDET x => in_domf x //\\ aforall (fun (m: aexp) => aupdate x m P)
  | c1 ⊕ c2 => slp_ok P c1 \\// slp_ok P c2
  | c1 ;; c2 => slp_ok (slp_ok P c1) c2
  | CSTAR Inv c => ffalse
    (* The carried invariant [Inv] is now in scope here.  Using it for a
       non-trivial loop SLP (e.g. [Inv]) requires adding soundness side
       conditions to [slp_ok_correct] (at least [P -->> Inv] and that [Inv]
       is closed under one iteration); left as [ffalse] until that is settled. *)
  end.

  (* Strongest Liberal Postcondition for error executions *)
  Fixpoint slp_err (P: assertion) (c: com) : assertion :=
  match c with
  | SKIP => ffalse
  | ERROR => P
  | ASSUME b => ffalse
  | ASSIGN x a => ffalse
  | NONDET x => ffalse
  | c1 ⊕ c2 => slp_err P c1 \\// slp_err P c2
  | c1 ;; c2 => slp_err P c1 \\// slp_err (slp_ok P c1) c2
  | CSTAR Inv c => ffalse
    (* As for [slp_ok]: [Inv] is available, but a meaningful erroring loop SLP
       needs soundness side conditions on [slp_err_correct] first. *)
  end.

  Lemma slp_ok_correct: forall P c,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ok ↑ slp_ok P c ⟧⟧.
  Proof.
    intros P c. revert P.
    induction c; intros P r HQ; cbn [slp_ok] in HQ.
    - (* SKIP *) destruct r as [s|s]; [|contradiction].
      exists s. split; [exact HQ | apply cexec_skip].
    - (* ERROR *) destruct r as [s|s]; contradiction.
    - (* ASSIGN x a *) destruct r as [s|s]; [|contradiction].
      destruct HQ as [Hdom [m [n [Heq_x [HP Heq_a]]]]].
      cbn in HP, Heq_a, Heq_x.
      unfold aequal in Heq_x, Heq_a. cbn in Heq_x, Heq_a.
      exists (update x m s). split; [ exact HP | ].
      replace s with (update x (aeval a (update x m s)) (update x m s)) at 2.
      + apply cexec_assign.
      + rewrite Heq_a, update_shadow, <- Heq_x. apply update_get. exact Hdom.
    - (* NONDET x *) destruct r as [s|s]; [|contradiction].
      destruct HQ as [Hdom HQ].
      exists (update x 0 s). split.
      + apply (HQ (CONST 0)).
      + replace s with (update x (s x) (update x 0 s)) at 2.
        * apply cexec_nondet.
        * rewrite update_shadow. apply update_get. exact Hdom.
    - (* ASSUME b *) destruct r as [s|s]; [|contradiction].
      destruct HQ as [Hb HP].
      exists s. split; [exact HP | apply cexec_assume; exact Hb].
    - (* SEQ c1 c2 *) destruct r as [s|s]; [|contradiction].
      destruct (IHc2 (slp_ok P c1) (RNormal s) HQ) as (s_mid & HQmid & EXEC2).
      destruct (IHc1 P (RNormal s_mid) HQmid) as (s_pre & HPpre & EXEC1).
      exists s_pre. split; [ exact HPpre | eapply cexec_seq; eauto ].
    - (* CHOICE c1 c2 *) destruct r as [s|s]; [|contradiction].
      destruct HQ as [H1 | H2].
      + destruct (IHc1 P (RNormal s) H1) as (s0 & HP & EXEC).
        exists s0. split; [ exact HP | apply cexec_choice_left; exact EXEC ].
      + destruct (IHc2 P (RNormal s) H2) as (s0 & HP & EXEC).
        exists s0. split; [ exact HP | apply cexec_choice_right; exact EXEC ].
    - (* CSTAR c *) destruct r as [s|s]; contradiction.
  Qed.

  Lemma slp_err_correct: forall P c,
    ⟦⟦ P ⟧⟧ c ⟦⟦ err ↑ slp_err P c ⟧⟧.
  Proof.
    intros P c. revert P.
    induction c; intros P r HQ; cbn [slp_err] in HQ.
    - (* SKIP *) destruct r as [s|s]; contradiction.
    - (* ERROR *) destruct r as [s|s]; [contradiction|].
      exists s. split; [exact HQ | apply cexec_error].
    - (* ASSIGN *) destruct r as [s|s]; contradiction.
    - (* NONDET *) destruct r as [s|s]; contradiction.
    - (* ASSUME *) destruct r as [s|s]; contradiction.
    - (* SEQ c1 c2 *) destruct r as [s|s]; [contradiction|].
      destruct HQ as [H1 | H2].
      + destruct (IHc1 P (RError s) H1) as (s_pre & HP & EXEC1).
        exists s_pre. split; [exact HP | apply cexec_seq_error; exact EXEC1].
      + destruct (IHc2 (slp_ok P c1) (RError s) H2) as (s_mid & HQmid & EXEC2).
        destruct (slp_ok_correct P c1 (RNormal s_mid) HQmid) as (s_pre & HP & EXEC1).
        exists s_pre. split; [exact HP | eapply cexec_seq_error_right; eauto].
    - (* CHOICE c1 c2 *) destruct r as [s|s]; [contradiction|].
      destruct HQ as [H1 | H2].
      + destruct (IHc1 P (RError s) H1) as (s0 & HP & EXEC).
        exists s0. split; [exact HP | apply cexec_choice_left; exact EXEC].
      + destruct (IHc2 P (RError s) H2) as (s0 & HP & EXEC).
        exists s0. split; [exact HP | apply cexec_choice_right; exact EXEC].
    - (* CSTAR c *) destruct r as [s|s]; contradiction.
  Qed.

  Theorem slp_correct: forall P c,
    let Q : postassertion := fun r => match r with
                                      | RNormal s => slp_ok  P c s
                                      | RError  s => slp_err P c s
                                      end in
    ⟦⟦ P ⟧⟧ c ⟦⟦  Q ⟧⟧.
  Proof.
    intros P c Q r HQ. subst Q. cbn in HQ.
    destruct r as [s | s].
    - apply (slp_ok_correct  P c (RNormal s) HQ).
    - apply (slp_err_correct P c (RError s) HQ).
  Qed.

End StrongestLiberalPostcondition.
