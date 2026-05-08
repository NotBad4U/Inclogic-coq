From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality.
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
    ⟦ P ⟧ c ⟦ ϵ ↑ ffalse ⟧
| Inc_triple_skip: forall P,
    ⟦ P ⟧ SKIP ⟦ ok ↑ P ⟧
| Inc_choice_l: forall P c1 c2,
    ⟦ P ⟧ c1 ⟦ ϵ ↑ P ⟧ ->
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ ϵ ↑ P ⟧
| Inc_choice_r: forall P c1 c2,
    ⟦ P ⟧ c2 ⟦ ϵ ↑ P ⟧ ->
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ ϵ ↑ P ⟧
| Inc_seq_ok: forall P c1 c2 Q1 Q2,
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ Q1 ⟧ c2 ⟦ ϵ ↑ Q2 ⟧ ->
    ⟦ P ⟧   (c1 ;; c2) ⟦ ϵ ↑ Q2 ⟧
| Inc_seq_err: forall P c1 c2 R,
    ⟦ P ⟧ c1 ⟦ err ↑ R ⟧ ->
    ⟦ P ⟧   (c1 ;; c2) ⟦ ϵ ↑ R ⟧
| Inc_iterate_zero: forall P c,
    ⟦ P ⟧ CSTAR c ⟦ ok ↑ P ⟧
| Inc_iterate_step: forall P c Q,
    ⟦ Q ⟧ CSTAR c ;; c ⟦ ϵ ↑ P ⟧ ->
    ⟦ P ⟧ CSTAR c ⟦ ϵ ↑ P ⟧
| Inc_error: forall P,
    ⟦ P ⟧ ERROR ⟦ err ↑ P ⟧
| Inc_consequence: forall P P' c Q Q',
    (P -->> P') ->
    ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ ->
    (Q' -->> Q) ->
    ⟦ P' ⟧ c ⟦ ϵ ↑ Q' ⟧
| Inc_assume : forall P b,
    ⟦ P ⟧ (ASSUME b) ⟦ ok ↑ atrue b //\\ P ⟧
| Inc_disjunc: forall P1 P2 c Q1 Q2,
    ⟦ P1 ⟧ c ⟦ ϵ ↑ Q1 ⟧ ->
    ⟦ P2 ⟧ c ⟦ ϵ ↑ Q2 ⟧ ->
    ⟦ P1 \\// P2 ⟧ c ⟦ ϵ ↑ Q1 \\// Q2 ⟧
| Inc_backwards_variant: forall (P: nat -> assertion) c n,
    ⟦ P n ⟧ c ⟦ ϵ ↑ P (n + 1)%nat ⟧ ->
    ⟦ P 0%nat ⟧ c ⟦ ϵ ↑ (fun s => exists (m: nat), P m s) ⟧
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


Notation 

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

(* Principle of Agreement: [u]c[u'] ∧ (u ⇒ o) ∧ {o} c {o} ⇒ u' ⇒ o' *)
(* TODO: requires soundness of Inc_triple (every state in U' is cexec-reachable
   from some state in U) and of WeakHoareRes (no errors from O, normal ends in O').
   Combined those give: take s' ∈ U', get s ∈ U ⊆ O reaching s' under cexec; weak
   Hoare rules out the RError branch and forces s' ∈ O'. *)
Lemma agreement: forall U c U' O O',
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧ ->
    U -->> O ->
    ⦃ O ⦄ c ⦃ O' ⦄  ->
    U' -->> O'.
Proof.
Admitted.

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
