(** * Kleene-algebra view of relations

    A small setoid layer on top of [Sequences.v] giving:
    - extensional equivalence [≡] of relations (axiom-free, just pointwise [<->]);
    - relation composition [⨟] (the Kleene "·" / sequence);
    - [Proper] instances so that [rewrite] traverses [⨟], [star], [plus];
    - the basic Kleene-algebra laws on [star]. *)

From Stdlib Require Import RelationClasses Morphisms Setoid.
From IncLogic Require Import Sequences.

Set Implicit Arguments.

(** ** Extensional equivalence of relations *)

Definition rel_eq {A} (R1 R2 : A -> A -> Prop) : Prop :=
  forall a b, R1 a b <-> R2 a b.

Infix "≡" := rel_eq (at level 70, no associativity).

#[global] Instance rel_eq_equiv {A} : Equivalence (@rel_eq A).
Proof.
  split.
  - intros R a b. reflexivity.
  - intros R1 R2 H a b. symmetry. apply H.
  - intros R1 R2 R3 H12 H23 a b. etransitivity; [ apply H12 | apply H23 ].
Qed.

(** ** Relation composition (sequence) *)

Definition rcomp {A} (R1 R2 : A -> A -> Prop) : A -> A -> Prop :=
  fun a c => exists b, R1 a b /\ R2 b c.

Infix "⨟" := rcomp (at level 60, right associativity).

#[global] Instance rcomp_proper {A} :
  Proper (@rel_eq A ==> @rel_eq A ==> @rel_eq A) (@rcomp A).
Proof.
  intros R1 R1' H1 R2 R2' H2 a c.
  unfold rcomp; split; intros (b & Hab & Hbc); exists b.
  - split; [ apply H1, Hab | apply H2, Hbc ].
  - split; [ apply H1, Hab | apply H2, Hbc ].
Qed.

(** ** [star] respects relation equivalence *)

Lemma star_mono {A} (R R' : A -> A -> Prop) :
  (forall a b, R a b -> R' a b) ->
  forall a b, star R a b -> star R' a b.
Proof.
  intros HRR' a b H. induction H.
  - apply star_refl.
  - eapply star_step; [ apply HRR'; exact H | exact IHstar ].
Qed.

#[global] Instance star_proper {A} :
  Proper (@rel_eq A ==> @rel_eq A) (@star A).
Proof.
  intros R R' HR a b. split; apply star_mono; intros x y; apply HR.
Qed.

(** ** [plus] respects relation equivalence *)

Lemma plus_mono {A} (R R' : A -> A -> Prop) :
  (forall a b, R a b -> R' a b) ->
  forall a b, plus R a b -> plus R' a b.
Proof.
  intros HRR' a b H. inversion H; subst.
  eapply plus_left; [ apply HRR'; eauto | eapply star_mono; eauto ].
Qed.

#[global] Instance plus_proper {A} :
  Proper (@rel_eq A ==> @rel_eq A) (@plus A).
Proof.
  intros R R' HR a b. split; apply plus_mono; intros x y; apply HR.
Qed.

(** ** Kleene-algebra laws *)

(** Identity (diagonal) relation, useful as the unit of [⨟]. *)
Definition rid {A} : A -> A -> Prop := fun a b => a = b.

Section KLEENE_LAWS.

Variable A : Type.
Implicit Types R S T : A -> A -> Prop.

(** Sequence is associative. *)
Lemma rcomp_assoc R S T : (R ⨟ S) ⨟ T ≡ R ⨟ (S ⨟ T).
Proof.
  intros a d. unfold rcomp; split.
  - intros (c & (b & Rab & Sbc) & Tcd). exists b; split; [ exact Rab | ].
    exists c; split; [ exact Sbc | exact Tcd ].
  - intros (b & Rab & (c & Sbc & Tcd)). exists c; split; [ | exact Tcd ].
    exists b; split; [ exact Rab | exact Sbc ].
Qed.

(** Identity is the left and right unit of sequence. *)
Lemma rcomp_id_l R : rid ⨟ R ≡ R.
Proof.
  intros a b. unfold rcomp, rid; split.
  - intros (x & -> & H). exact H.
  - intro H. exists a. split; [ reflexivity | exact H ].
Qed.

Lemma rcomp_id_r R : R ⨟ rid ≡ R.
Proof.
  intros a b. unfold rcomp, rid; split.
  - intros (x & H & ->). exact H.
  - intro H. exists b. split; [ exact H | reflexivity ].
Qed.

(** [star R] is the union of all powers of [R]: it contains [rid] and [R]. *)
Lemma rid_in_star R : (@rid A) ≡ rid ⨟ rid.
Proof. rewrite rcomp_id_l. reflexivity. Qed.

Lemma star_refl_incl R : forall a b, (@rid A) a b -> star R a b.
Proof. intros a b ->. apply star_refl. Qed.

Lemma R_in_star R : forall a b, R a b -> star R a b.
Proof. intros. apply star_one. assumption. Qed.

(** Idempotence: [R* ⨟ R* ≡ R*]. *)
Lemma star_idem R : star R ⨟ star R ≡ star R.
Proof.
  intros a c. unfold rcomp; split.
  - intros (b & Hab & Hbc). eapply star_trans; eauto.
  - intro H. exists a. split; [ apply star_refl | exact H ].
Qed.

(** Left unfolding: [R* ≡ rid ∪ R ⨟ R*].
    Without an explicit union operator we phrase it as the two inclusions. *)
Lemma star_unfold_left R : forall a b,
  star R a b <-> a = b \/ (R ⨟ star R) a b.
Proof.
  intros a b; split.
  - intro H. inversion H; subst.
    + left. reflexivity.
    + right. exists b0. split; assumption.
  - intros [-> | (c & Rac & Hcb)].
    + apply star_refl.
    + eapply star_step; eauto.
Qed.

(** Right unfolding: [R* ≡ rid ∪ R* ⨟ R]. *)
Lemma star_unfold_right R : forall a b,
  star R a b <-> a = b \/ (star R ⨟ R) a b.
Proof.
  intros a b; split.
  - intro H. induction H.
    + left. reflexivity.
    + destruct IHstar as [-> | (d & Hbd & Rdc)].
      * right. exists a. split; [ apply star_refl | exact H ].
      * right. exists d. split; [ eapply star_step; eauto | exact Rdc ].
  - intros [-> | (c & Hac & Rcb)].
    + apply star_refl.
    + eapply star_trans; [ exact Hac | apply star_one; exact Rcb ].
Qed.

(** The Kleene "shift" identity: [R ⨟ R* ≡ R* ⨟ R].
    Both sides equal [plus R]. *)
Lemma rcomp_star_shift R : R ⨟ star R ≡ star R ⨟ R.
Proof.
  intros a c. unfold rcomp; split.
  - intros (b & Rab & Hbc).
    assert (P : plus R a c) by (eapply plus_left; eauto).
    inversion P; subst.
    (* plus_left gives R a b0 /\ star b0 c — turn back into star_R ⨟ R. *)
    apply (@star_unfold_right R) in H0 as [-> | (d & Hbd & Rdc)].
    + exists a. split; [ apply star_refl | assumption ].
    + exists d. split; [ eapply star_step; eauto | exact Rdc ].
  - intros (b & Hab & Rbc).
    apply (@star_unfold_left R) in Hab as [-> | (d & Rad & Hdb)].
    + exists c. split; [ exact Rbc | apply star_refl ].
    + exists d. split; [ exact Rad | eapply star_trans; [ exact Hdb | apply star_one; exact Rbc ] ].
Qed.

(** [star] is idempotent under the star operation: star (star R) is star R. *)
Lemma star_star R : star (star R) ≡ star R.
Proof.
  intros a b; split.
  - intro H. induction H.
    + apply star_refl.
    + eapply star_trans; eauto.
  - intro H. apply star_one. exact H.
Qed.

End KLEENE_LAWS.
