From Coq Require Import PeanoNat Compare_dec Lia String Ascii.
From Coq Require Import OrderedType.

Set Asymmetric Patterns.

Lemma nat_compare_eq_refl : forall x, Nat.compare x x = Eq.
  intros; apply Nat.compare_eq_iff; trivial.
Qed.

#[global] Hint Rewrite <- nat_compare_lt : nat_comp_hints.
#[global] Hint Rewrite <- nat_compare_gt : nat_comp_hints.
#[global] Hint Rewrite    Nat.compare_eq_iff : nat_comp_hints.
#[global] Hint Rewrite <- Nat.compare_eq_iff : nat_comp_hints.
#[global] Hint Rewrite    nat_compare_eq_refl : nat_comp_hints.

Ltac autorewrite_nat_compare :=
  autorewrite with nat_comp_hints in *.

Lemma nat_compare_consistent :
  forall n0 n1,
    { Nat.compare n0 n1 = Lt /\ Nat.compare n1 n0 = Gt }
    + { Nat.compare n0 n1 = Eq /\ Nat.compare n1 n0 = Eq }
    + { Nat.compare n0 n1 = Gt /\ Nat.compare n1 n0 = Lt }.
Proof.
  intros n0 n1;
    destruct (lt_eq_lt_dec n0 n1) as [ [_lt | _eq] | _lt ];
    [ constructor 1; constructor 1  | constructor 1; constructor 2 | constructor 2 ];
    split;
    autorewrite_nat_compare;
    intuition.
Qed.

Print MiniOrderedType.

Module String_as_OT <: OrderedType.
  Definition t := string.

  Fixpoint string_compare str1 str2 :=
    match str1, str2 with
    | EmptyString, EmptyString => Eq
    | EmptyString, _           => Lt
    | _, EmptyString           => Gt
    | String char1 tail1, String char2 tail2 =>
      match Nat.compare (nat_of_ascii char1) (nat_of_ascii char2) with
      | Eq => string_compare tail1 tail2
      | Lt => Lt
      | Gt => Gt
      end
    end.

  Lemma string_compare_eq_refl : forall x, string_compare x x = Eq.
    intro x;
      induction x;
      simpl; trivial;
        autorewrite_nat_compare.
    trivial.
  Qed.

  Ltac comparisons_minicrush :=
    autorewrite_nat_compare;
    match goal with
    | [ |- context [Nat.compare ?a ?b] ] =>
      let H := fresh in
      first [
          assert (Nat.compare a b = Eq) as H by (autorewrite_nat_compare; lia) |
          assert (Nat.compare a b = Lt) as H by (autorewrite_nat_compare; lia) |
          assert (Nat.compare a b = Gt) as H by (autorewrite_nat_compare; lia)
        ]; rewrite H; intuition
    end.

  Ltac destruct_comparisons :=
    repeat match goal with
           | [ H: match ?pred ?a ?b with
                  | Lt => _ | Gt => _ | Eq => _ end = _
               |- _] =>
             let H := fresh in
             destruct (pred a b) eqn:H;
             try discriminate
           end.

  Ltac exfalso_from_equalities :=
    match goal with
      | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] => assert (b = c) by congruence; discriminate
    end.

  Definition eq := @eq string.

  #[global] Hint Resolve string_compare_eq_refl.

  Lemma eq_Eq : forall x y, x = y -> string_compare x y = Eq.
  Proof.
    intros; subst; auto.
  Qed.

  Lemma nat_of_ascii_injective :
    forall a b, nat_of_ascii a = nat_of_ascii b <-> a = b.
  Proof.
    intros a b; split; intro H;
    [ apply (f_equal ascii_of_nat) in H;
      repeat rewrite ascii_nat_embedding in H
    | apply (f_equal nat_of_ascii) in H ]; trivial.
  Qed.

  Lemma Eq_eq : forall x y, string_compare x y = Eq -> x = y.
  Proof.
    induction x;
      destruct y;
      simpl;
      first [ discriminate
            | intros;
              f_equal;
              destruct_comparisons;
              autorewrite_nat_compare;
              rewrite nat_of_ascii_injective in *
            | idtac ];
      intuition.
  Qed.

  Lemma Eq_eq_iff : forall x y, x = y <-> string_compare x y = Eq.
  Proof.
    intros; split; eauto using eq_Eq, Eq_eq.
  Qed.

  Definition eq_refl := @eq_refl string.

  Definition eq_sym := @eq_sym string.

  Definition eq_trans := @eq_trans string.

  Definition eq_equiv := @eq_equivalence string.


  Definition lt x y :=
    string_compare x y = Lt.

  (* Definition lt_strorder := @StrictOrder string lt. *)

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z;
      generalize x z;
      clear x z;

      induction y;
      destruct x;
      destruct z;
      intros;
      unfold lt in *;
      simpl in *;
      first [ discriminate
            | destruct_comparisons; comparisons_minicrush
            | trivial ]; intuition.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    unfold lt, not in *;
      intros;
      rewrite Eq_eq_iff in *;
      exfalso_from_equalities.
  Qed.

  Lemma Lt_Gt : forall x y, string_compare x y = Gt <-> string_compare y x = Lt.
  Proof.
    intros x;
      induction x as [ | x0 x' Hind ];
      intros y;
      destruct y as [ | y0 y' ];

      simpl;
      split;
      first [ discriminate | trivial ];

      destruct (nat_compare_consistent
                  (nat_of_ascii x0)
                  (nat_of_ascii y0))
        as [ [ (H1, H2) | (H1, H2) ] | (H1, H2) ];
      rewrite H1, H2;
      try rewrite Hind;
      auto.
  Qed.

  Definition compare : forall x y : string, Compare lt eq x y.
  Proof with assumption.
    intros x y.
    simpl.
     destruct (string_compare x y) eqn:comp.
     - unfold lt. constructor 2. apply Eq_eq...
     - constructor 1. unfold lt...
     - constructor 3. apply Lt_Gt...
  Defined.


  Definition eq_dec : forall (x y: string), { x = y } + { x <> y } := string_dec.


  Lemma lt_Transitive : Transitive lt.
  Proof.
       unfold Transitive in *.
       apply lt_trans.
  Qed.

  Lemma lt_transTrans : Transitive lt.
  Proof.
       unfold Transitive in *.
       apply lt_trans.
  Qed.

   Lemma lt_Irreflexive : Irreflexive lt.
  Proof.
       unfold Irreflexive in *.
       unfold Reflexive.
       unfold complement.
       intros x H.
       inversion H.
       rewrite string_compare_eq_refl in H1.
       inversion H1.
  Qed.

Instance lt_strorder : StrictOrder lt.
  Proof.
  apply Build_StrictOrder.
  - apply lt_Irreflexive.
  - apply lt_Transitive.
 Qed.

Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof.
  intros x y Heq1 x1  x2 Heq2.
  split ; rewrite Heq1 ; rewrite Heq2 ; intro H;  apply H.
Qed.

End String_as_OT.

Require Import FSetList.
Module fsetString := FSetList.Make(String_as_OT). 
(* Module mfoo := MSetList.Make(String_as_OT). *)


