From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Coq.Strings.String.
Require Export Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapFacts.
Require Export Coq.Structures.DecidableType.

Require Import Coq.Strings.String.
Require Export Coq.FSets.FMapWeakList.
Require Export Coq.Structures.DecidableType.

Module StringEQ <: DecidableType.
  Definition t := string.
  Definition eq := @Coq.Init.Logic.eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec := string_dec.
End StringEQ.


Module M := FMapWeakList.Make(StringEQ).

Require Import Coq.MSets.MSetWeakList.

(* Module StringEQFromEqualitiesGnagnagna <: Equalities.DecidableType.
  Definition t := string.
  Definition eq := @Coq.Init.Logic.eq t.
  Definition eq_equiv := Build_Equivalence eq (@refl_equal t) (@sym_eq t) ( @trans_eq t).
  Definition eq_dec := string_dec.
End StringEQFromEqualitiesGnagnagna.

Module M' := MSetWeakList.Make(StringEQFromEqualitiesGnagnagna). *)

Definition state := M.t nat.

Definition get (m : state) (k : string) :=
  M.find k m.

Definition set (m : state) (k : string) (v : nat) :=
  M.add k v m.

Definition empty :=
  M.empty nat.

Notation "▩" := (empty)
                (at level 100, right associativity).

Notation "x '!->' v ';' m" := (set m x v)
                              (at level 100, v at next level, right associativity).


Lemma t_update_shadow : forall (st : M.t nat) x v1 v2,
  (x !-> v2 ; x !-> v1 ; st) = (x !-> v2 ; st).
Admitted.

Theorem t_update_same : forall (m : M.t nat) x v,
  StateMap.get m x = Some v ->
  (x !->  v; m) = m.
Admitted.
