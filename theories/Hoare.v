Require Import StringAsOT.
Require Import StateMap.
Require Import Imp.

Definition hoare_triple
           (P : Assertion) (c : com) (s: Signal) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> s: st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ ε ↑ Q }}" :=
(hoare_triple P c ε Q) (at level 90, c custom com at level 99): inclogic_spec_scope.
