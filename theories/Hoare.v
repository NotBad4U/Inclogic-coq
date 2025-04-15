Require Import StateMap.
Require Import Imp.

(**
   We give a semantic interpretation to the statements [Hoare P c Q]
   of Hoare logic.  The interpretation is the relation [triple P c Q]
   defined below in terms of IMP's natural semantics
   (the relation [cexec s c s']).
*)

Definition hoare_triple
           (P : Assertion) (c : com) (s: Signal) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> s: st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ ε ↑ Q }}" :=
(hoare_triple P c ε Q) (at level 90, c custom com at level 99): inclogic_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) s c,
  (forall st, Q st) ->
  {{ P }} c {{ s ↑ Q }}.
Proof.
  unfold hoare_triple. intros. apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c s,
  (forall st, ~ (P st)) ->
  {{ P }} c {{ s ↑ Q }}.
Proof.
  unfold hoare_triple.
  intros.
  apply H in H1. destruct H1.
Qed.

Theorem hoare_skip : forall P s,
     {{ P }} skip {{ s ↑ P }}.
Proof.
  intros P s st st' H HP.
  inversion H; subst; assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2 e,
     {{ Q }} c2 {{ e ↑ R }} ->
     {{ P }} c1 {{ ok ↑ Q }} ->
     {{ P }} c1; c2 {{ e ↑ R }}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 e H1 H2 st st'' H12 Pre.
  specialize (H1 st st'').
  
  (* specialize (H2 st st''). *)
  
  (* inversion H12; subst.
  - specialize (H1 st'0 st').
    apply H1.
    assumption.
    specialize (H2 st st'0).
    eapply H2; 
    assumption.
  - specialize (H1 st st').
    specialize (H2 st st'). *)
    
Admitted.
