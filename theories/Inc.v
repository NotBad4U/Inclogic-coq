From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality.
From IncLogic Require Import Imp Sequences Hoare.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Reserved Notation "⟦ P ⟧ c ⟦ Q ⟧" (at level 90, c at next level).

(* Notation "⟦ P ⟧ c ⟦ Q1 ⟧ ⟦ Q2 ⟧" := (⟦ P ⟧ c ⟦ Q1 ⟧ /\ ⟦ P ⟧ c ⟦ Q2 ⟧) (at level 90, c at next level). *)

Definition afalse_assn : assertion := fun _ => False.


Inductive Inc_triple: assertion -> com -> postassertion -> Prop :=
| Inc_triple_skip: forall P,
    ⟦ P ⟧ SKIP ⟦ P ⟧
where "⟦ P ⟧ c ⟦ Q ⟧" := (Inc_triple P c (fun r => match r with
    | RNormal s => Q s
    | RError => False
    end)).