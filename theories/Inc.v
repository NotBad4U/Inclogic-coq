From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import MSets.MSetList.
Require Export Coq.Strings.String.
From Coq Require Import Lists.List.
Require Import Ltac2.Option.

Require Import StringAsOT.
Require Import StateMap.

Import ListNotations.
 
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNot (b : bexp)
.

Inductive com : Type :=
  | Skip
  | Asign: string -> aexp -> com
  | Seq : com -> com -> com
  | Assume : bexp -> com
  | Error: com
  | Star: com -> com
  | Choice: com -> com -> com.

Coercion AId : string >-> aexp.

Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

(* Eval compute in  InA_cons_hd M.E ("Y"%string :: "X"%string :: nil). *)

(* witch to aevalR *)
Fixpoint aeval (st : state) (a : aexp) : option nat :=
  match a with
  | ANum n => Some n
  | AId x => StateMap.get st x
  | <{a1 + a2}> => 
      match (aeval st a1), (aeval st a2) with
      | Some va1, Some va2 => Some (va1 + va2)
      | _, _ => None
      end
  end.

Definition equal_option [A B] (eq : A -> B -> bool) (a : option A) (b : option B) : bool
  := match a with
     | None => match b with
               | None => true
               | _ => false
               end
     | Some a => match b with
                 | Some b => eq a b
                 | _ => false
                 end
     end.

Fixpoint beval (st : state) (b : bexp): bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => equal_option (Nat.eqb) (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  end.


Reserved  Notation "'assume' l " 
          (in custom com at level 8, l custom com at level 0).
Reserved Notation "x ; y" (in custom com at level 90, right associativity).

Notation "x := y" :=
         (Asign x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "'local' x " :=
        (Asign x (ANum 0))
          (in custom com at level 8, x custom com at level 0) : com_scope.
Notation "'skip'" :=
         Skip (in custom com at level 0) : com_scope.
Notation "x ; y" :=
         (Seq x y)
          (in custom com at level 90, right associativity) : com_scope.
Notation "'assume' l " :=
        (Assume l)
          (in custom com at level 8, l custom com at level 0) : com_scope.
Notation "'error()'" :=
          Error (in custom com at level 0) : com_scope.
Notation "c '⋆'" :=
        (Star c) (in custom com at level 8) : com_scope.
Notation "x '⨁' y " :=
        (Choice x y) (in custom com at level 8) : com_scope.

(* Notations for while, if and assert keywords *)

Definition While b c := <{ (assume b ; c)⋆ ; assume ~ b }>.

Notation "'while' b 'do' c" :=
  (While b c)
  (in custom com at level 10, b at next level, c at next level) : com_scope.

Definition If b c c' := <{ (assume b ; c) ⨁ ((assume ~ b) ; c') }>.

Notation "'if' b 'then' c 'else' c'" :=
  (If b c c')
  (in custom com at level 10, c at next level, c' at next level) : com_scope.

Definition Assert b := <{ (assume b) ⨁ ((assume ~ b) ; error()) }>.

Notation "'assert' '(' c ')' " :=
  (Assert c) (in custom com at level 8) : com_scope.

Definition Assertion := state -> Prop.

Definition Aexp : Type := state -> option nat.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => Some n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

(* Sortclass, the class of sorts; its objects are the terms whose type is a sort (e.g. Prop or Type).  *)
Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assertion P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assertion P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assertion P st /\  assertion Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assertion P st \/ assertion Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assertion P st -> assertion Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assertion P st <-> assertion Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.


Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope inclogic_spec_scope.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : inclogic_spec_scope.
Open Scope inclogic_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : inclogic_spec_scope. 


(* Notation "'if' B 'then' T else E" :=
  ((assume (B) ; C) ⨁ (assume (~B) ; C))
  in custom com at level 80) : com_scope. *)

(* Notation "'assert' B" :=
  (assume (B) ⨁ (assume (~B) ; error()))
  in custom com at level 80) : com_scope. *)


Reserved Notation
         "st '=[' c ']=>' ϵ ':' st'"
         (at level 40, c custom com at level 99,
          st constr, ϵ constr at next level).


Inductive Signal: Type := 
| ok
| err.

Inductive ceval : com -> state -> Signal -> state -> Prop :=
| E_Skip : forall st,
  st =[ skip ]=> ok : st
| E_Local : forall st x,
  st =[ local x ]=> ok : (x !-> 0 ; st)
| E_Asgn : forall st a n x,
  aeval st a = Some n ->
  st =[ x := a ]=> ok : (x !-> n ; st)
(* Alternative version
| E_Asgn : forall st a n x st',
  aeval st a = n ->
  st' = (x !-> n ; st) ->
  st =[ x := a ]=> ok : st' *)
| E_Seq_Norm : forall c1 c2 st st' st'' ϵ,
  st =[ c1 ]=> ok : st' ->
  st' =[ c2 ]=> ϵ : st'' ->
  st =[ c1 ; c2 ]=> ϵ : st''
| E_Seq_Err : forall c1 c2 st st',
  st =[ c1 ]=> err : st' ->
  st =[ c1 ; c2 ]=> err : st'
 | E_Assume : forall st b,
  beval st b = true ->
  st =[ assume b ]=> ok : st
| E_Error: forall st,
  st =[ error() ]=> err: st
| E_StarZero : forall c st ϵ,
  st =[ c ⋆ ]=> ϵ : st
| E_StarNonZero : forall c st st' ϵ,
  st =[ c ⋆ ; c  ]=> ϵ : st' ->
  st =[ c ⋆ ]=> ϵ : st'
| E_ChoiceLeft: forall x y st st' ϵ,
  st =[ x ]=> ϵ : st' ->
  st =[ x ⨁ y ]=> ϵ : st'
| E_ChoiceRight: forall x y st st' ϵ,
  st =[ y ]=> ϵ : st' ->
  st =[ x ⨁ y ]=> ϵ : st'
where "st =[ c ]=> ϵ : st'" := (ceval c st ϵ st').

Local Hint Constructors ceval : core.

Definition Inc_triple
           (P : Assertion) (c : com) (s: Signal) (Q: Assertion): Prop :=
    forall st',
    Q st' ->
    exists st,
    st =[ c ]=> s : st' /\ P st.

Notation "[[ P ]] c [[ ϵ ↑ Q ]]" :=
  (Inc_triple P c ϵ Q) (at level 90, c custom com at level 99): inclogic_spec_scope.    

Notation "[[ P ]] c [[ ok ↑ Q ]] [[ err ↑ R ]] " :=
  ([[ P ]] c [[ ok ↑ Q ]] /\ [[ P ]] c [[ err ↑ R ]]) (at level 90, c custom com at level 99): inclogic_spec_scope.


(*
  [p]C1[ok:q] [q]C2[ϵ:r]
  ----------------------- ( d (normal))
  [p]C1;C2[ϵ:r]
*)
Theorem HInc_Sequence_norm : forall P Q R c1 c2 ε,
  [[ P ]] c1 [[ ok ↑ Q ]] -> 
  [[ Q ]] c2 [[ ε ↑ R ]] -> 
  [[ P ]] c1;c2 [[ ε ↑ R ]].
Proof.
  intros P Q R c1 c2 ε H1 H2 st' HR. (* st' HSeq.  HIncC1 HIncC2 st st'0 HSeq HPostR. *)
  unfold Inc_triple in H2.
  specialize (H2 _ HR) as [ st1 [ST1 QST1] ].
  unfold Inc_triple in H1.
  specialize (H1 _ QST1) as [st2 [ST2 QST2] ].
  exists st2. eauto.
Qed.

(*
  [p] C1 [ϵ:r]
  ----------------------- ( d (short-circuit))
  [p] C1;C2 [ϵ:r]
*)
Theorem HInc_Sequence_short : forall P Q c1 c2,
  [[ P ]] c1 [[ err ↑ Q ]] -> 
  [[ P ]] c1;c2 [[ err ↑ Q ]].
Proof.
  intros P Q c1 c2 HIncC1 st' Qst'.
  specialize (HIncC1 _ Qst') as [ st [E ST] ].
  exists st. eauto.
Qed.

(* [p]c[ε: q] ∧ q ⇐ q′ ⇒ [p]c[ε: q′]  *)
Lemma Consequence_Post : forall (P Q' Q : Assertion) ε c,
  [[ P ]] c  [[ ε ↑ Q ]] ->
  Q' ->> Q ->
  [[ P ]] c [[ ε ↑ Q' ]].
Proof.
  intros P Q' Q ε c HInc Himp st' Hpost.
  apply HInc with (st' := st').
  apply Himp.
  assumption.
Qed.

(* p′ ⇐ p ∧ [p]c[ε: q] ⇒ [p′]c[ε: q]  *)
Lemma Consequence_Pre : forall (P P' Q : Assertion) ε c,
  [[ P ]] c  [[ ε ↑ Q ]] ->
  P ->> P' ->
  [[ P' ]] c [[ ε ↑ Q ]].
  intros P P' Q ε c HInc Himp st' Hpost.
  unfold Inc_triple in HInc.
  specialize (HInc _ Hpost) as [ st [E ST] ].
  exists st.
  split.
  - assumption.
  - apply Himp.
    assumption.
Qed.

(*
  Incorrectness logic’s rule of consequence lets us enlarge (weaken) the pre
  and shrink (strengthen) the post-assertion.

  p' <= p   [p] C [ε: q]  q <= q'
  -------------------------------
  [p′]C[ε: q′]
*)
Theorem HInc_Consequence : forall P Q P' Q' ε c,
  [[ P ]] c [[ ε ↑ Q ]] -> 
  P ->> P' ->
  Q' ->> Q ->
  [[ P' ]] c [[ ε ↑ Q' ]].
Proof.
  intros P Q P' Q' ε c  Htriple Hpre Hpost.
  apply Consequence_Pre with (P := P).
  -  apply Consequence_Post with (Q := Q).
    + assumption.
    + assumption.
  - assumption.
Qed.

(*
  Incorrectness logic deny weakening the post-condition, it supports other rules like 'discard_disjunction'
  which allow us to focus on fewer than all the paths, a feature which is a hallmark of underapproximation.

  [p] C [ε: q1 ∨ q2]
  --------------
  [p] C [ε: q1]

  This rule is a particular case of the Consequence rule.
*)
Lemma discard_disjunction: forall (P Q1 Q2 : Assertion) (ε: Signal) (c: com), [[P]] c [[ ε ↑  Q1 \/ Q2]] -> [[ P ]] c [[ ε ↑ Q1 ]].
Proof.
  intros.
  apply (HInc_Consequence P (Q1 \/ Q2) P Q1 ε c);
  unfold "->>" ;eauto.
Qed.

Lemma Inc_or_comm:  forall P Q1 Q2 ε c, [[ P ]] c [[ε ↑ Q1 \/ Q2 ]] <-> [[ P ]] c [[ ε ↑ Q2 \/ Q1  ]].
Proof.
  intros P Q1 Q2 ε c.
  split;
  try (
    intros HLeft st' HPost;
    apply or_comm in HPost;
    eapply HLeft;
    assumption
  ).
Qed.

(*
  [p1]C[ϵ:q1] [p2]C[ϵ:q2]
  ----------------------- (Disjunction)
  [p1 ∨ p2]C[ϵ:q1 ∨ q2]
*)
Theorem Inc_disjunction: forall P1 P2 c ε Q1 Q2,
  [[ P1 ]] c [[ ε ↑ Q1 ]] -> 
  [[ P2 ]] c [[ ε ↑ Q2 ]] -> 
  [[ P1 \/ P2 ]] c [[ ε ↑ Q1 \/ Q2 ]].
Proof.
  intros P1 P2 c ε Q1 Q2 HP1Q1 HP2Q2.
  unfold Inc_triple.
  intros.
  destruct H as [ HP1 | HP2 ].
  - unfold Inc_triple in HP1Q1.
    specialize (HP1Q1 _ HP1) as [ st [E ST] ].
    eauto.
  - specialize (HP2Q2 _ HP2) as [ st [E ST] ].
    eauto.
Qed.

(*
  ∧∨ Symmetry: [p]c[q1] ∧ [p]c[q2] ⇐⇒ [p]c[q1 ∨ q2]
               {p}c{q1} ∧ {p}c{q2} ⇐⇒ {p}c{q1 ∧ q2}

*)
Theorem Inc_sym_and_or: forall P Q1 Q2 ε c,
  [[ P ]] c [[ ε ↑ Q1 ]] [[ ε ↑ Q2 ]] <-> [[ P ]] c [[ ε ↑ Q1 \/ Q2  ]].
Proof.
  intros.
  split.
  (* -> *)
  - intro H.
    destruct H as [HIncQ1 HIncQ2].
    intros st' [ HQ1 | HQ2 ].
    + eapply HIncQ1 ; eauto.
    + eapply HIncQ2 ; eauto.
  - (* <- *)
    intro H.
    unfold Inc_triple.
    split.
    + intros st' H1.
      apply (discard_disjunction P Q1 Q2 ε c) in H.
      unfold Inc_triple in H.
      apply (H st' H1).
    + intros st' H2.
      rewrite (Inc_or_comm _ _ _ _ ) in H.
      apply (discard_disjunction P Q2 Q1 ε c) in H.
      unfold Inc_triple in H.
      apply (H st' H2).
Qed.

(**
 --------------------  (Skip)
      [[ P ]] skip [[ok: P ]] [[er: False ]]
*)
Theorem Inc_skip : forall P,
  [[ P ]] skip [[ ok ↑ P ]] [[ err ↑ False ]].
Proof.
  intros P.
  split.
  - intros st HQ.
    exists st.
    eauto.
  - intros st' HPost.
    contradiction.
Qed.


(**
 --------------------  (Empty under-approximates)
      [[p]] C [[ϵ: false]]
*)
Theorem Empty_under_approximates: forall P c ε, [[ P ]] c [[ ε ↑ False ]].
Proof.
  intros P c ε st' HFalse.
  contradiction.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).
Coercion bassn : bexp >-> Assertion.
Arguments bassn /.

(*
  ----------------------- (Assume)
  [p] assume B [ok: p /\ B][err: False]
*)
Theorem HInc_Assume : forall P B,
  [[ P ]] assume B [[ ok ↑ P /\ B ]] [[ err ↑ False ]].
Proof.
  intros P B.
  split.
  - intros st' [ HP HB ]. 
    exists st'.
    split; eauto.
  - intros st' HFalse.
    contradiction.
Qed.

(*
  ----------------------- (Assert)
  [p] error () [ok: false][err: p]
*)
Theorem HInc_Assert : forall P,
  [[ P ]] error() [[ ok ↑ False ]] [[ err ↑ P ]].
Proof.
  intro P.
  split.
  - intros st' HFalse.
    contradiction.
  - intros st' HPost.
    exists st'; eauto.
Qed.

(* 
  ----------------------- Iterate zero
  [p] C⋆ [ok:p]
*)
Theorem HInc_IterateZero : forall P c,
  [[ P ]] c ⋆ [[ ok ↑ P ]].
Proof.
  intros P c st' HPost.
  exists st'.
  eauto.
Qed.

(*
  [p] C⋆ ; C [ε:q]
  ----------------------- (Iterate non-zero)
  [p] C⋆ [ε:q]
*)
Theorem HInc_IterateNonZero : forall P c ε Q,
[[ P ]] c ⋆ ; c [[ ε ↑ Q ]] ->
  [[ P ]] c ⋆ [[ ε ↑ Q ]].
Proof.
  intros P c ε Q HCstarSeq st' HQ.
  specialize (HCstarSeq st' HQ) as [ st [ Heval HP ] ].
  inversion Heval; subst; eauto.  
Qed.

Reserved Notation "C'^'n" (at level 1, no associativity).


Fixpoint Cpow (n: nat) (C: com): com := 
match n with
| 0 => <{skip}>
| S m => <{ C ; Cpow m C }>
end.



(*
  -------------------------------------------------- (Assignment)
  [p]x = e[ok: ∃x′.p[x′/x] ∧ x = e[x′/x]][er: false]
*)
Theorem hoare_asgn : forall X P a,
  [[ fun st => P st ]]
    X := a
  [[ ok ↑ fun st' =>  exists m, M.MapsTo X m st' /\ P (set st' X m) /\ (StateMap.get st' X) = aeval (set st' X m) a ]] [[ err ↑ False ]].
Proof with auto.
  intros X p a.
  unfold StateMap.get.
  split.
  - intros st'  [m [Hmap [Hm1 Hm2] ] ].
    exists (X !-> m ; st').
    split...
    pattern st' at 2.
    replace st' with (X !-> m; X !-> m; st').
    + apply E_Asgn.
      rewrite (StateMap.M.find_1 Hmap) in Hm2.
      symmetry...
    + rewrite t_update_shadow.
      rewrite t_update_same...
      apply (M.find_1 Hmap).
  - apply Empty_under_approximates.
Qed.

(*
Theorem inc_asgn : forall X P a,
  [[ fun st' => P st' ]]
    X := a
  [[ ok ↑ fun st => exists m, P (X !-> m ; st) /\ st X = aeval (X !-> m; st) a ]] [[ err ↑ False ]].
Proof with auto.
  intros X p a.
  split.
  - intros st [m [Hm1 Hm2] ].
    exists (X !-> m ; st).
    split...
    apply E_Asgn with (n := st X)...
    rewrite t_update_shadow.
    now rewrite t_update_same.
  - apply Empty_under_approximates.
Qed.
*)

(*
  [p] C_i [ϵ:q]
  ----------------------- (Choice (where i = 1 or 2))
  [p] C1 + C2 [ε:q]
*)
Theorem IncChoiceLeft : forall P Q c1 c2 ε,
  [[ P ]] c1 [[ ε ↑ Q ]]
  ->
  [[ P ]] c1 ⨁ c2 [[ ε ↑ Q ]].
Proof.
  intros P Q c1 c2 ϵ HTriplec1 st' HPost.
  specialize (HTriplec1 _ HPost) as [ st [ Hc1Eval HPre ] ].
  eauto.
Qed.

Theorem IncChoiceRight : forall P Q c1 c2 ε,
  [[ P ]] c2 [[ ε ↑ Q ]]
  ->
  [[ P ]] c1 ⨁ c2 [[ ε ↑ Q ]].
Proof.
  intros P Q c1 c2 ϵ HTriplec2 st' HPost.
  specialize (HTriplec2 _ HPost) as [ st [ Hc1Eval HPre ] ].
  eauto.
Qed.

(*
  [p] C_1 [ϵ:q] [p] C_2 [ϵ:q]
  ----------------------- (Choice (where i = 1 or 2))
  [p] C1 + C2 [ε:q]
*)
Theorem DerivedRuleofChoice : forall P Q1 Q2 c1 c2 ε,
  [[ P ]] c1 [[ ε ↑ Q1 ]]
  ->
  [[ P ]] c2 [[ ε ↑ Q2 ]]
  -> 
  [[ P ]] c1 ⨁ c2 [[ ε ↑ Q1 \/ Q2 ]].
Proof with auto.
  intros P Q1 Q2 c1 c2 ϵ H1 H2 st' [HQ1 | HQ2].
  - specialize (H1 _ HQ1) as [ st1 [ Hc1Eval HPre ] ].
    exists st1...
  - specialize (H2 _ HQ2) as [ st2 [ Hc2Eval HPre2 ] ].
    exists st2...  
Qed.


(* x is free in p if p is invariant under changing x
  : i.e., σ ∈ p ⇔ ∀ v. (σ | x ↦ v) ∈ p, where (σ | x ↦ v) for the 
  function like σ except that x maps to v.
*)
Definition Free x p : Prop := forall st, p st -> forall v, p (x !-> v ; st) .

Module FsetString := FSetList.Make(String_as_OT). 

(* Mod(C) is the set of variables modified by assignment statements in C *)
Fixpoint Mod (c: com): FsetString.t :=
match c with 
| Asign s a => FsetString.singleton s
| Seq c1 c2 => FsetString.union (Mod c1) (Mod c2) 
| _ => FsetString.empty
end.

Example ModTest1 : FsetString.elements (Mod <{ "X" := 1 ; skip ; "Y" := 2  }>)  = [ "X"%string ; "Y"%string ].
Proof. reflexivity. Qed.

Example ModTest2 : FsetString.elements (Mod <{ "X" := 1  }>)  = [ "X"%string ].
Proof. reflexivity. Qed.

(* The rules of Substitution and Constancy, as well as Consequence, are important for adapting
specifications for use in different contexts *)


(* P' that is just like P except that, wherever P looks up the variable X in the current state, P' instead uses the value of the expression a. *)
Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    exists v, (aeval st a) = Some v -> P (set st X v).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).


Theorem Constancy : forall P Q F c ε,
  [[ P ]] c [[ ε ↑ Q ]]
  ->
  [[ P /\ F ]] c [[ ε ↑ Q /\ F ]].
Proof.
intros  P Q F c ε H st' [HQ HF].
unfold Inc_triple in H.
specialize (H st' HQ) as [ st [Hceval HP] ].
exists st.
split.
assumption.
split.
assumption.
Admitted.


Theorem Subst1 : forall P Q c ε e x,
  [[ P ]] c [[ ε ↑ Q ]]
  ->
  [[ P [e |-> x] ]] c [[ ε ↑ Q [e |-> x ] ]].
Proof.
Admitted.


(*  Local BEGIN VAR V1; · · · VAR Vn; C END
  Semantics: command C is executed, then the values of V1, · · · , Vn
  are restored to the values they had before the block was entered

*)
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".


(* weakest under-approximate post 
  It is similar to the Hoare Strongest Postconditions
  If {P} S {Q} and for all Q’ such that {P} S {Q’}, Q ⇒ Q’, then Q is the strongest postcondition of S with respect to P

  - StrongestOverPost(r)p = ⋀ {q | {p}r{q} holds}
  - WeakestUnderPost(r)p = ⋁ {q | [p]r[q] holds}

  Proposition 8. StrongestOverPost(r) = WeakestUnderPost(r) = post(r)
  NOTE: we define the n-ary disjunction ⋁ {q | φ q } by `exists`
*)
Definition wpp P c Q ε :=
  [[ P ]] c [[ ε ↑ Q ]] /\
  exists Q', [[ P ]] c [[ ε ↑ Q' ]] -> (Q ->> Q').


(* TODO: Make a more concrete example to challenge wpp *)
Example is_wpp: wpp (fun st => True) <{ skip }> (fun st => True) ok. 
Admitted.

Declare Scope hoare_spec_scope.

Open Scope hoare_spec_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (s: Signal) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> s: st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ ε Q }}" :=
(hoare_triple P c ε Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(* Principle of Agreement : [u]c[u'] ∧ u ⇒ o ∧ {o}c{o'} ⇒ u' => o' *)
Lemma Agreement: forall IPRe IPost c ε HPre HPost, [[IPRe]] c [[ ε ↑ IPost ]] /\ IPRe ->> HPre /\ (hoare_triple HPre c ε HPost) -> IPost ->> HPost.
Proof.
  intros IPRe IPost c ε HPre HPost [ HTripleInc [ HyIPReimpHPre HTripleHoare ] ] st' HIpost.
  apply HTripleInc in HIpost.
  destruct HIpost as [ st [ HInceval HIPre ] ].
  apply HyIPReimpHPre in HIPre.
  eapply HTripleHoare in HIPre; eauto.
Qed.

(* Principle of Denial: [u]c[u'] ∧ u ⇒ o ∧ ¬(u' ⇒ o') ⇒ ¬({o}c{o'}) *)
Lemma Denial: forall IPRe IPost c ε HPre HPost, [[IPRe]] c [[ ε ↑ IPost ]] /\ IPRe ->> HPre /\ ~(IPost ->> HPost) ->  ~(hoare_triple HPre c ε HPost).
Proof.
  intros IPRe IPost c ε HPre HPost [ HTripleInc [ HyIPReimpHPre HnotIPostimpHpost ] ] HTripleHoare.
  apply HnotIPostimpHpost.
  unfold "->>".
  intros st' HIpost.
  apply HTripleInc in HIpost.
  destruct HIpost as [ st [ HInceval HIPre ] ].
  apply HyIPReimpHPre in HIPre.
  eapply HTripleHoare in HIPre; eauto.
Qed.