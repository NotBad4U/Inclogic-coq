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
Require Import Imp.
Require Import Hoare.

Import ListNotations.

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


Local Hint Constructors ceval : core.

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

(* FIXME: *)
(*
  [p(n)] C [ok: p(n+1)]
  ----------------------- (Backwards Variant (where n fresh))
  [p(0)] C⋆ [ε: ∃ n. p(n)]
*)
Theorem Inc_IterBackwardsVariant : forall (P: nat -> Assertion) c ε,
  (forall n: nat,
  [[ (P n) ]] c [[ ε ↑ (P (n + 1) ) ]]) ->
  [[ (P 0) ]] c ⋆ [[ ε ↑ fun st' =>  exists m, (P m) st' ]].
Proof.
  intros P c ε H st' [ m HPost].
  unfold Inc_triple in H.
  induction m.
  - admit.
  - apply IHm.
    assert (H2 : S m = m + 1). apply (eq_sym (add_1_r m)).
    rewrite H2 in HPost.
    specialize (H m st' HPost) as [st [Heval Hpre] ].
Admitted.



Reserved Notation "C'^'n" (at level 1, no associativity).


Fixpoint Cpow (n: nat) (C: com): com := 
match n with
| 0 => <{skip}>
| S m => <{ C ; Cpow m C }>
end.

(* FIXME: *)
Theorem DeriveIteration : forall P c ε Q b,
  forall x, x < b -> [[ P ]] Cpow x c [[ ε ↑ Q ]] ->
  [[ P ]] c ⋆ [[ ε ↑ fun st' => x < b -> Q st' ]].
Proof with auto.
  (* intros P c ε Q b x H HCstarSeq st HQ.
  destruct x.
  - simpl in *. exists st.
    specialize (HQ H).
    specialize (HCstarSeq st HQ) as [ st' [ Heval HP ] ].
    inversion Heval. subst.
    split...
  - simpl in *.
    specialize (HQ H).
    (* unfold Inc_triple in HCstarSeq. *)
    pose (HCstarSeq st HQ).
    destruct e as [ st' [ Heval HP ] ].
    unfold Inc_triple in HCstarSeq.
    apply lt_succ_l in H.
    exists st'.

    admit. *)
    (* apply IHx H  *)
  (* specialize (HCstarSeq st' HQ) as [ st [ Heval HP ] ]. *)
  (* inversion Heval; subst; eauto.   *)
Admitted.

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

(* substAexp x y a, which replaces all occurrences of a variable x with a value y inside an arithmetic expression a. *)
Fixpoint substAexp (x: string) (y: aexp) (a: aexp) : aexp :=
match a with
  | ANum n => ANum n
  | AId var => if var_eq x var then y else x
  | <{a1 + a2}> => <{(substAexp x y a1) + (substAexp x y a2)}>
end.

(* substBeval x y b, which replaces all occurrences of a variable x with a value y inside a boolean expression b. *)
Fixpoint substBeval (x: string) (y: aexp) (b: bexp) : bexp :=
let auxa t := substAexp x y t in
let aux t := substBeval x y t in
match b with
| BTrue => BTrue
| BFalse => BFalse
| BEq a1 a2 => BEq (auxa a1) (auxa a2)
| BNot b => aux b
end.

(* subst x y c, which replaces all occurrences of a variable x with a value y inside a command c. *)
Fixpoint substCmd (x: string) (y: aexp) (c: com) : com :=
let aux t := substCmd x y t in
match y with 
| AId yvar => 
  let if_y_eq z t1 t2 := if var_eq x z then t1 (* change nothing *) else t2 (* update *) in
  match c with
  | Skip => Skip
  | Asign x' v =>  if_y_eq x' (Asign yvar (substAexp x y v)) (Asign x' (substAexp x y v)) 
  | Seq c1 c2 => Seq (aux c1) (aux c2) 
  | Assume b => Assume b
  | Error => Error
  | Star c => Star (aux c)
  | Choice c1 c2 => Choice (aux c1) (aux c2)
  | CLocal x' c' => if_y_eq x' (CLocal yvar (aux c')) (CLocal x' (aux c'))
  end
| w => 
  match c with
  | Skip => Skip
  | Asign var exp =>  (Asign var (substAexp x w exp))
  | Seq c1 c2 => Seq (aux c1) (aux c2) 
  | Assume b => Assume (substBeval x w b)
  | Error => Error
  | Star c => Star (aux c)
  | Choice c1 c2 => Choice (aux c1) (aux c2)
  | CLocal x' c' => (CLocal x' (aux c'))
  end
end.

Example testsubstCmd: substCmd "X"%string (AId "Y"%string)
  <{ "X" := (AId "X"%string); skip; "Z" :=  (AId "X"%string)}> 
  = <{ "Y" := (AId "Y"%string); skip; "Z" :=  (AId "Y"%string)}>.
Proof. reflexivity. Qed.


Example testsubstCmd2: substCmd "X"%string (APlus (ANum 1) (ANum 1))
  <{ "Y" := (AId "X"%string); skip; "Z" :=  (APlus (ANum 1) (AId "X"%string))}> 
  = <{ "Y" := (APlus (ANum 1) (ANum 1)); skip; "Z" := (APlus (ANum 1) (APlus (ANum 1) (ANum 1)))}>.
Proof. reflexivity. Qed.



(* Local Variable

  [p] C (y/x) [ϵ:q]
  ------------------------- y ∈ Free(p, C)  
  [p] local x. C [ε: ∃y. q]
*)
Theorem LocalVariable : forall P Q F (C: com) (y: aexp) (x: string) ε,
  [[ P ]] substCmd x y C [[ ε ↑ Q ]]
  ->
  [[ P /\ F ]] local x . C [[ ε ↑ Q /\ F ]].
Proof.
Admitted.

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
  [[ P [x |-> e] ]] substCmd x e c [[ ε ↑ Q [x |-> e ] ]].
Proof.
Admitted.

Theorem Subst2 : forall P Q c ε y x,
  [[ P ]] c [[ ε ↑ Q ]]
  ->
  [[ P [x |-> y] ]] substCmd x y c [[ ε ↑ Q [x |-> y ] ]].
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
