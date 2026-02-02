From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality.
From IncLogic Require Import Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * 1.  The IMP language *)

(** ** 1.1 Arithmetic expressions *)

Definition ident := string.

(** The abstract syntax: an arithmetic expression is either... *)

Inductive aexp : Type :=
  | CONST (n: Z)                       (**r a constant, or *)
  | VAR (x: ident)                     (**r a variable, or *)
  | PLUS (a1: aexp) (a2: aexp)         (**r a sum of two expressions, or *)
  | MINUS (a1: aexp) (a2: aexp).       (**r a difference of two expressions *)

Definition store : Type := ident -> Z.

Fixpoint aeval (a: aexp) (s: store) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  end.

Eval compute in (aeval (PLUS (VAR "x") (MINUS (VAR "x") (CONST 1)))  (fun x => 2)).

Eval cbn in (aeval (PLUS (VAR "x") (MINUS (CONST 10) (CONST 1)))) (fun x => 2).

(** Result: [ = fun s : store => s "x" + 9 ]. *)

(** We can prove mathematical properties of a given expression. *)

Lemma aeval_xplus1:
  forall s x, aeval (PLUS (VAR x) (CONST 1)) s > aeval (VAR x) s.
Proof.
  intros. cbn. lia.
Qed.

(** Finally, we can prove "meta-properties" that hold for all expressions.
  For example: the value of an expression depends only on the values of its
  free variables.

  Free variables are defined by this recursive predicate:
*)
Fixpoint free_in_aexp (x: ident) (a: aexp) : Prop :=
  match a with
  | CONST n => False
  | VAR y => y = x
  | PLUS a1 a2 | MINUS a1 a2 => free_in_aexp x a1 \/ free_in_aexp x a2
  end.

Theorem aeval_free:
  forall s1 s2 a,
  (forall x, free_in_aexp x a -> s1 x = s2 x) ->
  aeval a s1 = aeval a s2.
Proof.
  induction a; cbn; intros SAMEFREE.
- (* Case a = CONST n *)
  auto.
- (* Case a = VAR x *)
  apply SAMEFREE. auto.
- (* Case a = PLUS a1 a2 *)
  rewrite IHa1, IHa2; auto.
- (* Case a = MINUS a1 a2 *)
  rewrite IHa1, IHa2; auto.
Qed.

Definition OPP (a: aexp) : aexp := MINUS (CONST 0) a.

Lemma aeval_OPP: forall s a, aeval (OPP a) s = - (aeval a s).
Proof.
  intros; cbn. lia.
Qed.

(** The IMP language has conditional statements (if/then/else) and
  loops.  They are controlled by expressions that evaluate to Boolean
  values.  Here is the abstract syntax of Boolean expressions. *)

Inductive bexp : Type :=
  | TRUE                              (**r always true *)
  | FALSE                             (**r always false *)
  | EQUAL (a1: aexp) (a2: aexp)       (**r whether [a1 = a2] *)
  | LESSEQUAL (a1: aexp) (a2: aexp)   (**r whether [a1 <= a2] *)
  | EVEN (a1: aexp)                   (**r whether [a1] evaluates to an even integer *)
  | NOT (b1: bexp)                    (**r Boolean negation *)
  | AND (b1: bexp) (b2: bexp).        (**r Boolean conjunction *)

(** Just like arithmetic expressions evaluate to integers,
  Boolean expressions evaluate to Boolean values [true] or [false]. *)

Fixpoint beval (b: bexp) (s: store) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval a1 s =? aeval a2 s
  | LESSEQUAL a1 a2 => aeval a1 s <=? aeval a2 s
  | EVEN a1 => Z.even (aeval a1 s)
  | NOT b1 => negb (beval b1 s)
  | AND b1 b2 => beval b1 s && beval b2 s
  end.

(** There are many useful derived forms. *)

Definition NOTEQUAL (a1 a2: aexp) : bexp := NOT (EQUAL a1 a2).

Definition GREATEREQUAL (a1 a2: aexp) : bexp := LESSEQUAL a2 a1.

Definition GREATER (a1 a2: aexp) : bexp := NOT (LESSEQUAL a1 a2).

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).

(** Derived form: evenness test on arithmetic expressions. *)
Definition ODD (a: aexp) : bexp := NOT (EVEN a).

(** ** 1.2 Commands *)
Declare Custom Entry com.
Declare Scope com_scope.
Delimit Scope com_scope with com.
Local Open Scope com_scope.

Notation "x + y" := (PLUS x y) (in custom com at level 50, left associativity).
Notation "x - y" := (MINUS x y) (in custom com at level 50, left associativity).

(**  Commands *)

Inductive com: Type :=
  | SKIP                         (**r do nothing *)
  | ERROR                        (**r interrupt the program *)
  | ASSIGN (x: ident) (a: aexp)  (**r assignment: [v := a] *)
  | NONDET (x: ident)            (**r non-deterministic assignment to [x] *)
  | ASSUME (b: bexp)             (**r assume that [b] holds *)
  | SEQ (c1: com) (c2: com)      (**r sequence: [c1; c2] *)
  | CHOICE (c1: com) (c2: com)   (**r non-deterministic choice: [c1 + c2] *)
  | CSTAR (c1: com).             (**r non-deterministic iteration: [c1★] *)

(** We can write [c1 ;; c2] instead of [SEQ c1 c2], it is easier on the eyes. *)

Infix ";;" := SEQ (at level 80, right associativity).

Notation "c1 '⊕' c2" := (CHOICE c1 c2)
                         (in custom com at level 85, right associativity).

Notation "c '★'" := (CSTAR c)
                         (in custom com at level 90, right associativity).

Notation "c '★'" := (CSTAR c)
                         (at level 90, right associativity) : com_scope.

(** We can now define the syntax of while-loops in terms of the core IMP commands. *)
Notation "'WHILE' b 'DO' c 'END'" :=
  (((ASSUME b ;; c) ★) ;; ASSUME (NOT b))
    (at level 95, right associativity) : com_scope.

(** Similarly, we can define conditional statements.

    Note: Coq does not handle an “optional ELSE” well when both notations
    start with exactly the same prefix [IF ... THEN ...].

    To keep the convenient no-ELSE syntax, we reserve [IF ... THEN ... END]
    for the no-ELSE form, and introduce a separate keyword [IFELSE] for the
    form with [ELSE]. *)
Notation "'IF' b 'THEN' c1 'ELSE' c2 'END'" :=
  (CHOICE
     (ASSUME b ;; c1)
     (ASSUME (NOT b) ;; c2))
    (at level 89, right associativity,
     b at level 99,
     c1 at level 89,
     c2 at level 89) : com_scope.

Notation "'IF' b 'THEN' c1 'END'" :=
  (IF b THEN c1 ELSE SKIP END)
  (at level 90, right associativity,
   b at level 99,
   c1 at level 89,
   only parsing) : com_scope.

Notation "'ASSERT' b" :=
  (CHOICE
     (ASSUME b)
     (ASSUME (NOT b) ;; ERROR))
    (at level 100, right associativity) : com_scope.

(** Here is an example arithmetic expression: *)

(** Here is an example IMP program that computes the Euclidean division
    of two natural numbers [a] and [b], storing the quotient in variable
    ["q"] and the remainder in variable ["r"].  We assume that [b > 0]. *)

Definition Euclidean_division: com :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE (LESSEQUAL (VAR "b") (VAR "r")) DO
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1)))
  END.

(** Example in section 3.1 *)
Definition Under_approximating_ex: com :=
  IF (EVEN (VAR "x")) THEN
    IF (ODD (VAR "y")) THEN
      ASSIGN "z" (CONST 42)
    ELSE
      SKIP
    END
  END.

(** ** 1.3 Small-step operational semantics *)

(** A useful operation over stores:
    [update x v s] is the store that maps [x] to [v] and is equal to [s] for
    all variables other than [x]. *)

Definition update (x: ident) (v: Z) (s: store) : store :=
  fun y => if string_dec x y then v else s y.

Lemma update_same: forall x v s, (update x v s) x = v.
Proof.
  unfold update; intros. destruct (string_dec x x); congruence.
Qed.

Lemma update_other: forall x v s y, x <> y -> (update x v s) y = s y.
Proof.
  unfold update; intros. destruct (string_dec x y); congruence.
Qed.

(** The result type indicates the end value of a program, either a state or an error *)
Inductive result : Type :=
| RNormal : store -> result
| RError : result.

(** The relation [ red (c, s) (c', s') ] defines a basic reduction,
    that is, the first computation step when executing command [c]
    in initial memory state [s].
    [s'] is the memory state "after" this computation step.
    [c'] is a command that represent all the computations that remain
    to be performed later.

    The reduction relation is presented as a Coq inductive predicate,
    with one case (one "constructor") for each reduction rule.
*)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval a s) s)
  | red_nondet: forall x s n,
    red (NONDET x, s) (SKIP, update x n s)
  | red_assume_true: forall b s,
    (* beval b s = true -> *)
    red (ASSUME b, s) (SKIP, s)
  (* | red_assume_false: forall b s,
    beval b s = false ->
    red (ASSUME b, s) (ERROR, s) *)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_error: forall c s,
    red (SEQ ERROR c, s) (ERROR, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_choice_left: forall c1 c2 s,
      red (CHOICE c1 c2, s) (c1, s)
  | red_choice_right: forall c1 c2 s,
      red (CHOICE c1 c2, s) (c2, s)
  | red_cstar_done: forall c s,
      red (CSTAR c, s) (SKIP, s)
  | red_cstar_step: forall c s,
      red (CSTAR c, s) (SEQ c (CSTAR c), s).

(** Final configurations for the small-step semantics, corresponding to [result]. *)
Inductive final : com * store -> result -> Prop :=
  | final_skip : forall s,
    final (SKIP, s) (RNormal s)
  | final_error : forall s,
    final (ERROR, s) RError.

  (** Termination for the small-step semantics that returns a [result]. *)
  Definition terminates_result (s: store) (c: com) (r: result) : Prop :=
    exists cs, star red (c, s) cs /\ final cs r.

(** This IMP language is not deterministic due to the nondeterministic choice (+) operator *)
Lemma red_nondeterm :
  exists cs cs1 cs2,
    red cs cs1 /\ red cs cs2 /\ cs1 <> cs2.
Proof.
  exists (CHOICE SKIP (ASSIGN "x" (CONST 1)), fun x => 0).
  exists (SKIP, fun x => 0).
  exists (ASSIGN "x" (CONST 1), fun x => 0).
  split.
  - apply red_choice_left.
  - split.
    + apply red_choice_right.
    + intro. discriminate H.
Qed.

(** We define the semantics of a command by chaining successive reductions.
    The command [c] in initial state [s] terminates with final state [s']
    if we can go from [(c, s)] to [(skip, s')] in a finite number of reductions.
*)

Definition terminates (s: store) (c: com) (s': store) : Prop :=
  star red (c, s) (SKIP, s').

(** The [star] operator is defined in library [Sequences].
    [star R] is the reflexive transitive closure of relation [R].
    On paper it is often written [R*].
    The [star red] relation therefore represents zero, one or several
    reduction steps. *)

(** Likewise, command [c] diverges (fails to terminate) in initial state [s]
    if there exists an infinite sequence of reductions starting with [(c, s)].
    The [infseq] relation operator is defined in library [Sequences].
*)

Definition diverges (s: store) (c: com) : Prop :=
  infseq red (c, s).

(** Generally speaking, a third kind of executions is possible:
    "going wrong" after a finite number of reductions.
   A configuration [(c', s')] "goes wrong" if it cannot reduce and is
   not a final configuration, that is, [c' <> SKIP] and [c' <> ERROR]. *)

Definition goes_wrong (s: store) (c: com) : Prop :=
  exists c', exists s',
  star red (c, s) (c', s') /\ irred red (c', s') /\ c' <> SKIP /\ c' <> ERROR.

(** A command other than [SKIP] can always reduce. *)
Lemma red_progress:
  forall c s,
    c = SKIP \/ c = ERROR \/ exists c', exists s', red (c, s) (c', s').
Proof.
  induction c; intros.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. exists SKIP. exists (update x (aeval a s) s). apply red_assign.
  - right. right. exists SKIP. exists (update x 0 s). apply red_nondet.
  - right. right.  exists SKIP. exists s. apply red_assume_true.
    (* destruct (beval b s) eqn:HB.
     + exists SKIP. exists s. apply red_assume_true. (* exact HB. *)
    + exists ERROR. exists s. apply red_assume_false. exact HB. *)
  - (* SEQ *)
    specialize (IHc1 s) as [Hskip | [Herror | (c' & s' & STEP)]].
    + subst. right. right. exists c2. exists s. apply red_seq_done.
    + subst. right. right. exists ERROR. exists s. apply red_seq_error.
    + right. right. exists (SEQ c' c2). exists s'. apply red_seq_step. exact STEP.
  - right. right. exists c1. exists s. apply red_choice_left.
  - right. right. exists SKIP. exists s. apply red_cstar_done.
Qed.

Lemma not_goes_wrong:
  forall c s, ~(goes_wrong s c).
Proof.
  intros c s (c' & s' & STAR & IRRED & NOTSKIP & NOTERROR).
  (* If [(c',s')] is reachable and [c'] is neither final form, then it must be
     able to take a reduction step (by [red_progress]), contradicting [irred]. *)
  destruct (red_progress c' s') as [EQSKIP | [EQERROR | (c'' & s'' & STEP)]].
  - contradiction.
  - contradiction.
  - unfold irred in IRRED. specialize (IRRED (c'', s'') STEP). contradiction.
Qed.

(* * A technical lemma: a sequence of reductions can take place to the left
    of a [SEQ] constructor.  This generalizes rule [red_seq_step]. *)
Lemma red_seq_steps:
  forall c2 s c s' c',
  star red (c, s) (c', s') -> star red ((c ;; c2), s) ((c' ;; c2), s').
Proof.
  intros. dependent induction H.
- apply star_refl.
- destruct b as [c1 st1].
  apply star_step with (c1;;c2, st1). apply red_seq_step. auto. auto.  
Qed.

(** Natural semantics *)

Reserved Notation "st0 =[ c ]=> st1"
  (at level 40, c at level 99, st1 at level 39).

Inductive cexec: store -> com -> result -> Prop :=
  | cexec_skip: forall s,
      s =[ SKIP ]=> RNormal s
  | cexec_error: forall s,
      s =[ ERROR ]=> RError
  | cexec_assign: forall s x a,
    s =[ ASSIGN x a ]=> RNormal (update x (aeval a s) s)
  | cexec_nondet: forall s x n,
    s =[ NONDET x ]=> RNormal (update x n s)
  | cexec_assume: forall s b,
    (* beval b s = true -> *)
    s =[ ASSUME b ]=> RNormal s
  (* | cexec_assume_false: forall s b,
    beval b s = false ->
    s =[ ASSUME b ]=> RError *)
  | cexec_seq: forall c1 c2 s s' s'',
    s  =[ c1 ]=> RNormal s' ->
    s' =[ c2 ]=> RNormal s'' ->
    s  =[ SEQ c1 c2 ]=> RNormal s''
  | cexec_seq_error: forall c1 c2 s,
    s  =[ c1 ]=> RError ->
    s  =[ SEQ c1 c2 ]=> RError
  | cexec_seq_error_right: forall c1 c2 s s',
    s  =[ c1 ]=> RNormal s' ->
    s' =[ c2 ]=> RError ->
    s  =[ SEQ c1 c2 ]=> RError
  | cexec_choice_left: forall s c1 c2 r,
    s =[ c1 ]=> r ->
    s =[ CHOICE c1 c2 ]=> r
  | cexec_choice_right: forall s c1 c2 r,
    s =[ c2 ]=> r ->
    s =[ CHOICE c1 c2 ]=> r
  | cexec_cstar_done: forall c s,
    s =[ CSTAR c ]=> RNormal s
  | cexec_cstar_step_ok: forall c s s' r,
    s  =[ c ]=> RNormal s' ->
    s' =[ CSTAR c ]=> r ->
    s  =[ CSTAR c ]=> r
  | cexec_cstar_step_error: forall c s,
    s  =[ c ]=> RError ->
    s  =[ CSTAR c ]=> RError
  where "st0 =[ c ]=> st1" := (cexec st0 c st1).

Notation "s1 =[ c ]=> 'ok' ↑ s2" := (cexec s1 c (RNormal s2))
  (at level 40, c at level 99, s2 at level 39).

Notation "s1 =[ c ]=> 'err'" := (cexec s1 c RError)
  (at level 40, c at level 99).

(** We now show an equivalence between evaluations that terminate according
    to the natural semantics
        (existence of a derivation of [cexec s c s'])
    and to the reduction semantics
        (existence of a reduction sequence from [(c,s)] to [(SKIP, s')].

    We start with the natural semantics => reduction sequence direction,
    which is proved by an elegant induction on the derivation of [cexec]. *)

Theorem cexec_to_reds:
  forall s c r, cexec s c r -> terminates_result s c r.
Proof.
  induction 1.
  - (* SKIP *)
    exists (SKIP, s). split.
    + apply star_refl.
    + apply final_skip.
  - (* ERROR *)
    exists (ERROR, s). split.
    + apply star_refl.
    + apply final_error.
  - (* ASSIGN *)
    exists (SKIP, update x (aeval a s) s). split.
    + apply star_one. apply red_assign.
    + apply final_skip.
  - (* NONDET *)
    exists (SKIP, update x n s). split.
    + apply star_one. apply red_nondet.
    + apply final_skip.
  - (* ASSUME true *)
    exists (SKIP, s). split.
     + apply star_one. apply red_assume_true. (*exact H. *)
    + apply final_skip.
   (*-  ASSUME false *)
    (* exists (ERROR, s). split.
    + apply star_one. apply red_assume_false. exact H.
    + apply final_error. *)
  - (* SEQ normal *)
    destruct IHcexec1 as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst cs1.
    destruct IHcexec2 as (cs2 & STAR2 & FINAL2).
    inversion FINAL2; subst cs2.
    exists (SKIP, s''). split.
    + eapply star_trans.
      * apply red_seq_steps with (c2 := c2) in STAR1. exact STAR1.
      * eapply star_step. apply red_seq_done. subst. exact STAR2.
    + apply final_skip.
  - (* SEQ error (left) *)
    destruct IHcexec as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst cs1.
    exists (ERROR, s0). split.
    + eapply star_trans.
      * apply red_seq_steps with (c2 := c2) in STAR1. exact STAR1.
      * apply star_one. apply red_seq_error.
    + apply final_error.
  - (* SEQ error (right) *)
    destruct IHcexec1 as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst cs1.
    destruct IHcexec2 as (cs2 & STAR2 & FINAL2).
    inversion FINAL2; subst cs2.
    exists (ERROR, s1). split.
    + subst.
      eapply star_trans.
      * apply red_seq_steps with (c2 := c2) in STAR1. exact STAR1.
      * eapply star_step.
        -- apply red_seq_done.
        -- exact STAR2.
    + apply final_error.
  - (* CHOICE left *)
    destruct IHcexec as (cs & STAR & FINAL').
    exists cs. split.
    + eapply star_step. apply red_choice_left. exact STAR.
    + exact FINAL'.
  - (* CHOICE right *)
    destruct IHcexec as (cs & STAR & FINAL').
    exists cs. split.
    + eapply star_step. apply red_choice_right. exact STAR.
    + exact FINAL'.
  - (* CSTAR done *)
    exists (SKIP, s). split.
    + apply star_one. apply red_cstar_done.
    + apply final_skip.
  - (* CSTAR step ok *)
    destruct IHcexec1 as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst cs1.
    destruct IHcexec2 as (cs2 & STAR2 & FINAL2).
    exists cs2. split.
    + eapply star_trans.
      * apply star_one. apply red_cstar_step.
      * eapply star_trans.
        -- apply red_seq_steps with (c2 := CSTAR c) in STAR1. exact STAR1.
        -- eapply star_step. apply red_seq_done. subst. exact STAR2.
    + exact FINAL2.
  - (* CSTAR step error *)
    destruct IHcexec as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst cs1.
    exists (ERROR, s0). split.
    + eapply star_trans.
      * apply star_one. apply red_cstar_step.
      * eapply star_trans.
        -- apply red_seq_steps with (c2 := CSTAR c) in STAR1. exact STAR1.
        -- apply star_one. apply red_seq_error.
    + apply final_error.
Qed.

(* * One full body execution yields at least one [red] step from [c★] to [c★]. *)
Lemma plus_cstar_iteration:
  forall c s s',
    star red (c, s) (SKIP, s') ->
    plus red (CSTAR c, s) (CSTAR c, s').
Proof.
  intros c s s' STARC.
  eapply plus_left.
  - apply red_cstar_step.
  - eapply star_trans.
    + (* reduce the body on the left of the sequence *)
      apply red_seq_steps with (c2 := CSTAR c) in STARC.
      exact STARC.
    + (* then drop the leading SKIP *)
      apply star_one. apply red_seq_done.
Qed.


(** If the body always terminates (and is not [SKIP]), we can repeat it forever,
    hence there exists an infinite reduction sequence for [c★]. *)
Lemma diverges_cstar_via_cexec_cstar_step:
  forall c s,
    (forall st, exists st', st =[ c ]=> RNormal st') ->
    diverges s (CSTAR c).
Proof.
  intros c s BODY_TERMINATES.
  unfold diverges.
  eapply (@infseq_coinduction_principle
            (com * store)
            red
            (fun cs => exists st, cs = (CSTAR c, st))); eauto.
  intros cs (st0 & EQ). subst cs.
    destruct (BODY_TERMINATES st0) as (st1 & EXECc).
    pose proof (cexec_to_reds st0 c (RNormal st1) EXECc) as TERM.
    destruct TERM as (cs1 & STARc & FINALc).
    inversion FINALc; subst cs1.
    exists (CSTAR c, st1). split.
    + apply plus_cstar_iteration; subst; auto.
    + exists st1. reflexivity.
Qed.

(** The other direction, from a reduction sequence to a [cexec]
    derivation, is more subtle.  Here is the key lemma, showing how a
    reduction step followed by a [cexec] execution can combine into a
    [cexec] execution. *)

Lemma red_append_cexec:
  forall c1 s1 c2 s2, red (c1, s1) (c2, s2) ->
  forall s', s2 =[ c2 ]=> s' -> s1 =[ c1 ]=> s'.
Proof.
  intros until s2; intros STEP. dependent induction STEP; intros s' EXEC.
  - (* red_assign *)
    inversion EXEC; subst. apply cexec_assign.
  - (* red_nondet *)
    inversion EXEC; subst. eapply cexec_nondet.
  - (* red_assume_true *)
    inversion EXEC; subst. eapply cexec_assume; eauto.
  (* - red_assume_false *)
    (* inversion EXEC; subst. eapply cexec_assume_false; eauto. *)
  - (* red_seq_done  *)
    destruct s' as [st'|].
    + apply cexec_seq with s2. apply cexec_skip. exact EXEC.
    + apply cexec_seq_error_right with s2. apply cexec_skip. exact EXEC.
  - (* red_seq_error *)
    inversion EXEC; subst.
    eapply cexec_seq_error. apply cexec_error.
  - (* red_seq_step *)
    inversion EXEC; subst.
    + (* normal *)
      eapply cexec_seq.
      * eapply IHSTEP; eauto.
      * exact H4.
    + (* error left *)
      eapply cexec_seq_error.
      eapply IHSTEP; eauto.
    + (* error right *)
      eapply cexec_seq_error_right.
      * eapply IHSTEP; eauto.
      * exact H4.
  - (* red_choice_left *)
    apply cexec_choice_left. exact EXEC.
  - (* red_choice_right *)
    apply cexec_choice_right. exact EXEC.
  - (* red_cstar_done *)
    inversion EXEC; subst. apply cexec_cstar_done.
  - (* red_cstar_step *)
    inversion EXEC; subst.
    + (* normal *)
      eapply cexec_cstar_step_ok; eauto.
    + (* error left *)
      eapply cexec_cstar_step_error; eauto.
    + (* error right *)
      eapply cexec_cstar_step_ok; eauto.
Qed.

(** By induction on the reduction sequence, it follows that a command
    that terminates according to the small-step semantics executes according
    to the natural semantics, with the same [result]. *)
Theorem reds_to_cexec:
  forall s c r,
  terminates_result s c r -> s =[ c ]=> r.
Proof.
  intros s c r (cs & STAR & FINAL).
  dependent induction STAR.
  - inversion FINAL; subst; constructor.
  - destruct b as [c2 s2].
    eapply red_append_cexec; eauto.
Qed.

Corollary reds_to_cexec_normal:
  forall s c s',
    star red (c, s) (SKIP, s') -> s =[ c ]=> RNormal s'.
Proof.
  intros s c s' STAR.
  apply reds_to_cexec.
  exists (SKIP, s'). split; [exact STAR | constructor].
Qed.

Corollary reds_to_cexec_error:
  forall s c s',
    star red (c, s) (ERROR, s') -> s =[ c ]=> RError.
Proof.
  intros s c s' STAR.
  apply reds_to_cexec.
  exists (ERROR, s'). split; [exact STAR | constructor].
Qed.