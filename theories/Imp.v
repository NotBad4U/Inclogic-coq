Require Export Coq.Strings.String.
Require Import StateMap.

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
  | Choice: com -> com -> com
  | CLocal: string -> com -> com.

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
Notation "'local' x . C" :=
        (CLocal x C)
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
| E_SkipF :
  empty =[ skip ]=> err : empty
| E_Local : forall st st' x v c ϵ,
  (x !-> v ; st) =[ local x . c ]=> ϵ : (x !-> v ; st')
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
| E_ErrorOk:
  empty =[ error() ]=> ok: empty
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

