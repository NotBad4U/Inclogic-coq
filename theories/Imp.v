From Coq Require Import Strings.String Bool.
Require Import StateMap.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ident := string.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : ident)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNot (b : bexp)
  | BLessEqual (a1 a2 : aexp)
  | BAnd (a1 a2 : bexp)
.

Inductive com : Type :=
  | Skip
  | Asign: string -> aexp -> com
  | Seq : com -> com -> com
  | Assume : bexp -> com
  | Error: com
  | Star: com -> com                   (* Kleene iteration *)
  | Choice: com -> com -> com          (* Kleene algebra union *)
  | CLocal: string -> com -> com
  | Nondet: string -> com.             (* Nondet Assignment *)

Coercion AId : ident >-> aexp.

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
Notation "x + y" := (APlus x y) (in custom com at level 70, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 70, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 50, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Notation "a //\\ b" := (BAnd a b) (in custom com at level 60, right associativity).
Notation "a <= b" := (BLessEqual a b) (in custom com at level 60).
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
  | <{a1 - a2}> => match (aeval st a1), (aeval st a2) with
      | Some va1, Some va2 => Some (va1 - va2)
      | _, _ => None
      end
  | <{a1 * a2}> => match (aeval st a1), (aeval st a2) with
      | Some va1, Some va2 => Some (va1 * va2)
      | _, _ => None
      end
  end.


Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)
  where "e '==>' n" := (aevalR e n) : type_scope.

Definition NOTEQUAL (a1 a2: aexp) : bexp := <{~ (a1 = a2)}>.

Definition GREATEREQUAL (a1 a2: aexp) : bexp := <{ a2 <= a1 }>.

Definition GREATER (a1 a2: aexp) : bexp := <{~ (a1 <= a2)}>.

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := <{~ ((~ b1) //\\ (~ b2))}>.

Notation "a \\// b" := (OR a b) (in custom com at level 80, right associativity).


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
  | BLessEqual a1 a2 => equal_option (Nat.leb) (aeval st a1) (aeval st a2)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  | BNot b1 => negb (beval st b1)
  end.

Lemma beval_OR:
  forall st b1 b2, beval st <{b1 \\// b2}> = beval st b1 || beval st b2.
Proof.
  intros. cbn.
  rewrite negb_andb.
  do 2 rewrite negb_involutive.
  reflexivity.
Qed.

(*
  The value of an expression depends only on the values of its free variables.

  Free variables are defined by this recursive predicate:
*)
Fixpoint free_in_aexp (x: ident) (a: aexp) : Prop :=
  match a with
  | ANum n => False
  | AId y => y = x
  | APlus a1 a2 | AMinus a1 a2 | AMult a1 a2 => free_in_aexp x a1 \/ free_in_aexp x a2
  end.

Theorem aeval_free:
  forall s1 s2 a,
  (forall x, free_in_aexp x a -> get s1 x = get s2 x) ->
  aeval s1 a  = aeval s2 a .
Proof.
  induction a; cbn; intros Hfree; auto.
  all: (rewrite IHa1, IHa2; auto).
Qed.


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
Notation "'nondet' l " :=
        (Assume l)
          (in custom com at level 8, l custom com at level 0) : com_scope.
Notation "'error()'" :=
          Error (in custom com at level 0) : com_scope.
Notation "c '⋆'" :=
        (Star c) (in custom com at level 8) : com_scope.
Notation "x '⨁' y " :=
        (Choice x y) (in custom com at level 8) : com_scope.

(* Notations for while, if and assert keywords *)

Definition While b c := <{ (assume b ; c) ⋆ ; assume ~ b }>.

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

Fixpoint Cpow (C: com) (n: nat): com := 
match n with
| 0 => <{skip}>
| S m => <{ C ; Cpow C m }>
end.

Infix "^" := Cpow (in custom com at level 10).

(* Notation "c '^' n" :=
  (Cpow c n) (in custom com at level 8) : com_scope. *)

Reserved Notation
         "st '=[' c ']=>' ϵ ':' st'"
         (at level 40, c custom com at level 99,
          st constr, ϵ constr at next level).

Inductive Signal: Type := 
| ok
| err.

Inductive ceval : com -> state -> Signal -> state -> Prop :=
| E_Skip : forall st eps,
  st =[ skip ]=> eps : st
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
| E_StarSkip : forall c st ϵ,
  st =[ skip ]=> ϵ : st -> 
  st =[ c ⋆ ]=> ϵ : st
| E_StarIter : forall c st st' ϵ,
  (* st =[ c ⋆ ; c  ]=> ϵ : st' -> *)
  st =[ c ⋆ ]=> ϵ : st ->
  st =[ c ]=> ϵ : st' -> 
  st =[ c ⋆ ]=> ϵ : st'
| E_ChoiceLeft: forall x y st st' ϵ,
  st =[ x ]=> ϵ : st' ->
  st =[ x ⨁ y ]=> ϵ : st'
| E_ChoiceRight: forall x y st st' ϵ,
  st =[ y ]=> ϵ : st' ->
  st =[ x ⨁ y ]=> ϵ : st'
(* | E_Nondet: forall x st n,
  st =[ skip ]=> ok : (x !-> n ; st) *)
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


Hint Unfold assert_implies : core.


(* substAexp x y a, which replaces all occurrences of a variable x with a value y inside an arithmetic expression a. *)
Fixpoint substAexp (x: string) (y: aexp) (a: aexp) : aexp :=
match a with
  | ANum n => ANum n
  | AId var => if String.eqb x var then y else (AId var)
  | <{a1 + a2}> => <{(substAexp x y a1) + (substAexp x y a2)}>
  | <{a1 - a2}> => <{(substAexp x y a1) - (substAexp x y a2)}>
  | <{a1 * a2}> => <{(substAexp x y a1) * (substAexp x y a2)}>
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
| <{ a1 <= a2 }> => <{ auxa a1 <= auxa a2 }>
| <{ b1 //\\ b2 }> => <{(aux b1) //\\ (aux b2)}>
end.

(* subst x y c, which replaces all occurrences of a variable x with a value y inside a command c. *)
Fixpoint substCmd (x: string) (y: aexp) (c: com) : com :=
let aux t := substCmd x y t in
match y with 
| AId yvar => 
  let if_y_eq z t1 t2 := if String.eqb x z then t1 (* update *) else t2 (* skip *) in
  match c with
  | Skip => Skip
  | Asign x' v =>  if_y_eq x' (Asign yvar (substAexp x y v)) (Asign x' (substAexp x y v)) 
  | Seq c1 c2 => Seq (aux c1) (aux c2) 
  | Assume b => Assume b
  | Error => Error
  | Star c => Star (aux c)
  | Choice c1 c2 => Choice (aux c1) (aux c2)
  | CLocal x' c' => if_y_eq x' (CLocal yvar (aux c')) (CLocal x' (aux c'))
  | Nondet x' => if_y_eq x' (Nondet yvar) (Nondet x')
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
  | Nondet x' => Nondet x'
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


(* - apply (E_Seq_Norm c <{ c ⋆ }> _ _ _ _ H6 H2). *)

(* induction c; inversion H; subst.
- econstructor. apply H6. *)


Hint Unfold assert_implies : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.