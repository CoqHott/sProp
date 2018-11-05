(* -*- mode: coq; coq-prog-args: ("-allow-sprop") -*- *)
Require Import Relations.

Set Primitive Projections.
Record sigmaP {A : SProp} {B : A -> SProp} : SProp := sigmaPI { prP1 : A; prP2 : B prP1 }.

Arguments sigmaP A B : clear implicits.
Arguments sigmaPI {A} B prP1 prP2.

Notation "{ x : A & P }" := (sigmaP A (fun x => P)) : type_scope.
Notation "x .1" := (prP1 x) (at level 3).
Notation "x .2" := (prP2 x) (at level 3).
Notation " ( x ; p ) " := (sigmaPI _ x p).

Inductive sFalse : SProp := .
Inductive sTrue : SProp := I : sTrue.

From Equations Require Import Equations.

(** INTERNAL: Equations binding *)
(** This binds constants to use by Equations, only the sort, true and
    false propositions are used by the Derive Invert command. Work is in
    progress to use a general registration command as for sigma types below. *)

Equations Logic
          SProp Id Id_rect Id_rect_r Id_rect_dep_r
          sFalse sTrue I prod pair
          relation clos_trans WellFounded well_founded.

Register sigmaP as equations.sigmasP.type.
Register sigmaPI as equations.sigmasP.intro.
Register prP1 as equations.sigmasP.pr1.
Register prP2 as equations.sigmasP.pr2.
(** END INTERNAL: Equations binding *)

(** The standard library's le cannot be turned into a natural SProp *)
Fail Derive Invert for le.

(** Definable but squashed *)
Inductive le : nat -> nat -> SProp :=
| ind_le_0 n : le 0 n
| ind_le_S n m (H : le n m) : le (S n) (S m).

Fail Check (fun m n (H : le m n) => match H with ind_le_0 n => true | ind_le_S m n H => false end).

Derive Invert for le.

Check eq_refl : invert_le =
(fix le (var var0 : nat) {struct var} : SProp :=
  match var with
  | 0 => fun _ : nat => sTrue
  | S n =>
      fun var1 : nat =>
      match var1 with
      | 0 => sFalse
      | S n0 => le n n0
      end
  end var0).

Infix "<=" := invert_le.

Infix "<" := (fun n m => S n <= m).

Definition le_0 : forall n, 0 <= n := fun n => I.

Definition le_S : forall {m n}, m <= n -> S m <= S n := fun n m e => e.

(** The induction principle is not generated automatically yet. *)
Definition le_rect
           (P : forall m n , m <= n -> Type)
           (X0 : forall n : nat, P 0 n (le_0 n))
           (XS : forall (m n : nat) (e:m <= n), P m n e -> P (S m) (S n) (le_S e))
  : forall n m (e: n <= m), P n m e :=
    fix le_rect (var var0 : nat) (var1 : var <= var0) {struct var} : P var var0 var1 :=
      match var return (forall var0 (var1 : var <= var0), P var var0 var1)  with
      | 0 => fun (var0: nat) var1 => X0 var0
      | S n0 =>
        fun var0 : nat =>
          match var0 with
          | 0 => fun var1 => match var1 with end
          | S n1 => fun var1 => XS n0 n1 var1 (le_rect n0 n1 var1)
          end
      end var0 var1.

Check (fun m n (H : invert_le m n) => le_rect (fun _ _ _ => bool) (fun n => true) (fun _ _ _ _ => false) m n H).

Definition minus_correct n m (e : n <= m) : n + (m - n) = m.
Proof.
  generalize dependent n. 
  induction m; intros. 
  - destruct n. reflexivity. destruct e.
  - destruct n. reflexivity. cbn in *. f_equal.
    apply IHm; assumption.
Defined. 
    
Inductive Divide : nat -> nat -> SProp :=
| divide_0' : forall n, Divide n 0
| divide_S' : forall n m (e: S n <= S m), Divide (S n) (m - n) -> Divide (S n) (S m).

Derive Invert for Divide.

Check eq_refl : invert_Divide =
             fix invert_Divide var var0 {struct var0} : SProp :=
  match var0 with
  | 0 => sTrue
  | S n =>
      match var with
      | 0 => fun _ : nat => sFalse
      | S n0 =>
          fun n1 : nat => {_ : S n0 <= S n1 & invert_Divide (S n0) (n1 - n0)}
      end n
  end.

Infix "|" := invert_Divide (at level 80). 

Definition divide_0 n : n | 0 := I. 

Definition divide_S n m (e: S n <= S m) (H: S n | S m - S n) : S n | S m
  := (e;H). 

Fixpoint divide_rect (P : forall n m, n | m -> Type)
       (H0 : forall n : nat, P n 0 (divide_0 n))
       (HS : forall (n m : nat) (e : S n <= S m) (d : S n | m - n),
        P (S n) (m - n) d -> P (S n) (S m) (divide_S n m e d))
       (n n0 : nat) (H : n | n0) {struct n0} : P n n0 H.
Proof.
  destruct n0.
  - exact (H0 n).
  - destruct n. destruct H. 
    exact (HS n n0 H.1 H.2 (divide_rect P H0 HS (S n) (n0 - n) H.2)).
Defined. 

Goal 5 | 145.
  cbn. repeat econstructor. 
Defined.

Goal (5 | 146) -> sFalse.
  cbn. firstorder.
Defined. 


(* Although we have definitional proof irrelevance for n | m, we can still extract the natural number 
that witnesses the fact that n is a divisor of m out of the proof that n | m *)

Definition divide_to_nat {n m} : n | m -> nat :=
  divide_rect (fun _ _ (_:_ | _) => nat) (fun _ => 0) (fun _ _ _ _ k => S k) n m.

Lemma divide_to_nat_correct n m (e:n | m): divide_to_nat e * n = m.
Proof.
  refine (divide_rect (fun n m e => divide_to_nat e * n = m) _ _ n m e).
  - intro n0. cbn. reflexivity.
  - intros. cbn in *. f_equal. rewrite <- (minus_correct n0 m0 e0).
    f_equal. exact H.
Defined.
  
Inductive is_gcd (a b g:nat) : SProp :=
 is_gcd_intro :
  (g | a) -> (g | b) -> (forall x, (x | a) -> (x | b) -> (x | g)) ->
  is_gcd a b g.

Definition rel_prime (a b:nat) : SProp := is_gcd a b 1.

(* This definition gives us definitional proof irrelevance for prime, without paying the price of the definition of a decision procedure into booleans 
(for instance using the sieve of Eratosthenes) and a proof that it corresponds to primality *)

Inductive prime (p:nat) : SProp :=
  prime_intro :
    1 < p -> (forall n, (1 <= n) -> (n < p) -> rel_prime n p) -> prime p.

Goal prime 13.
  cbn. econstructor. exact I. intro n. 
  destruct n. inversion 1. intros _ e. cbn in e.
  repeat (try solve [firstorder];
      destruct n; [ cbn;  repeat econstructor; repeat (destruct x; firstorder) |]).
  firstorder.
Defined. 


