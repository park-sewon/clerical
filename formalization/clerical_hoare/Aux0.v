Require Import ZArith.
Require Import List.

(* Clerical independent auxillary definitions *)

Inductive three := one | two | third.

(* There should be built-in functions for these... *)
Definition eq_Set {A B : Set} (p : A = B) (a : A) : B.
Proof.
  rewrite<- p;  exact a.
Qed.
Definition eq_Type {A B : Type} (p : A = B) (a : A) : B.
Proof.
  rewrite<- p;  exact a.
Qed.

Lemma split_pair : forall {A B : Type} {a c : A} {b d : B}, (a,b) = (c,d) -> a = c /\ b = d.
Proof.
  intros.
  trivial.
  inversion H.
  constructor; trivial; trivial.
Qed.

Lemma make_pair : forall A B {a c : A} {b d : B}, a = c -> b = d -> (a,b) = (c,d).
Proof.
  intros.
  rewrite H; rewrite H0; trivial.
Qed.

Definition head {A : Type} (a : list A) : option A :=
  match a with
  | a :: A => Some a
  | _ => None
  end.
Definition tail {A : Type} (a : list A) : list A :=
  match a with
  | a :: A => A
  | _ => nil
  end.

Lemma list_eq_destruct : forall {A : Type} {a b : A} {c d : list A},
    a :: c = b :: d -> a = b /\ c = d.
Proof.
  intros.
  assert (head (a::c) = head (b::d)).
  rewrite H.
  trivial.
  simpl in H0.
  inversion H0.
  constructor; trivial.
  destruct H0.
  assert (tail (a::c) = tail (b::d)).
  rewrite H; trivial.
  simpl in H0.
  trivial.
Qed.


Require Import Coq.Reals.Reals.
Require Import ZArith.
Require Import Coq.ZArith.Zorder.
Require Import Coq.PArith.Pnat.
Require Import Coq.NArith.Nnat.
Open Scope R_scope.


Fixpoint prec_embedding_nat (n:nat) : R :=
    match n with
    | O => 1
    | S n => 2 * prec_embedding_nat n
    end.

Definition prec_embedding (z:Z) : R :=
  match z with
  | 0%Z => 1
  | Zpos n => prec_embedding_nat (Pos.to_nat n)
  | Zneg n => 1 */ (prec_embedding_nat (Pos.to_nat n))
  end.

