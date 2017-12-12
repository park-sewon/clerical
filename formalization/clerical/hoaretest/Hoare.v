Require Import ZArith.
Require Import String.
Require Import Clerical. 
Require Import Semantics.
Require Import List.
Require Import Typing.


(* define state as a dependent type; it only makes sense to define a state when a 
   context is given! *)

Definition map (v : typed_variable) := sem_datatype (snd v).

Inductive state (Γ : context) : Type :=
| empty_state : Γ = empty_context -> state Γ
| cons_rw : forall v Δ, state Δ -> fst Γ = cons v (fst Δ) -> snd Γ = snd Δ -> map v -> state Γ
| cons_ro : forall v Δ, state Δ -> fst Γ = fst Δ -> snd Γ = cons v (snd Δ) -> map v -> state Γ.



Module example.
Definition Ε : context := (nil, nil).
Definition triv : Ε  = (nil, nil).
Proof. trivial. Qed.

Definition ε : state Ε := empty_state Ε triv.

Definition ν : typed_variable := (Id "x", DInteger).
Definition Δ : context := (ν :: nil, nil).
Lemma triv2 : fst Δ = ν :: (fst Ε).
Proof. trivial. Qed.
Lemma triv3 : snd Δ = snd Ε.
Proof. trivial. Qed.

Definition σ : state Δ := cons_rw Δ ν Ε ε triv2 triv3 (4%Z).
End example.




(* assertion also needs to become a dependent type of context *)

Definition assertion (Γ : context)  := state Γ -> Type.
Definition implies (Γ : context) (p q : assertion Γ) : Type := forall σ, p σ -> q σ.
Notation "Γ ⊢ p ->> q" := (implies Γ p q) (at level 80) : hoare_scope.
Open Scope hoare_scope.



(* hoare triple is defined for well--typed commands *)
Inductive  hoare_triple (Γ : context) : Type :=
| no_return : assertion Γ -> comp ->  assertion Γ -> hoare_triple Γ.


Definition correct (Γ : context) (h : hoare_triple Γ) := Type.

Axiom proof_rule_skip :
  forall Γ p, correct Γ (no_return Γ p SKIP p).

Axiom proof_rule_sequence :
  forall Γ p₁ p₂ q₁ q₂ c₁ c₂, correct Γ (no_return Γ p₁ c₁ q₁) ->
                              correct Γ (no_return Γ p₂ c₂ q₂) ->
                              Γ ⊢ q₁ ->> p₂ ->
                              correct Γ (no_return Γ p₁ (Sequence c₁ c₂) q₂).

Axiom proof_rule_consequence :
  forall Γ p' p c q q', correct Γ (no_return Γ p c q) ->
                        Γ ⊢ p' ->> p -> Γ ⊢ q ->> q' ->
                        correct Γ (no_return Γ p' c q').


