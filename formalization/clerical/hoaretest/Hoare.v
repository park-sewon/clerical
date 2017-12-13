Require Import ZArith.
Require Import String.
Require Import Clerical. 
Require Import Semantics.
Require Import List.
Require Import Typing.

(* proof rules by discussion between Andrej Bauer, Sewon Park and Alex Simpson
   Implementation by discussion between Franz B., Sewon Park *)

(* for a state, it should not matter whether a context is readonly or writeable...
   better let state to be a dependent type of typed variable list..?
   however, correctness of a program differs whether we have a variable readonly or not.
   for example, Γ; Δ ⊢ {q} x := e {p} can be only proven if we have distinction of Γ and Δ.
   Hence, a state and an assertion needs to be a dependent type of list of typed variable and
   triple and correctness needs to be dependent of Γ;Δ
 *)


Inductive state (Γ : context) : Type :=
| empty_state : Γ = empty_context -> state Γ
| cons_rw : forall v Δ, state Δ -> fst Γ = cons v (fst Δ) -> snd Γ = snd Δ -> (sem_datatype (snd v)) -> state Γ
| cons_ro : forall v Δ, state Δ -> fst Γ = fst Δ -> snd Γ = cons v (snd Δ) -> (sem_datatype (snd v)) -> state Γ.



(* TODO : need to be partial for the case where variable duplicates *)
Definition context_union (Γ₁ Γ₂ : context) : context := ((fst Γ₁) ++ (fst Γ₂), (snd Γ₁) ++ (snd Γ₂)).
Lemma empty_union : forall Γ, context_union empty_context Γ = Γ.
Proof.
  intro.
  unfold context_union.
  assert (h : fst empty_context = nil).
    unfold empty_context.
    trivial.
  assert (h2 : snd empty_context = nil).
    unfold empty_context.
    trivial.
  rewrite h; rewrite h2.
  simpl.
  destruct Γ.
  trivial.
Qed.

Fixpoint state_union (Γ₁ Γ₂ : context) (γ₁ : state Γ₁) (γ₂ : state Γ₂) : state (context_union Γ₁  Γ₂).
Proof.
  induction γ₁.

  assert (h : ((context_union Γ Γ₂) = Γ₂)).
  pose proof (empty_union Γ₂).
  rewrite<- e in H.
  exact H.
  rewrite h.
  exact γ₂.

  assert (h1 : fst (context_union Γ Γ₂) = cons v (fst (context_union Δ Γ₂))).
    unfold context_union.
    simpl.
    rewrite e.
    trivial.
  assert (h2 : snd (context_union Γ Γ₂) = snd (context_union Δ Γ₂)).
    unfold context_union.
    simpl.
    rewrite e0.
    trivial.
  exact (cons_rw (context_union Γ Γ₂) v (context_union Δ Γ₂) IHγ₁ h1 h2 s).

  assert (h1 : snd (context_union Γ Γ₂) = cons v (snd (context_union Δ Γ₂))).
    unfold context_union.
    simpl.
    rewrite e0.
    trivial.
  assert (h2 : fst (context_union Γ Γ₂) = fst (context_union Δ Γ₂)).
    unfold context_union.
    simpl.
    rewrite e.
    trivial.
  exact (cons_ro (context_union Γ Γ₂) v (context_union Δ Γ₂) IHγ₁ h2 h1 s).
Qed.
  

Fixpoint is_in_typed (Γ : list typed_variable) (v : typed_variable) : bool :=
  match Γ with
  | nil => false
  | cons w Γ => if eq_name_type_v v w then true else is_in_typed Γ v
  end.
Definition is_in (Γ : context) (v : typed_variable) : bool :=
  if is_in_typed (fst Γ) v then true else if is_in_typed (snd Γ) v then true else false.
                                  
Fixpoint assigned_value (Γ : context) (γ : state Γ) (s : string) (τ : datatype) : option (sem_datatype τ).
Proof.
  induction  γ.
Admitted.
    
                 


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

Definition γ : state Δ := cons_rw Δ ν Ε ε triv2 triv3 (4%Z).
End example.



Definition assertion (Γ : context) (τ : result_type) := ((sem_result_type τ) * state Γ -> Type).

  

Definition implies (Γ : context) (τ : result_type) (p q : assertion Γ τ) : Type
  := forall γ, p γ -> q γ.

Definition implies_to_unit (Γ : context) (τ : result_type) (p : assertion Γ τ) (q : assertion Γ RCommand): Type
  := forall y γ, p (y, γ) -> q (tt, γ).


Notation "Γ , τ ⊢ p ->> q" := (implies Γ τ p q) (at level 80) : hoare_scope.
Open Scope hoare_scope.



(* hoare triple is defined for well--typed commands *)
Inductive  hoare_triple (Γ : context) (τ : result_type) (c : comp) : Type
  := totally : assertion Γ RCommand -> has_type Γ c τ -> assertion Γ τ -> hoare_triple Γ τ c.


Definition correct (Γ : context) (τ : result_type) (c : comp) (h : hoare_triple Γ τ c) := Type.


(*
—————————————————- (r.skip)
Γ;Δ ⊢ {θ} skip {θ}
*)
Axiom proof_rule_skip :
  forall Γ p, correct Γ RCommand SKIP (totally Γ RCommand SKIP p (has_type_Skip Γ) p).


(*
Γ;Δ ⊢ φ → φ' Γ;Δ ⊢ {φ'} c {y : τ | ψ'} Γ;Δ,y:τ ⊢ ψ' → ψ
——————————————————-—————————————————-—–———————————————- (r.consequence)
Γ;Δ ⊢ {φ} c {y : τ | ψ}
*)
Axiom proof_rule_consequence :
  forall Γ τ φ φ' c ψ' ψ h, correct Γ τ c (totally Γ τ c φ' h ψ') ->
                        Γ , RCommand ⊢ φ ->> φ' -> Γ , τ ⊢ ψ' ->> ψ ->
                        correct Γ τ c (totally Γ τ c φ h ψ).

(*
Γ;Δ ⊢ {φ} c₁ {ψ} Γ;Δ ⊢ {ψ} c₂ {y : τ | θ}
——————————————————-—————————————————-—–———————————————- (r.sequence)
Γ;Δ ⊢ {φ} c₁;;c₂ {y : τ | θ}
*)
Axiom proof_rule_sequence :
  forall Γ τ φ ψ θ c₁ c₂ h₁ h₂,
    correct Γ RCommand c₁ (totally Γ RCommand c₁ φ h₁ ψ) ->
    correct Γ τ c₂ (totally Γ τ c₂ ψ h₂ θ) ->
    correct Γ τ (Sequence c₁ c₂) (totally Γ τ (Sequence c₁ c₂) φ (has_type_Sequence Γ c₁ c₂ τ h₁ h₂) θ).


(*
;Γ,Δ ⊢ {φ} e {y : τ | ψ}
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {φ ∧ ∀ y : τ. (ψ -> θ[y/x]} x:= e {θ}
*)


(*
;Γ,Δ ⊢ {φ} e {x : σ | ψ}  x:σ,Γ; Δ ⊢ {ψ} c {y : τ | θ} x ∉ Γ;Δ
——————————————————-—————————————————-—–———————————————- (r.newvar)
Γ;Δ ⊢ {φ} newvar x := e in c {y : τ | ∃ x : γ. θ}
*)
Axiom proof_rule_newvar :
  forall Γ σ σ' φ ψ θ τ e c h₁ h₂ s (g : in_context Γ s -> False),
    correct (readonly Γ) σ e (totally (readonly Γ) σ e φ h₁ ψ) ->
    σ = RData σ' ->
    correct (add_rw Γ s σ') τ c (totally  (add_rw Γ s σ') τ c ψ h₂ θ) ->
    correct Γ τ c (totally Γ τ (Newvar s e c) φ
                           (has_type_newvar Γ s τ σ e c g h₁ h₂)
                           (fun δ => exists x, θ (state_union x δ))). 
                           


(*
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {θ(x)} x {y : τ | θ(y)}
*)


