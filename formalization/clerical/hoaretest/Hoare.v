Require Import ZArith.
Require Import String.
Require Import Clerical. 
Require Import Semantics.
Require Import List.
Require Import Typing.
Require Import Bool.
Require Import Hoare_aux.
(* proof rules by discussion between Andrej Bauer, Sewon Park and Alex Simpson
   Implementation detail discussed between Franz B. and Sewon Park *)

Definition add_rw_ctx (Γ : context) (v : typed_variable) : context := (v :: fst Γ, snd Γ).
Definition add_ro_ctx (Γ : context) (v : typed_variable) : context := (fst Γ, v :: snd Γ).


(* State inductively defined via a context.
   val is a function that returns value of v within Γ *)
Inductive state (Γ : context) : Type :=
| emty_state : Γ = empty_context -> state Γ
| cons_rw : forall v Δ, state Δ -> add_rw_ctx Δ v = Γ -> (sem_datatype (snd v)) -> state Γ
| cons_ro : forall v Δ, state Δ -> add_ro_ctx Δ v = Γ -> (sem_datatype (snd v)) -> state Γ.

Fixpoint val {Γ : context} (γ : state Γ) (v : typed_variable) : option (sem_datatype (snd v)).
Proof.
  pose proof (typed_mem_dec Γ v).
  destruct H.
  destruct γ.  
  exact None.
  pose proof (variable_name_type_dec v0 v).
  destruct H.
  pose proof (eq_variable_has_same_type v0 v e1).
  rewrite<- H.
  exact (Some s).
  exact (val Δ γ v).
  pose proof (variable_name_type_dec v0 v).
  destruct H.
  pose proof (eq_variable_has_same_type v0 v e1).
  rewrite<- H.
  exact (Some s).
  exact (val Δ γ v).
  exact None.
Qed.


(* Assertion is a function from state to prop.
   Γ ⊢ p ::= {x : τ | φ} means
*)
Definition assertion (Γ : context) (τ : result_type) := (sem_result_type τ) -> state  Γ -> Prop. 





(* when ψ is an assertion with return type τ, make it to an assertion with return type unit
   where the return value encoded in context *)
Definition merge_ro (Γ : context) (τ : result_type) (s : string) (ψ : assertion Γ τ) :
  assertion (add_ro_ctx Γ (Id s, origin_type τ)) RCommand.
Proof.
  Admitted.

Definition merge_rw (Γ : context) (τ : result_type) (s : string) (ψ : assertion Γ τ) :
  assertion (add_rw_ctx Γ (Id s, origin_type τ)) RCommand.
Proof.
  Admitted.

Definition collapse (Γ : context) (τ : result_type) (ψ : assertion Γ τ) :
  assertion (readonly Γ) τ.
Proof.
  Admitted.

Definition collapse_rev {Γ : context} {τ : result_type} (ψ : assertion (readonly Γ) τ) :
  assertion Γ τ.
Proof.
  Admitted.

(* return φ[y/x] which is τ -> Γ -> prop *)
Definition rewrite_void {Γ : context} (φ : assertion Γ RCommand) (v : typed_variable) : assertion Γ (RData (snd v)).
Proof.
  Admitted.


Lemma t₁ : forall s τ, sem_result_type τ = sem_result_type (RData (snd (Id s, origin_type τ))).
Proof.
  intros.
  assert (τ = RData (snd (Id s, origin_type τ))). 
  simpl.
  unfold origin_type.
  destruct τ.
  trivial.
  rewrite<- H.
  trivial.
Qed.

Definition rewrite_aux (τ : result_type) (s : string) :   sem_result_type τ -> sem_result_type (RData (snd (Id s, origin_type τ))).
Proof.
  pose proof t₁ s τ.
  rewrite H.
  intro.
  exact H0.
Qed.
  

    
Definition implies {Γ : context} {τ : result_type} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ -> q x γ.

Definition implies_2 {Γ : context} {τ : result_type} (p q : assertion Γ τ) : assertion Γ τ
  := fun y γ => p y γ -> q y γ.

Definition conjs {Γ : context} {τ : result_type} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ /\ q x γ.

Definition conjs_2 {Γ : context} {τ : result_type} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ /\ q x γ.

(* hoare triple is defined for well--typed commands *)
Inductive  triple (Γ : context) (c : comp) (τ : result_type) : Type
  := totally : assertion Γ RCommand -> assertion Γ τ -> triple Γ c τ.

Definition correct  {Γ : context} {c : comp} {τ : result_type} (h : triple Γ c τ) := Type.


Notation "p ->> q" := (implies  p q) (at level 80) : hoare_scope.
Notation "p //\ q" := (conjs  p q) (at level 80) : hoare_scope.

Notation "p → q" := (implies_2  p q) (at level 80) : hoare_scope.
Notation "p ∧ q" := (conjs_2  p q) (at level 80) : hoare_scope.



Open Scope hoare_scope.

(* Hoare–style proof rules *)
(* 1. Skip
   2. Conseq
   3. Sequence
   4. Newvar
   5. Assignment
*)


(*
—————————————————- (r.skip)
Γ;Δ ⊢ {θ} skip {θ}
*)
Axiom proof_rule_skip :
  forall Γ p, correct (totally Γ SKIP RCommand p p).

(*
Γ;Δ ⊢ φ → φ' Γ;Δ ⊢ {φ'} c {y : τ | ψ'} Γ;Δ,y:τ ⊢ ψ' → ψ
——————————————————-—————————————————-—–———————————————- (r.consequence)
Γ;Δ ⊢ {φ} c {y : τ | ψ}
*)
Axiom proof_rule_consequence :
  forall Γ τ φ φ' c ψ' ψ,
    has_type Γ c τ ->
    correct (totally Γ c τ φ' ψ') ->
    φ ->> φ' -> ψ' ->> ψ ->
    correct (totally Γ c τ φ ψ).

(*
Γ;Δ ⊢ {φ} c₁ {ψ} Γ;Δ ⊢ {ψ} c₂ {y : τ | θ}
——————————————————-—————————————————-—–———————————————- (r.sequence)
Γ;Δ ⊢ {φ} c₁;;c₂ {y : τ | θ}
*)
Axiom proof_rule_sequence :
  forall Γ τ φ ψ θ c₁ c₂,
    has_type Γ c₁ RCommand -> has_type Γ c₂ τ ->
    correct (totally Γ c₁ RCommand φ ψ) ->
    correct (totally Γ c₂ τ ψ θ) ->
    correct (totally Γ (c₁ ;; c₂) τ φ θ).

(*
;Γ,Δ ⊢ {φ} e {x : σ | ψ}  x:σ,Γ; Δ ⊢ {ψ} c {y : τ | θ} x ∉ Γ;Δ
——————————————————-—————————————————-—–———————————————- (r.newvar)
Γ;Δ ⊢ {φ} newvar x := e in c {y : τ | ∃ x : γ. θ}
 *)
Axiom proof_rule_newvar :
  forall Γ σ φ ψ τ e c s θ,
    not_in_context_t Γ (Id s, origin_type σ) ->
    correct (totally (readonly Γ) e σ φ ψ) ->
    correct (totally (add_rw_ctx Γ (Id s, origin_type σ)) c τ (merge_rw Γ σ s (collapse_rev ψ)) θ) ->
    correct (totally Γ (Newvar s e c) τ (collapse_rev φ)
                     (fun y δ => exists x,
                         let v := (Id s, origin_type σ) in
                         let γ' := cons_rw (add_rw_ctx Γ v) v Γ δ eq_refl x in (θ y γ'))
            ).

  
(*
;Γ,Δ ⊢ {φ} e {y : τ | ψ}
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {φ ∧ ∀ y : τ. (ψ -> θ[y/x]} x:= e {θ}
*)
Axiom proof_rule_assignment :
  forall Γ s e τ φ ψ θ,
    correct (totally (readonly Γ) e τ φ ψ) ->
    correct (totally Γ (SET s := e) RCommand
                     ((collapse_rev φ) ∧
                      (fun _ δ => forall y,
                       (collapse_rev ψ) y δ -> rewrite_void θ (Id s, origin_type τ) (rewrite_aux τ s y) δ    
                      )) θ 

            ).


(*
x ∈ Γ 
——————————————————-—————————————————-—–———————————————- (r.variable)
Γ;Δ ⊢ {θ} x {y : τ | θ(y)}
*)


(*
;Γ,Δ ⊢ {φ} e₁ {y : τ₁ | ψ₁} ... ;Γ,Δ ⊢ {φ} eᵢ {y : τᵢ | ψᵢ} 
—————————————————————————————————————————————-—————————————————-—–———————————————- (r.operator)
Γ;Δ ⊢ {θ} op(e₁, ..., eᵢ) {y : τ |∃ y₁,...,yᵢ, y = [[op]](y₁, ..., yᵢ) ∧ ψ₁∧...∧ψᵢ}
*)

(*







(* PREV WORKS:

    correct Δ e σ (totally Δ e σ φ ψ) ->
    correct ((Id s, (origin_type σ)) :: Δ) c τ (totally ((Id s, (origin_type σ)) :: Δ) c τ (merge (Δ) σ s ψ) θ) ->
    correct Δ (Newvar s e c)  τ (totally Δ (Newvar s e c) τ φ
                                         (fun y δ => exists x,
                                              let γ' := cons_state  ((Id s, origin_type σ) :: Δ) (Id s, origin_type σ) Δ δ eq_refl x  in  (θ y γ'))).






(*
;Γ,Δ ⊢ {φ} e {y : τ | ψ}
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {φ ∧ ∀ y : τ. (ψ -> θ[y/x]} x:= e {θ}
*)

Lemma trans_lst : forall Γ, m_context Γ = m_context (readonly Γ).
Proof.
Admitted.

(*
;Γ,Δ ⊢ {φ} e {x : σ | ψ}  x:σ,Γ; Δ ⊢ {ψ} c {y : τ | θ} x ∉ Γ;Δ
——————————————————-—————————————————-—–———————————————- (r.newvar)
Γ;Δ ⊢ {φ} newvar x := e in c {y : τ | ∃ x : γ. θ}
 *)
Check eq_rect.
Definition ttt (x : nat) := x + 4.
Axiom wtf : Z = nat.
Check eq_refl.
Check eq_sym.


Axiom proof_rule_newvar :
  forall Γ σ σ' φ ψ θ τ e c h₁ h₂ s (g : in_context Γ s -> False),
    correct (readonly Γ) e σ (totally (readonly Γ) e σ φ h₁ ψ) ->
    σ = RData σ' ->
    correct (add_rw Γ s σ') c τ (totally  (add_rw Γ s σ') c τ (merge (m_context Γ) σ s ψ) h₂ θ) ->
    correct Γ c τ (totally Γ (Newvar s e c) τ φ
                           (has_type_newvar Γ s τ σ e c g h₁ h₂)
                           (fun δ => exists x, θ (state_union x δ))). 
                           


(*
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {θ(x)} x {y : τ | θ(y)}
*)






(* state as dependent type of typed_variable list *)
Definition l_context := list typed_variable.


(* state is a somewhat like a list constructed resprect to a list of typed variables:
   - empty_state constructs an empty state given a proof that given Γ is empty
   - con_state constructs a σ : state (v :: Δ) when σ' : state Δ and σᵥ : v ↦ s ∈ sem_datatype v is given *) 
Inductive state (Γ : l_context) : Type :=
| empty_state : Γ = nil -> state Γ
| cons_state : forall v Δ, state Δ -> cons v Δ = Γ -> (sem_datatype (snd v)) -> state Γ.

(* TODO : need to be partial for the case where variable duplicates *)
Definition context_union (Γ₁ Γ₂ : context) : context := ((fst Γ₁) ++ (fst Γ₂), (snd Γ₁) ++ (snd Γ₂)).

Lemma empty_union : forall Γ, context_union empty_context Γ = Γ.
Proof.
  intro.
  unfold context_union.
  assert (h : fst empty_context = nil).
  unfold empty_context; trivial.
  assert (h2 : snd empty_context = nil).
  unfold empty_context; trivial.
  rewrite h; rewrite h2.
  simpl;  destruct Γ.
  trivial.
Qed.

Fixpoint state_union (Γ₁ Γ₂ : list typed_variable) (γ₁ : state Γ₁) (γ₂ : state Γ₂) : state (Γ₁ ++ Γ₂).
Proof.
  induction γ₁.
  assert (h : ((Γ ++ Γ₂) = Γ₂)).
  rewrite e; trivial.
  rewrite h.
  exact γ₂.
  assert (h1 : cons v (Δ ++ Γ₂) = (Γ ++ Γ₂)).
  rewrite <-e; trivial.
  exact (cons_state (Γ ++ Γ₂) v (Δ ++ Γ₂) IHγ₁ h1 s).
Qed.

Fixpoint is_in_typed (Γ : list typed_variable) (v : typed_variable) : bool :=
  match Γ with
  | nil => false
  | cons w Γ => if eq_name_type_v v w then true else is_in_typed Γ v
  end.

Lemma variable_name_type_dec : forall v w, {eq_name_type_v v w = false} + {eq_name_type_v v w = true}.
Proof.
  intros.
  pose proof (bool_dec (eq_name_type_v v w) true).
  destruct H.
  trivial.
  right; exact e.
  pose proof (not_true_is_false (eq_name_type_v v w) n).
  left; exact H.
Qed.

Lemma eq_variable_has_same_type : forall v w, eq_name_type_v v w = true -> snd v = snd w.
Proof.
  intros.
  unfold eq_name_type_v in H.
  destruct (eq_name_v v w).
  unfold eq_type in H.
  induction (snd v).
  induction (snd w).
  trivial.
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  induction (snd w).
  contradict H.
  exact diff_false_true.
  trivial.
  contradict H.
  exact diff_false_true.
  induction (snd w).
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  trivial.
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  destruct (snd w).
  contradict H.
  exact diff_false_true.
  trivial.
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  destruct (snd w).
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  trivial.
  contradict H.
  exact diff_false_true.
  destruct (snd w).
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  contradict H.
  exact diff_false_true.
  trivial.
  contradict H.
  exact diff_false_true.
Qed.

Lemma typed_membership_dec : forall Γ v, {is_in_typed Γ v = false} + {is_in_typed Γ v = true}.
Proof.
  intros.
  trivial.
  pose proof (bool_dec (is_in_typed Γ v) true).
  destruct H.
  trivial.
  right; exact e.
  pose proof (not_true_is_false (is_in_typed Γ v) n).
  left; exact H.
Qed.

Fixpoint val (Γ : l_context) (γ : state Γ) (v : typed_variable) : option (sem_datatype (snd v)).
Proof.
  pose proof (typed_membership_dec Γ v).
  destruct H.
  exact None.
  destruct γ.
  exact None.
  pose proof (variable_name_type_dec v0 v).
  destruct H.
  exact (val Δ γ v).
  pose proof (eq_variable_has_same_type v0 v e1).
  rewrite<- H.
  exact (Some s).
Qed.

Definition assertion (Γ : list typed_variable) (τ : result_type) := (sem_result_type τ) -> state  Γ -> Prop. 

Definition origin_type (τ : result_type) : datatype := match τ with RData τ => τ end.

(* Γ ⊢ {x : τ | ψ} ≡ x:τ,Γ ⊢ {ψ} *)
Definition merge (Γ : list typed_variable) (τ : result_type) (s : string) (ψ : assertion Γ τ) :
  assertion ((Id s, origin_type τ) :: Γ) RCommand.
Proof.
  Admitted.
  
  
  
Definition implies (Γ : list typed_variable) (τ : result_type) (p q : assertion Γ τ) : Type
  := forall x γ, p x γ -> q x γ.
Definition implies_to_unit (Γ : list typed_variable) (τ : result_type) (p : assertion Γ τ) (q : assertion Γ RCommand): Type
  := forall y γ, p y γ -> q tt γ.




(* hoare triple is defined for well--typed commands *)
Inductive  hoare_triple (Δ : l_context) (c : comp) (τ : result_type) : Type
  := totally : assertion (Δ) RCommand ->
               assertion (Δ) τ ->
               hoare_triple Δ c τ.

Definition correct  (Δ : l_context) (c : comp) (τ : result_type) (h : hoare_triple Δ c τ) :=
  match h with
  | totally _ c _ φ
                                                                                             




(*
;Γ,Δ ⊢ {φ} e {x : σ | ψ}  x:σ,Γ; Δ ⊢ {ψ} c {y : τ | θ} x ∉ Γ;Δ
——————————————————-—————————————————-—–———————————————- (r.newvar)
Γ;Δ ⊢ {φ} newvar x := e in c {y : τ | ∃ x : γ. θ}
 *)

Axiom proof_rule_newvar :
  forall Δ σ φ ψ τ e c s θ,
    correct Δ e σ (totally Δ e σ φ ψ) ->
    correct ((Id s, (origin_type σ)) :: Δ) c τ (totally ((Id s, (origin_type σ)) :: Δ) c τ (merge (Δ) σ s ψ) θ) ->
    correct Δ (Newvar s e c)  τ (totally Δ (Newvar s e c) τ φ
                                         (fun y δ => exists x,
                                              let γ' := cons_state  ((Id s, origin_type σ) :: Δ) (Id s, origin_type σ) Δ δ eq_refl x  in  (θ y γ'))).


Module example_of_assertions.

  Definition Γ : l_context := (Id "x", DInteger) :: (Id "y", DInteger) :: (Id "z", DInteger) :: (Id "q", DInteger) :: nil.
  Definition φ : assertion Γ RCommand := fun y σ =>
                                           (match val Γ σ (Id "x", DInteger) with
                                            | None => False
                                            | Some x => (x > 4)%Z
                                            end).
End example_of_assertions.
  

Notation "Γ , τ ⊢ p ->> q" := (implies (m_context Γ) τ p q) (at level 80) : hoare_scope.
Open Scope hoare_scope.




(* Hoare–style proof rules *)
(*
—————————————————- (r.skip)
Γ;Δ ⊢ {θ} skip {θ}
*)
Axiom proof_rule_skip :
  forall Γ p, correct Γ SKIP RCommand (totally Γ SKIP RCommand p (has_type_Skip Γ) p).


(*
Γ;Δ ⊢ φ → φ' Γ;Δ ⊢ {φ'} c {y : τ | ψ'} Γ;Δ,y:τ ⊢ ψ' → ψ
——————————————————-—————————————————-—–———————————————- (r.consequence)
Γ;Δ ⊢ {φ} c {y : τ | ψ}
*)
Axiom proof_rule_consequence :
  forall Γ τ φ φ' c ψ' ψ h, correct Γ c τ (totally Γ c τ φ' h ψ') ->
                        Γ , RCommand ⊢ φ ->> φ' -> Γ , τ ⊢ ψ' ->> ψ ->
                        correct Γ c τ (totally Γ c τ φ h ψ).

(*
Γ;Δ ⊢ {φ} c₁ {ψ} Γ;Δ ⊢ {ψ} c₂ {y : τ | θ}
——————————————————-—————————————————-—–———————————————- (r.sequence)
Γ;Δ ⊢ {φ} c₁;;c₂ {y : τ | θ}
*)
Axiom proof_rule_sequence :
  forall Γ τ φ ψ θ c₁ c₂ h₁ h₂,
    correct Γ c₁ RCommand (totally Γ c₁ RCommand φ h₁ ψ) ->
    correct Γ c₂ τ (totally Γ c₂ τ ψ h₂ θ) ->
    correct Γ (Sequence c₁ c₂) τ (totally Γ (Sequence c₁ c₂) τ φ (has_type_Sequence Γ c₁ c₂ τ h₁ h₂) θ).


(*
;Γ,Δ ⊢ {φ} e {y : τ | ψ}
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {φ ∧ ∀ y : τ. (ψ -> θ[y/x]} x:= e {θ}
*)

Lemma trans_lst : forall Γ, m_context Γ = m_context (readonly Γ).
Proof.
Admitted.

(*
;Γ,Δ ⊢ {φ} e {x : σ | ψ}  x:σ,Γ; Δ ⊢ {ψ} c {y : τ | θ} x ∉ Γ;Δ
——————————————————-—————————————————-—–———————————————- (r.newvar)
Γ;Δ ⊢ {φ} newvar x := e in c {y : τ | ∃ x : γ. θ}
 *)
Check eq_rect.
Definition ttt (x : nat) := x + 4.
Axiom wtf : Z = nat.
Check eq_refl.
Check eq_sym.


Axiom proof_rule_newvar :
  forall Γ σ σ' φ ψ θ τ e c h₁ h₂ s (g : in_context Γ s -> False),
    correct (readonly Γ) e σ (totally (readonly Γ) e σ φ h₁ ψ) ->
    σ = RData σ' ->
    correct (add_rw Γ s σ') c τ (totally  (add_rw Γ s σ') c τ (merge (m_context Γ) σ s ψ) h₂ θ) ->
    correct Γ c τ (totally Γ (Newvar s e c) τ φ
                           (has_type_newvar Γ s τ σ e c g h₁ h₂)
                           (fun δ => exists x, θ (state_union x δ))). 
                           


(*
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {θ(x)} x {y : τ | θ(y)}
*)

*)

