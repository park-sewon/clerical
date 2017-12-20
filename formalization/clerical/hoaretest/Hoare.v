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


Definition assertion (Γ : context) (τ : result_type) := (sem_result_type τ) -> state  Γ -> Prop. 

(* unproved stuffs......... *)

(* total function of evaluation with given that Γ contains v *)
Definition val_tot {Γ : context} (γ : state Γ) (v : typed_variable) (p : in_context_t Γ v) : sem_datatype (snd v).
Proof.
Admitted.

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

Definition s_collapse {Γ : context} (γ : state Γ) : state (readonly Γ).
Proof.
Admitted.

Definition s_collapse_rev {Γ : context} (γ : state (readonly Γ)) : state Γ.
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

Definition rewrite_aux_1 (τ : result_type) (s : string) :   sem_result_type τ -> sem_result_type (RData (snd (Id s, origin_type τ))).
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

Definition disjs {Γ : context} {τ : result_type} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ \/ q x γ.


Definition negate {Γ : context} {τ : result_type} (p : assertion Γ τ) : assertion Γ τ
  := fun y γ => ~ p y γ.

(* hoare triple is defined for well--typed commands *)
Inductive  triple (Γ : context) (c : comp) (τ : result_type) : Type
  := totally : assertion Γ RCommand -> assertion Γ τ -> triple Γ c τ.

Definition correct  {Γ : context} {c : comp} {τ : result_type} (h : triple Γ c τ) := Type.


Notation "p ->> q" := (implies  p q) (at level 80) : hoare_scope.
Notation "p //\ q" := (conjs  p q) (at level 80) : hoare_scope.
Notation "p → q" := (implies_2  p q) (at level 80) : hoare_scope.
Notation "p ∧ q" := (conjs_2  p q) (at level 80) : hoare_scope.
Notation "p ∨ q" := (disjs  p q) (at level 80) : hoare_scope.
Notation "¬ p" := (negate  p) (at level 80) : hoare_scope.
Notation "'ι' n" := (prec_embedding n) (at level 60) : hoare_scope.
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
                       (collapse_rev ψ) y δ -> rewrite_void θ (Id s, origin_type τ) (rewrite_aux_1 τ s y) δ    
                      )) θ 

            ).


(*
x:τ ∈ Γ 
——————————————————-—————————————————-—–———————————————- (r.variable)
Γ;Δ ⊢ {θ} x {y : τ | θ(y)}
*)
Axiom proof_rule_variable :
  forall Γ x τ θ (p :  in_context_t Γ (Id x, origin_type τ)),
    correct (totally Γ (Var x) τ θ (fun y δ => θ tt δ /\ val_tot δ (Id x, origin_type τ) p = rewrite_aux_1 τ x y)).
    

(* is this okay to have this? *)
Definition eq_Set {A B : Set} (p : A = B) (a : A) : B.
Proof.
  rewrite<- p.
  exact a.
Qed.

Definition eq_Type {A B : Type} (p : A = B) (a : A) : B.
Proof.
  rewrite<- p.
  exact a.
Qed.


(*
;Γ,Δ ⊢ {φ} e₁ {y : τ₁ | ψ₁} ... ;Γ,Δ ⊢ {φ} eᵢ {y : τᵢ | ψᵢ} 
—————————————————————————————————————————————-—————————————————-—–———————————————- (r.operator)
Γ;Δ ⊢ {φ} op(e₁, ..., eᵢ) {y : τ |∃ y₁,...,yᵢ, y = [[op]](y₁, ..., yᵢ) ∧ ψ₁∧...∧ψᵢ}
 *)
(* --- uniop ---*)
Axiom proof_rule_uniop :
  forall Γ e u τ₁ τ φ ψ
         (p₁ : sem_result_type τ₁ = sem_datatype (uni_type u false))
         (p₂ : sem_datatype (uni_type u true) =  sem_result_type (RData τ)),
    correct (totally (readonly Γ) e τ₁ φ ψ) ->
    correct (totally Γ (UniOp u e) (RData τ) (collapse_rev φ)
                     (fun y δ => exists y₁,
                          (collapse_rev ψ) y₁ δ /\ y = eq_Set p₂ (sem_UniOp u (eq_Set p₁ y₁)))).

(* --- binop --- *)
Axiom proof_rule_binop :
  forall Γ e₁ e₂ b τ₁ τ₂ τ φ ψ₁ ψ₂
         (p₁ : sem_result_type τ₁ = sem_datatype(bin_type b one))
         (p₂ : sem_result_type τ₂ = sem_datatype(bin_type b two))
         (p₃ : sem_datatype (bin_type b third) = sem_result_type (RData τ)),
    correct (totally (readonly Γ) e₁ τ₁ φ ψ₁) ->
    correct (totally (readonly Γ) e₂ τ₂ φ ψ₂) ->
    correct (totally Γ (BinOp b e₁ e₂) (RData τ) (collapse_rev φ)
                     (fun y δ => exists y₁ y₂,
                          (collapse_rev ψ₁) y₁ δ /\ (collapse_rev ψ₂) y₂ δ /\
                          y = eq_Set p₃ (sem_BinOp b (eq_Set p₁ y₁) (eq_Set p₂ y₂)))).


(*
;Γ,Δ ⊢ {T₁} e₁ {y : bool | y = true}
;Γ,Δ ⊢ {T₂} e₂ {y : bool | y = true}
;Γ,Δ ⊢ {T₂ ∧ F₁} e₁ {y : bool | y = false}
;Γ,Δ ⊢ {T₁ ∧ F₂} e₂ {y : bool | y = false}
Γ; Δ ⊢ {φ ∧ ¬ F₁} c₁ {y : τ | ψ}
Γ; Δ ⊢ {φ ∧ ¬ F₂} c₂ {y : τ | ψ}
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {φ ∧ (T₁ ∨ T₂)} case e₁ ⇒ c₁ || e₂ ⇒ c₂ end {y : τ | ψ}
*)

Definition return_is_true (Γ : context) : assertion Γ RBoolean := fun y δ => y = true.
Definition return_is_false (Γ : context) : assertion Γ RBoolean := fun y δ => y = false.
Definition return_is_bool (Γ : context) : assertion Γ RBoolean := fun y δ => y = true \/ y = false.

Axiom proof_rule_case :
  forall Γ e₁ e₂ c₁ c₂ τ T₁ T₂ F₁ F₂ φ ψ,
    correct (totally (readonly Γ) e₁ RBoolean T₁ (return_is_true (readonly Γ))) ->
    correct (totally (readonly Γ) e₂ RBoolean T₂ (return_is_true (readonly Γ))) ->
    correct (totally (readonly Γ) e₁ RBoolean (T₂ ∧ F₁) (return_is_false (readonly Γ))) ->
    correct (totally (readonly Γ) e₂ RBoolean (T₁ ∧ F₂) (return_is_false (readonly Γ))) ->
    correct (totally Γ c₁ τ (collapse_rev (φ ∧ (¬ F₁))) ψ) ->
    correct (totally Γ c₂ τ (collapse_rev (φ ∧ (¬ F₂))) ψ) ->
    correct (totally Γ (Case e₁ c₁ e₂ c₂) τ (collapse_rev (φ ∧ (T₁ ∨ T₂))) ψ).

(*
;Γ,Δ ⊢ {I} e {y : bool | y = true ∨ y = false}
;Γ,Δ ⊢ {T} e {y : bool | y = true}
;Γ,Δ ⊢ {F ∨ ∃ z. ψ ∨ z < 0} e {y : bool | y = false}
Γ; Δ ⊢ {I ∧ ¬ F ∧ ψ[z₀/z]} c {tt | I ∧ ∀ z, ψ → z < z₀}      ψ is a formulae in programming variables x and z satisfies ∀x∃!zψ
——————————————————-—————————————————-—–———————————————- (r.while)
Γ;Δ ⊢ {I} while e do c  {tt | I ∧ ¬ T}
 *)
Axiom proof_rule_while :
  forall Γ e c I T F ψ,
    correct (totally (readonly Γ) e RBoolean I (return_is_bool (readonly Γ))) ->
    correct (totally (readonly Γ) e RBoolean T (return_is_true (readonly Γ))) ->
    (forall δ, exists! n : Z, ψ n δ) ->
    correct (totally (readonly Γ) e RBoolean (F ∨ (fun _ δ => (exists z, (ψ z δ /\ (z < 0)%Z)))) (return_is_false (readonly Γ))) ->
    (forall z₀, correct (totally Γ c RCommand
                                ((collapse_rev I) ∧ (¬ (collapse_rev F)) ∧ (fun _ δ => ψ z₀ (s_collapse δ)))
                                (collapse_rev (I ∧ fun _ δ => (forall z, ψ z δ -> (z < z₀)%Z)))
    )) ->
    correct (totally Γ (While e c) RCommand (collapse_rev I) (collapse_rev (I ∧ (¬ T)))).
        


(*
;x : int,Γ,Δ ⊢ {φ'} e {y : Real | ψ'}    φ -> ∀ x ≥ 0. φ' | φ -> ∀ x ≥ 0, y,z (ψ ∧ ψ' → |z-y| ≤ 2⁻ˣ)
——————————————————-—————————————————-—–—  (r.lim)
Γ;Δ ⊢ {φ} lim x.e {z : Real | ψ'}
 *)
Require Import Reals.
Axiom proof_rule_limit :
  forall Γ s e φ φ' ψ ψ',
    correct (totally (add_ro_ctx (readonly Γ) (Id s, DInteger)) e RReal φ' ψ') ->
    φ ->> (fun y δ => forall x : Z, let v := (Id s, DInteger) in
                                    let δ' := cons_ro (add_ro_ctx (readonly Γ) v) v (readonly Γ) δ eq_refl x in φ' y δ') ->
    forall n y z δ,
      φ tt δ -> let v := (Id s, DInteger) in
      (ψ' y (cons_ro (add_ro_ctx (readonly Γ) v) v (readonly Γ) δ eq_refl n)) /\ ψ z δ -> (Rabs (y - z) <= ι n)%R.


