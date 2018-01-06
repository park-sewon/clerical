Require Import ZArith.
Require Import String.
Require Import Bool.
Require Import List.
Require Import Reals.


Require Import Aux0.
Require Import Clerical.
Require Import Aux_Clerical.
Require Import Typing.
Require Import Semantics.
Require Import Assertions.
(* proof rules by discussion between Andrej Bauer, Sewon Park and Alex Simpson
   Implementation detail discussed between Franz B. and Sewon Park *)

(*
—————————————————- (r.skip)
Γ;Δ ⊢ {θ} skip {θ}
*)
Axiom proof_rule_skip :
  forall Γ p, correct (totally Γ SKIP DUnit p p).

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
    has_type Γ c₁ DUnit -> has_type Γ c₂ τ ->
    correct (totally Γ c₁ DUnit φ ψ) ->
    correct (totally Γ c₂ τ ψ θ) ->
    correct (totally Γ (c₁ ;; c₂) τ φ θ).

(*
;Γ,Δ ⊢ {φ} e {x : σ | ψ}  x:σ,Γ; Δ ⊢ {ψ} c {y : τ | θ} x ∉ Γ;Δ
——————————————————-—————————————————-—–———————————————- (r.newvar)
Γ;Δ ⊢ {φ} newvar x := e in c {y : τ | ∃ x : γ. θ}
 *)
Axiom proof_rule_newvar :
  forall Γ σ φ ψ τ e c s θ,
    not_ctx_mem_tv Γ (Id s, σ) ->
    correct (totally (readonly Γ) e σ φ ψ) ->
    correct (totally (add_rw_ctx Γ (Id s, σ)) c τ (push_state s (collapse_rev ψ)) θ) ->
    correct (totally Γ (Newvar s e c) τ (collapse_rev φ)
                     (fun y δ => exists x,
                         let v := (Id s, σ) in let Δ := ctx_collapse Γ in 
                         let γ' := cons_state (v :: Δ) v Δ  δ eq_refl x in (θ y γ'))
            ).


(*
;Γ,Δ ⊢ {φ} e {y : τ | ψ}
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {φ ∧ ∀ y : τ. (ψ -> θ[y/x]} x:= e {θ}
*)
Axiom proof_rule_assignment :
  forall Γ s e τ φ ψ θ (p : ctx_mem_tv_rw Γ (Id s, τ)),
    correct (totally (readonly Γ) e τ φ ψ) ->
    correct (totally Γ (SET s := e) DUnit
                     ((collapse_rev φ) ∧
                      (fun _ δ => forall y,
                       (collapse_rev ψ) y δ -> rewrite_void θ (Id s, τ) (ctx_mem_trans_rw Γ (Id s, τ) p) (rewrite_aux_1 τ s y) δ    
                      )) θ 

            ).

(*
x:τ ∈ Γ 
——————————————————-—————————————————-—–———————————————- (r.variable)
Γ;Δ ⊢ {θ} x {y : τ | θ(y)}
*)
Axiom proof_rule_variable :
  forall Γ x τ θ (p :  ctx_mem_tv Γ (Id x, τ)),
    correct (totally Γ (Var x) τ θ (fun y δ => θ tt δ /\ val_tot δ (Id x, τ) (ctx_mem_trans Γ (Id x, τ) p) = rewrite_aux_1 τ x y)).
    

(*
;Γ,Δ ⊢ {φ} e₁ {y : τ₁ | ψ₁} ... ;Γ,Δ ⊢ {φ} eᵢ {y : τᵢ | ψᵢ} 
—————————————————————————————————————————————-—————————————————-—–———————————————- (r.operator)
Γ;Δ ⊢ {φ} op(e₁, ..., eᵢ) {y : τ |∃ y₁,...,yᵢ, y = [[op]](y₁, ..., yᵢ) ∧ ψ₁∧...∧ψᵢ}
 *)
(* --- uniop ---*)
Axiom proof_rule_uniop :
  forall Γ e u τ₁ τ φ ψ
         (p₁ : sem_datatype τ₁ = sem_datatype (uni_type u false))
         (p₂ : sem_datatype (uni_type u true) =  sem_datatype τ),
    correct (totally (readonly Γ) e τ₁ φ ψ) ->
    correct (totally Γ (UniOp u e) τ (collapse_rev φ)
                     (fun y δ => exists y₁,
                          (collapse_rev ψ) y₁ δ /\ y = eq_Set p₂ (sem_UniOp u (eq_Set p₁ y₁)))).

(* --- binop --- *)
Axiom proof_rule_binop :
  forall Γ e₁ e₂ b τ₁ τ₂ τ φ ψ₁ ψ₂
         (p₁ : sem_datatype τ₁ = sem_datatype(bin_type b one))
         (p₂ : sem_datatype τ₂ = sem_datatype(bin_type b two))
         (p₃ : sem_datatype (bin_type b third) = sem_datatype τ),
    correct (totally (readonly Γ) e₁ τ₁ φ ψ₁) ->
    correct (totally (readonly Γ) e₂ τ₂ φ ψ₂) ->
    correct (totally Γ (BinOp b e₁ e₂) τ (collapse_rev φ)
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

Axiom proof_rule_case :
  forall Γ e₁ e₂ c₁ c₂ τ T₁ T₂ F₁ F₂ φ ψ,
    correct (totally (readonly Γ) e₁ DBoolean T₁ (return_is_true (ctx_collapse (readonly Γ)))) ->
    correct (totally (readonly Γ) e₂ DBoolean T₂ (return_is_true (ctx_collapse (readonly Γ)))) ->
    correct (totally (readonly Γ) e₁ DBoolean (T₂ ∧ F₁) (return_is_false (ctx_collapse (readonly Γ)))) ->
    correct (totally (readonly Γ) e₂ DBoolean (T₁ ∧ F₂) (return_is_false (ctx_collapse (readonly Γ)))) ->
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
    correct (totally (readonly Γ) e DBoolean I (return_is_defined (ctx_collapse (readonly Γ)))) ->
    correct (totally (readonly Γ) e DBoolean T (return_is_true (ctx_collapse (readonly Γ)))) ->
    (forall δ, exists! n : Z, ψ n δ) ->
    correct (totally (readonly Γ) e DBoolean (F ∨ (fun _ δ => (exists z, (ψ z δ /\ (z < 0)%Z)))) (return_is_false (ctx_collapse (readonly Γ)))) ->
    (forall z₀, correct (totally Γ c DUnit
                                ((collapse_rev I) ∧ (¬ (collapse_rev F)) ∧ (fun _ δ => ψ z₀ (s_collapse δ)))
                                (collapse_rev (I ∧ fun _ δ => (forall z, ψ z δ -> (z < z₀)%Z)))
    )) ->
    correct (totally Γ (While e c) DUnit (collapse_rev I) (collapse_rev (I ∧ (¬ T)))).
        
(*
;x : int,Γ,Δ ⊢ {φ'} e {y : Real | ψ'}    φ -> ∀ x ≥ 0. φ' | φ -> ∀ x ≥ 0, y,z (ψ ∧ ψ' → |z-y| ≤ 2⁻ˣ)
——————————————————-—————————————————-—–—  (r.lim)
Γ;Δ ⊢ {φ} lim x.e {z : Real | ψ}
 *)
Axiom proof_rule_limit :
  forall Γ s e φ φ' ψ' (ψ : assertion (ctx_collapse (readonly Γ)) DReal),
    correct (totally (add_ro_ctx (readonly Γ) (Id s, DInteger)) e DReal φ' ψ') ->
    (φ ->> (fun y δ => forall x : Z, let v := (Id s, DInteger) in
                                    let δ' := cons_state (ctx_collapse (add_ro_ctx (readonly Γ) v)) v (ctx_collapse (readonly Γ)) δ eq_refl x in  φ' y δ')) ->
    (forall n y z δ,
      φ tt δ -> let v := (Id s, DInteger) in
                (ψ' y (cons_state (ctx_collapse (add_ro_ctx (readonly Γ) v)) v (ctx_collapse (readonly Γ)) δ eq_refl n)) /\ ψ z δ -> (Rabs (y - z) <= ι n)%R) ->
    correct (totally Γ (Lim s e) DReal (collapse_rev φ) (collapse_rev ψ)).
                

Section Examples.
  Definition trivial_prog_1 :=
    NEWVAR "y" := Real 1 IN
                       (
                         SET "x" := VAR "x" +r VAR "y"
                       ) ;;
                       VAR "x".
  Definition Γ₀ : context := ((Id "x", DReal), true) :: empty_context.
  Eval compute in (judge_type Γ₀ trivial_prog_1).
  Definition x := (Id "x", DReal).
  Definition y := (Id "y", DReal).
  Definition Γ := ctx_collapse Γ₀.
  Lemma mem_x : (cctx_mem_fun Γ x = true).
  Proof. compute; trivial. Qed.
  
  Definition φ : assertion (ctx_collapse Γ₀) DUnit := fun _ δ => (val_tot δ x mem_x) > 0.
  Definition ψ : assertion (ctx_collapse Γ₀) DReal := fun y δ => y > 1.
  Lemma prog_1_is_correct : correct (totally Γ₀ trivial_prog_1 DReal φ ψ).
  Proof.
  Admitted.
  
  Definition Squareroot :=
    Lim "n" (
          NEWVAR "a" := Real 1 IN (
                               WHILE
                                 MCASE
                                 ABS ((VAR "a") -r (VAR "z") /r (VAR "a")) >r Prec (VAR "n") ==> TRUE OR ABS ((VAR "a") -r (VAR "z") /r (VAR "a")) <r Prec (VAR "n") ==> FALSE END DO
                                                                                                                                                      SET "a" := ((VAR "a") +r (VAR "z") /r (VAR "a")) /r Real 2
                                                                                                                                                                                                       END)).
  
  Definition Γ₁  : context := add_rw empty_context  "z" DReal.
  
  Lemma mem_z : (cctx_mem_fun (ctx_collapse Γ₁) (Id "z", DReal)) = true.
  Proof. compute; exact eq_refl. Qed.
  
  Definition precond : assertion (ctx_collapse Γ₁) DUnit := fun _ δ => (val_tot δ (Id "z", DReal) mem_z > 0)%R.
  Definition postcond : assertion (ctx_collapse Γ₁) DReal := fun y δ => (val_tot δ (Id "z", DReal) mem_z = y)%R.

  Lemma square_root_is_correct : correct (totally Γ₁ Squareroot DReal precond postcond).
  Proof.
    Admitted.
End Examples.