Require Import ZArith.
Require Import String.
Require Import Bool.
Require Import List.

Require Import Aux0.
Require Import Clerical.
Require Import Aux_Clerical.
Require Import Typing.
Require Import Semantics.

(* proof rules by discussion between Andrej Bauer, Sewon Park and Alex Simpson
   Implementation detail discussed between Franz B. and Sewon Park *)


(* State inductively defined via a context.
   val is a function that returns value of v within Γ *)
Inductive state (Γ : context) : Type :=
| emty_state : Γ = nil -> state Γ
| cons_state : forall v Δ b, state Δ -> (v, b) :: Δ = Γ -> (sem_datatype (snd v)) -> state Γ.

(* partial state evaluation *)
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
  exact None.
Qed.

(* total state evaluation given that v is member of Γ *)
Fixpoint val_tot {Γ : context} (γ : state Γ) (v : typed_variable) (p : ctx_mem_tv Γ v) : sem_datatype (snd v).
Proof.
  destruct p.
  destruct γ.

  (* contradiction c :: Γ = nil *)
  symmetry in e;   pose proof (nil_cons e) as q; contradict q.
  destruct (variable_name_type_dec v w).
  rewrite (eq_variable_has_same_type v w e0).
  pose proof (list_eq_destruct e).
  destruct H.
  pose proof (split_pair H).
  destruct H1.
  rewrite<- H1.
  exact s.

  pose proof (list_eq_destruct e).
  destruct H.
  rewrite H0 in γ.
  exact (val_tot Γ γ v p).
  destruct γ.
  symmetry in e0;   pose proof (nil_cons e0) as q; contradict q.
  rewrite (eq_variable_has_same_type v w e).
  pose proof (list_eq_destruct e0).
  destruct H.
  pose proof (split_pair H).
  destruct H1.
  rewrite<- H1.
  exact s.
Qed.

Definition assertion (Γ : context) (τ : datatype) := (sem_datatype τ) -> state  Γ -> Prop. 
Definition return_is_true (Γ : context) : assertion Γ DBoolean := fun y δ => y = true.
Definition return_is_false (Γ : context) : assertion Γ DBoolean := fun y δ => y = false.
Definition return_is_defined (Γ : context) : assertion Γ DBoolean := fun y δ => y = true \/ y = false.


Definition pop_state {Γ : context} {w : typed_variable * bool} (γ : state (w :: Γ)) :
  (sem_datatype (snd (fst w))) *  state Γ.
Proof.
  inversion γ.
  symmetry in H; apply nil_cons in H; contradict H.
  apply list_eq_destruct in H; destruct H.
  elim H.
  simpl.
  rewrite <- H1; exact (H0, X).
Qed.

Definition merge_rw {Γ : context} {τ : datatype} (s : string) (ψ : assertion Γ τ) :
  assertion (add_rw_ctx Γ (Id s, τ)) DUnit :=
  fun _ δ => let (y, γ) := pop_state δ in ψ y γ.
  
Lemma empty_context_is : readonly nil = nil.
Proof.
  simpl; trivial.
Qed.

Lemma readonly_cons : forall v Γ b, (v, false) :: readonly Γ = readonly ((v, b) :: Γ).
Proof.
  intros; simpl; trivial.
Qed.

Lemma readonly_cons_2 : forall v Γ b, (v, false) :: readonly Γ = readonly ((v, b) :: Γ).
Proof.
  intros; simpl; trivial.
Qed.


Fixpoint s_collapse {Γ : context} (γ : state Γ) : state (readonly Γ).
Proof.
  inversion γ.
  rewrite  H.
  rewrite empty_context_is.
  exact (emty_state nil eq_refl).

  pose proof (readonly_cons v Δ b).
  rewrite H in H1.
  exact (cons_state (readonly Γ) v (readonly Δ) false (s_collapse Δ X) H1 H0).
Qed.

Fixpoint s_collapse_rev {Γ : context} (γ : state (readonly Γ)) : state Γ.
Proof.
  inversion γ.
  assert (Γ = nil).
  destruct Γ.
  trivial.
  simpl in H; symmetry in H; destruct p; apply nil_cons in H; contradict H.

  rewrite H0.
  exact (emty_state nil eq_refl).
  destruct Γ.
  simpl in H; symmetry in H; apply nil_cons in H; contradict H.
  destruct p.
  simpl in H.
  apply (list_eq_destruct) in H; destruct H.
  rewrite H1 in X.
  pose proof (s_collapse_rev Γ X).
  apply (split_pair) in H; destruct H.
  rewrite <- H.
  exact (cons_state ((v, b0) :: Γ) v Γ b0 X0  eq_refl H0).
Qed.
  
Definition collapse {Γ : context} {τ : datatype} (ψ : assertion Γ τ) :
  assertion (readonly Γ) τ := fun y (δ : state (readonly Γ)) => ψ y (s_collapse_rev δ).
  
Definition collapse_rev {Γ : context} {τ : datatype} (ψ : assertion (readonly Γ) τ) :
  assertion Γ τ := fun y δ => ψ y (s_collapse δ).

(* return φ[y/x] which is τ -> Γ -> prop 
!!!! needs closer look whether this is really rewritting !!!!*)
Definition rewrite_void {Γ : context} (φ : assertion Γ DUnit) (v : typed_variable) (p :ctx_mem_tv Γ v)
  : assertion Γ (snd v)
:= fun y δ => val_tot δ v p = y /\ φ tt δ.

Lemma t₁ : forall s τ, sem_datatype τ = sem_datatype (snd (Id s, τ)).
Proof.
  intros.
  assert (τ = snd (Id s, τ)). 
  simpl.
  trivial.
  rewrite<- H.
  trivial.
Qed.

Definition rewrite_aux_1 (τ :datatype) (s :string) :   sem_datatype τ -> sem_datatype (snd (Id s, τ)).
Proof.
  pose proof t₁ s τ.
  rewrite H.
  intro.
  exact H0.
Qed.

Definition implies {Γ : context} {τ : datatype} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ -> q x γ.

Definition implies_2 {Γ : context} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ
  := fun y γ => p y γ -> q y γ.

Definition conjs {Γ : context} {τ : datatype} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ /\ q x γ.

Definition conjs_2 {Γ : context} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ /\ q x γ.

Definition disjs {Γ : context} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ \/ q x γ.


Definition negate {Γ : context} {τ : datatype} (p : assertion Γ τ) : assertion Γ τ
  := fun y γ => ~ p y γ.

(* hoare triple is defined for well--typed commands *)
Inductive  triple (Γ : context) (c : comp) (τ : datatype)
  := totally : assertion Γ DUnit -> assertion Γ τ -> triple Γ c τ.

Definition correct  {Γ : context} {c : comp} {τ : datatype} (h : triple Γ c τ) := Type.


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
    correct (totally (add_rw_ctx Γ (Id s, σ)) c τ (merge_rw s (collapse_rev ψ)) θ) ->
    correct (totally Γ (Newvar s e c) τ (collapse_rev φ)
                     (fun y δ => exists x,
                         let v := (Id s, σ) in
                         let γ' := cons_state (add_rw_ctx Γ v) v Γ true δ eq_refl x in (θ y γ'))
            ).

  
(*
;Γ,Δ ⊢ {φ} e {y : τ | ψ}
——————————————————-—————————————————-—–———————————————- (r.assignment)
Γ;Δ ⊢ {φ ∧ ∀ y : τ. (ψ -> θ[y/x]} x:= e {θ}
*)
Axiom proof_rule_assignment :
  forall Γ s e τ φ ψ θ (p : ctx_mem_tv Γ (Id s, τ)),
    correct (totally (readonly Γ) e τ φ ψ) ->
    correct (totally Γ (SET s := e) DUnit
                     ((collapse_rev φ) ∧
                      (fun _ δ => forall y,
                       (collapse_rev ψ) y δ -> rewrite_void θ (Id s, τ) p (rewrite_aux_1 τ s y) δ    
                      )) θ 

            ).


(*
x:τ ∈ Γ 
——————————————————-—————————————————-—–———————————————- (r.variable)
Γ;Δ ⊢ {θ} x {y : τ | θ(y)}
*)
Axiom proof_rule_variable :
  forall Γ x τ θ (p :  ctx_mem_tv Γ (Id x, τ)),
    correct (totally Γ (Var x) τ θ (fun y δ => θ tt δ /\ val_tot δ (Id x, τ) p = rewrite_aux_1 τ x y)).
    

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
    correct (totally (readonly Γ) e₁ DBoolean T₁ (return_is_true (readonly Γ))) ->
    correct (totally (readonly Γ) e₂ DBoolean T₂ (return_is_true (readonly Γ))) ->
    correct (totally (readonly Γ) e₁ DBoolean (T₂ ∧ F₁) (return_is_false (readonly Γ))) ->
    correct (totally (readonly Γ) e₂ DBoolean (T₁ ∧ F₂) (return_is_false (readonly Γ))) ->
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
    correct (totally (readonly Γ) e DBoolean I (return_is_defined (readonly Γ))) ->
    correct (totally (readonly Γ) e DBoolean T (return_is_true (readonly Γ))) ->
    (forall δ, exists! n : Z, ψ n δ) ->
    correct (totally (readonly Γ) e DBoolean (F ∨ (fun _ δ => (exists z, (ψ z δ /\ (z < 0)%Z)))) (return_is_false (readonly Γ))) ->
    (forall z₀, correct (totally Γ c DUnit
                                ((collapse_rev I) ∧ (¬ (collapse_rev F)) ∧ (fun _ δ => ψ z₀ (s_collapse δ)))
                                (collapse_rev (I ∧ fun _ δ => (forall z, ψ z δ -> (z < z₀)%Z)))
    )) ->
    correct (totally Γ (While e c) DUnit (collapse_rev I) (collapse_rev (I ∧ (¬ T)))).
        



Require Import Reals.

(*
;x : int,Γ,Δ ⊢ {φ'} e {y : Real | ψ'}    φ -> ∀ x ≥ 0. φ' | φ -> ∀ x ≥ 0, y,z (ψ ∧ ψ' → |z-y| ≤ 2⁻ˣ)
——————————————————-—————————————————-—–—  (r.lim)
Γ;Δ ⊢ {φ} lim x.e {z : Real | ψ}
 *)
Axiom proof_rule_limit :
  forall Γ s e φ φ' ψ' (ψ : assertion (readonly Γ) DReal),
    correct (totally (add_ro_ctx (readonly Γ) (Id s, DInteger)) e DReal φ' ψ') ->
    φ ->> (fun y δ => forall x : Z, let v := (Id s, DInteger) in
                                    let δ' := cons_state (add_ro_ctx (readonly Γ) v) v (readonly Γ) false δ eq_refl x in φ' y δ') ->
    (forall n y z δ,
      φ tt δ -> let v := (Id s, DInteger) in
                (ψ' y (cons_state (add_ro_ctx (readonly Γ) v) v (readonly Γ) false δ eq_refl n)) /\ ψ z δ -> (Rabs (y - z) <= ι n)%R) ->
    correct (totally Γ (Lim s e) DReal (collapse_rev φ) (collapse_rev ψ)).
                
                

Section Examples.
  Definition Squareroot :=
    Lim "n" (
          NEWVAR "a" := Real 1 IN (
                               WHILE
                                   MCASE
                                   ABS ((VAR "a") -r (VAR "z") /r (VAR "a")) >r Prec (VAR "n") ==> TRUE OR ABS ((VAR "a") -r (VAR "z") /r (VAR "a")) <r Prec (VAR "n") ==> FALSE END DO
                                                                                                                                                        SET "a" := ((VAR "a") +r (VAR "z") /r (VAR "a")) /r Real 2
                                                                                                                                                                                                         END)).

  Definition Γ₀  : context := add_rw empty_context  "z" DReal.
  
  Definition z_mem : ctx_mem_tv Γ₀ (Id "z", DReal).
  Proof.
    assert (ctx_mem_tv_fun Γ₀ (Id "z", DReal) = true).
    compute; trivial.
    exact (ctx_mem_tv_imp Γ₀ (Id "z", DReal) H).
  Qed.

  Definition precond : assertion Γ₀ DUnit := fun _ δ => (val_tot δ (Id "z", DReal) z_mem > 0)%R.
  Definition postcond : assertion Γ₀ DReal := fun y δ => (val_tot δ (Id "z", DReal) z_mem = y)%R.

  Lemma square_root_is_correct : correct (totally Γ₀ Squareroot DReal precond postcond).
                          
