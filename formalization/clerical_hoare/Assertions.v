Require Import Aux0.
Require Import Clerical.
Require Import Typing.
Require Import Semantics.

Require Import Bool.
Require Import List.
Require Import String.

Definition cctx := list typed_variable.

(* partial evaluation *)
Fixpoint val {Γ : cctx} (γ : state Γ) (v : typed_variable) : option (sem_datatype (snd v)).
Proof.
  pose proof (bool_dec (cctx_mem_fun Γ v) true) as H; destruct H.
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

(* total evaluation *)
Fixpoint val_tot {Γ : cctx} (γ : state Γ) (v : typed_variable) (p : cctx_mem_fun Γ v = true) : sem_datatype (snd v).
Proof.
  destruct γ.
  unfold cctx_mem_fun in p.
  rewrite e in p.
  contradict p.
  exact diff_false_true.

  destruct (variable_name_type_dec v v0).
  pose proof (eq_variable_has_same_type v v0 e0).
  rewrite H.
  exact s.
  
  unfold cctx_mem_fun in p.
  rewrite <- e in p.
  rewrite e0 in p.
  fold  cctx_mem_fun in p.  
  exact (val_tot Δ γ v p).
Qed.

(* total  evaluation amonng a tuple *)
Fixpoint val_tot_t {Γ : ctx} (γ : sem_ctx Γ) (v : typed_variable) (p : ctx_mem_tv_fun Γ v = true) : sem_datatype (snd v).
Proof.
  unfold ctx_mem_tv_fun in p; unfold sem_ctx in γ.
  destruct γ.
  case_eq (cctx_mem_fun (ctx_rw Γ) v).
  intro H;  exact (val_tot s v H).
  intro  H; rewrite H in p; exact (val_tot s0 v p).
Qed.

Definition assertion (Γ : ctx) (τ : datatype) := (sem_datatype τ) -> sem_ctx Γ -> Prop. 
Definition return_is_true (Γ : ctx) : assertion Γ DBoolean := fun y δ => y = true.
Definition return_is_false (Γ : ctx) : assertion Γ DBoolean := fun y δ => y = false.
Definition return_is_defined (Γ : ctx) (τ : datatype) : assertion Γ τ := fun y δ => True.

(* pop and push of state and assertion:
   - pop : given a state γ which is defined over w :: Δ, return a tuple of (w, δ) where δ is a state defined over Δ
   - push : given an assertion defined over y → Γ → prop, return an assertion over * -> y :: Γ -> prop
 *)

Definition pop_state {Γ : cctx} {w : typed_variable} (γ : state (w :: Γ)) :
  (sem_datatype (snd  w)) *  state Γ.
Proof.
  inversion γ.
  symmetry in H; apply nil_cons in H; contradict H.
  
  apply list_eq_destruct in H; destruct H.
  rewrite <- H1, <-  H; exact (H0, X).
Qed.


Definition push_assertion {Γ : ctx} {τ : datatype} (s : string) (ψ : assertion Γ τ) :
  assertion (add_rw_ctx Γ (Id s, τ)) DUnit :=
  fun _ δ => let (y, δ') := pop_state (fst δ) in ψ y (δ', snd δ).
  
Lemma empty_context_is : readonly empty_ctx = empty_ctx.
Proof.
  simpl; trivial.
Qed.


(* return φ[y/x] which is τ -> Γ -> prop  *)
Definition rewrite_void {Γ : ctx} (φ : assertion Γ DUnit) (v : typed_variable) (p :ctx_mem_tv_fun Γ v = true)
  : assertion Γ (snd v)
:= fun y δ => val_tot_t δ v p = y /\ φ tt δ.



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

Definition implies {Γ : ctx} {τ : datatype} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ -> q x γ.

Definition implies_2 {Γ : ctx} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ
  := fun y γ => p y γ -> q y γ.

Definition conjs {Γ : ctx} {τ : datatype} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ /\ q x γ.

Definition conjs_2 {Γ : ctx} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ /\ q x γ.

Definition disjs {Γ : ctx} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ \/ q x γ.


Definition negate {Γ : ctx} {τ : datatype} (p : assertion Γ τ) : assertion Γ τ
  := fun y γ => ~ p y γ.

Inductive  triple (Γ : ctx) (c : comp) (τ : datatype)
  := totally : assertion Γ DUnit -> assertion Γ τ -> triple Γ c τ.

Definition correct  {Γ : ctx} {c : comp} {τ : datatype} (h : triple Γ c τ) := Type.


Notation "p ->> q" := (implies  p q) (at level 80) : hoare_scope.
Notation "p //\ q" := (conjs  p q) (at level 80) : hoare_scope.
Notation "p → q" := (implies_2  p q) (at level 80) : hoare_scope.
Notation "p ∧ q" := (conjs_2  p q) (at level 80) : hoare_scope.
Notation "p ∨ q" := (disjs  p q) (at level 80) : hoare_scope.
Notation "¬ p" := (negate  p) (at level 80) : hoare_scope.
Notation "'ι' n" := (prec_embedding n) (at level 60) : hoare_scope.
Open Scope hoare_scope.