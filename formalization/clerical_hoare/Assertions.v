Require Import Aux0.
Require Import Clerical.
Require Import Aux_Clerical.
Require Import Typing.
Require Import Semantics.

Require Import Bool.
Require Import List.
Require Import String.

Definition cctx := list typed_variable.

(* State defined as a dependent type of cctx. *)
Inductive state (Γ : cctx) : Type :=
| emty_state : Γ = nil -> state Γ
| cons_state : forall v Δ, state Δ -> v :: Δ = Γ -> (sem_datatype (snd v)) -> state Γ.

Fixpoint cctx_mem_fun (Γ : cctx) (v : typed_variable) : bool :=
  match Γ with
  | w :: Γ => if eq_tv_tv v w then true else cctx_mem_fun Γ v
  | _ => false
  end.

(* partial state evaluation *)
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

Check nil_cons.
(* total state evaluation given that v is member of Γ *)
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

Definition assertion (Γ : cctx) (τ : datatype) := (sem_datatype τ) -> state Γ -> Prop. 
Definition return_is_true (Γ : cctx) : assertion Γ DBoolean := fun y δ => y = true.
Definition return_is_false (Γ : cctx) : assertion Γ DBoolean := fun y δ => y = false.
Definition return_is_defined (Γ : cctx) : assertion Γ DBoolean := fun y δ => y = true \/ y = false.


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


Definition push_state {Γ : cctx} {τ : datatype} (s : string) (ψ : assertion Γ τ) :
  assertion ((Id s, τ) :: Γ) DUnit :=
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


Fixpoint ctx_collapse (Γ : context) : cctx :=
  match Γ with
  | (v, _) :: Δ => v :: (ctx_collapse Δ)
  | nil => nil
  end.

Lemma readonly_is_trivial : forall Γ, ctx_collapse (readonly Γ) = ctx_collapse Γ.
Proof.
  intros.
  induction Γ.
  simpl; trivial.

  simpl.
  destruct a.
  simpl.
  rewrite IHΓ.
  trivial.
Qed.

(* return φ[y/x] which is τ -> Γ -> prop  *)
Definition rewrite_void {Γ : cctx} (φ : assertion Γ DUnit) (v : typed_variable) (p :cctx_mem_fun Γ v = true)
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

Definition implies {Γ : cctx} {τ : datatype} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ -> q x γ.

Definition implies_2 {Γ : cctx} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ
  := fun y γ => p y γ -> q y γ.

Definition conjs {Γ : cctx} {τ : datatype} (p q : assertion Γ τ) : Type
  := forall x γ, p x γ /\ q x γ.

Definition conjs_2 {Γ : cctx} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ /\ q x γ.

Definition disjs {Γ : cctx} {τ : datatype} (p q : assertion Γ τ) : assertion Γ τ 
  := fun x γ => p x γ \/ q x γ.


Definition negate {Γ : cctx} {τ : datatype} (p : assertion Γ τ) : assertion Γ τ
  := fun y γ => ~ p y γ.

Inductive  triple (Γ : context) (c : comp) (τ : datatype)
  := totally : assertion (ctx_collapse Γ) DUnit -> assertion (ctx_collapse Γ) τ -> triple Γ c τ.

Definition correct  {Γ : context} {c : comp} {τ : datatype} (h : triple Γ c τ) := Type.



Lemma ctx_collapse_trivial : forall v b Γ, ctx_collapse ((v,b) :: Γ) = v  :: ctx_collapse Γ.
Proof.
  intros.
  simpl.
  trivial.
Qed.

Definition collapse_rev {Γ : context} {τ : datatype} (φ : assertion (ctx_collapse (readonly Γ)) τ) : assertion (ctx_collapse Γ) τ.
Proof.
  pose proof (readonly_is_trivial Γ).
  rewrite H in φ.
  exact φ.
Qed.


Lemma ctx_mem_trans_rw : forall Γ v, ctx_mem_tv_rw Γ v -> cctx_mem_fun (ctx_collapse Γ) v = true.
Proof.
  intros.
  induction X.
  simpl.
  case_eq (eq_tv_tv v w).
  trivial.
  intro.
  exact IHX.
  simpl; rewrite e; exact eq_refl.
Qed.  


Lemma ctx_mem_trans : forall Γ v, ctx_mem_tv Γ v -> cctx_mem_fun (ctx_collapse Γ) v = true.
Proof.
  intros.
  induction X.
  simpl.
  case_eq (eq_tv_tv v w).
  trivial.
  intro.
  exact IHX.
  simpl; rewrite e; exact eq_refl.
Qed.  

Definition s_collapse {Γ : context} (δ : state (ctx_collapse Γ)) : state (ctx_collapse (readonly Γ)).
Proof.
  rewrite <- (readonly_is_trivial) in δ; exact δ.
Qed.
 


Notation "p ->> q" := (implies  p q) (at level 80) : hoare_scope.
Notation "p //\ q" := (conjs  p q) (at level 80) : hoare_scope.
Notation "p → q" := (implies_2  p q) (at level 80) : hoare_scope.
Notation "p ∧ q" := (conjs_2  p q) (at level 80) : hoare_scope.
Notation "p ∨ q" := (disjs  p q) (at level 80) : hoare_scope.
Notation "¬ p" := (negate  p) (at level 80) : hoare_scope.
Notation "'ι' n" := (prec_embedding n) (at level 60) : hoare_scope.
Open Scope hoare_scope.