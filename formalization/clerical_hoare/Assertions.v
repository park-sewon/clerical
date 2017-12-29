Require Import Aux0.
Require Import Clerical.
Require Import Aux_Clerical.
Require Import Typing.
Require Import Semantics.

Require Import Bool.
Require Import List.
Require Import String.

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
