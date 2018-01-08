(* the file consists of helper functions (definitions) dereived from Clerical.v *)
Require Import String.
Require Import List.
Require Import Bool.

Require Import Clerical.





Definition eq_type (τ₁ τ₂ : datatype) : bool :=
  match τ₁, τ₂ with
  | DUnit, DUnit => true
  | DBoolean, DBoolean => true
  | DInteger, DInteger => true
  | DReal, DReal => true
  | _, _ => false
  end.

Definition name_v (v : typed_variable) : string := let v := fst v in match v with Id s => s end.
Definition type_v (v : typed_variable) : datatype := snd v.


Definition eq_tv_tv_name (v₁ v₂ : typed_variable) : bool :=
  let v₁ := fst v₁ in let v₂ := fst v₂ in
                      match v₁, v₂ with
                      | Id s₁, Id s₂ => if string_dec s₁ s₂ then true else false
                      end.

Definition eq_tv_str (v₁ : typed_variable) (s : string) : bool :=
  let v₁ := fst v₁ in  match v₁ with Id s₁ => if string_dec s₁ s then true else false end.

Definition eq_tv_tv (v₁ v₂ : typed_variable) : bool :=
  if eq_tv_tv_name v₁ v₂ then eq_type (snd v₁) (snd v₂) else false.

Lemma eq_type_sym : forall τ₁ τ₂, eq_type τ₁ τ₂ = eq_type τ₂ τ₁.
Proof.
  intros.
  destruct τ₁.
  destruct τ₂.
  trivial.
  simpl; trivial.
  simpl; trivial.
  simpl; trivial.
  simpl; trivial.
  simpl; trivial.
  simpl; trivial.
Qed.

Lemma eq_tv_tv_name_sym : forall v₁ v₂, eq_tv_tv_name v₁ v₂ = eq_tv_tv_name v₂ v₁.
Proof.
  intros.
  unfold eq_tv_tv_name.
  destruct v₁.
  destruct v₂.
  simpl.
  destruct v.
  destruct v0.
  destruct (string_dec s s0), (string_dec s0 s); trivial.
  contradict n; exact (eq_sym e).
  contradict n; exact (eq_sym e).
Qed.
  
Lemma eq_tv_tv_sym : forall v₁ v₂, eq_tv_tv v₁ v₂ = eq_tv_tv v₂ v₁.
Proof.
  intros.
  unfold eq_tv_tv.
  rewrite (eq_tv_tv_name_sym).
  rewrite (eq_type_sym).
  trivial.
Qed.
  
Definition add_rw_ctx (Γ : context) (v : typed_variable) : context := (v, true) :: Γ.
Definition add_ro_ctx (Γ : context) (v : typed_variable) : context := (v, false) :: Γ.
Definition add_rw (Γ : context) (s : string) (τ : datatype) := ((Id s, τ), true) ::  Γ.
Definition add_ro (Γ : context) (s : string) (τ : datatype) := ((Id s, τ), false) ::  Γ.

Inductive ctx_mem_str : context -> string -> Type :=
| triv : forall Γ s v b, ctx_mem_str Γ s -> ctx_mem_str ((v, b) :: Γ) s
| base : forall Γ s v b, eq_tv_str v s = true -> ctx_mem_str ((v, b) :: Γ) s.

Inductive ctx_mem_str_rw : context -> string -> Type :=
| triv_rw : forall Γ s v b, ctx_mem_str_rw Γ s -> ctx_mem_str_rw ((v, b) :: Γ) s
| base_rw : forall Γ s v, eq_tv_str v s = true -> ctx_mem_str_rw ((v, true) :: Γ) s.

Inductive ctx_mem_tv : context -> typed_variable -> Type :=
| triv_t : forall Γ v w b, ctx_mem_tv Γ v -> ctx_mem_tv ((w, b) :: Γ) v
| base_t : forall Γ v w b, eq_tv_tv v w = true -> ctx_mem_tv ((w, b) :: Γ) v.

Inductive ctx_mem_tv_rw : context -> typed_variable -> Type :=
| triv_t_rw : forall Γ v w b, ctx_mem_tv_rw Γ v -> ctx_mem_tv_rw ((w, b) :: Γ) v
| base_t_rw : forall Γ v w, eq_tv_tv v w = true -> ctx_mem_tv_rw ((w, true) :: Γ) v.

Inductive not_ctx_mem_tv : context -> typed_variable -> Type :=
| n_triv_t : forall Γ v w b, not_ctx_mem_tv Γ v -> eq_tv_tv v w = false -> not_ctx_mem_tv ((w, b) :: Γ) v
| n_base_t : forall v, not_ctx_mem_tv empty_context v.

Fixpoint readonly (Γ : context) : context :=
  match Γ with
  | (v, b) :: Γ' => (v, false) :: (readonly Γ')
  | nil => nil
  end.

Fixpoint ctx_mem_str_fun (Γ : context) (s : string) : bool :=
  match Γ with
  | (v, b) :: Γ' => if (eq_tv_str v s) then true else (ctx_mem_str_fun Γ' s)
  | nil => false
  end.

Fixpoint ctx_mem_str_fun_rw (Γ : context) (s : string) : bool :=
  match Γ with
  | (v, b) :: Γ' => if (eq_tv_str v s) then  b else (ctx_mem_str_fun_rw Γ' s)
  | nil => false
  end.

Fixpoint ctx_mem_str_fun_ro (Γ : context) (s : string) : bool :=
  match Γ with
  | (v, b) :: Γ' => if (eq_tv_str v s) then negb b else (ctx_mem_str_fun_ro Γ' s)
  | nil => false
  end.

Fixpoint ctx_locate_str_fun (Γ : context) (s : string) : option (typed_variable * bool) :=
  match Γ with
  | (v, b) :: Γ' => if (eq_tv_str v s) then Some (v, b) else (ctx_locate_str_fun Γ' s)
  | nil => None
  end.

Fixpoint ctx_mem_tv_fun (Γ : context) (v : typed_variable) : bool :=
  match Γ with
  | (w, _ ) :: Γ => if eq_tv_tv w v then true else ctx_mem_tv_fun Γ v
  | nil => false
  end.

(* function results inductive definition of context membership *)
Lemma ctx_mem_tv_imp : forall Γ s, ctx_mem_tv_fun Γ s = true -> ctx_mem_tv Γ s.
Proof.
  intros.
  induction Γ.
  contradict H.
  compute.
  exact diff_false_true.
  destruct a.
  destruct (bool_dec (eq_tv_tv t s) true).
  rewrite (eq_tv_tv_sym) in e.
  exact (base_t Γ s t b e).
  simpl in H.
  assert ((if eq_tv_tv t s then true else ctx_mem_tv_fun Γ s) = ctx_mem_tv_fun Γ s).
  case_eq (eq_tv_tv t s).
  intro.
  contradict n; exact H0.
  intro.
  trivial.
  rewrite H0 in H.
  apply IHΓ in H.
  exact (triv_t Γ s t b H).
Qed.  
  

Lemma eq_variable_has_same_type : forall v w, eq_tv_tv v w = true -> snd v = snd w.
Proof.
  intros.
  unfold eq_tv_tv in H.
  destruct (eq_tv_tv_name v w).
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

Lemma typed_mem_dec : forall Γ v, {ctx_mem_tv_fun Γ v = true} + {ctx_mem_tv_fun Γ v = false}.
Proof.
  intros Γ v.
  pose proof (bool_dec (ctx_mem_tv_fun Γ v) true).
  destruct H.
  left; trivial.
  pose proof (not_true_is_false (ctx_mem_tv_fun Γ v) n).
  right; trivial.
Qed.


Lemma variable_name_type_dec : forall v w, {eq_tv_tv v w = true} + {eq_tv_tv v w = false}.
Proof.
  intros.
  pose proof (bool_dec (eq_tv_tv v w) true).
  destruct H.
  left; trivial.
  pose proof (not_true_is_false (eq_tv_tv v w) n).
  right; trivial.
Qed.

