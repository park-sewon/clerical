(* An initial attempt at defining a language for real number comptuations, based on
   converstations with Sewon Park and Alex Simspon *)

(* This version is just a simple command language, to get us started. *)

Require Import ZArith.
Require Import List.
Require Import String.
Require Import Bool.
(*Require Import Delay.*)

(* Datatypes *)
Inductive datatype :=
  | DUnit
  | DBoolean
  | DInteger
  | DReal.

Definition eq_type (τ₁ τ₂ : datatype) : bool :=
  match τ₁, τ₂ with
  | DUnit, DUnit => true
  | DBoolean, DBoolean => true
  | DInteger, DInteger => true
  | DReal, DReal => true
  | _, _ => false
  end.

(* Primitive operators  | todo: separate the operators by their operands' types? *)
Inductive binary_op :=
  | OpPlusInt | OpMultInt | OpSubInt
  | OpPlusReal | OpMultReal | OpSubReal | OpDivReal
  | OpLtInt | OpEqInt | OpGtInt | OpLeInt | OpGeInt 
  | OpLtReal | OpGtReal
  | OpAnd | OpOr.

Inductive unary_op :=
  | OpNot | OpNegInt | OpNegReal | OpABS | OpPrec.

Fixpoint binary_op_type (op : binary_op) : option datatype -> option datatype -> option datatype :=
  match op with
  | OpPlusInt => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DInteger | _, _ => None  end
  | OpMultInt => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DInteger | _, _ => None  end
  | OpSubInt => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DInteger | _, _ => None  end
  | OpPlusReal => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DReal , Some DReal => Some DReal | _, _ => None  end
  | OpMultReal => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DReal, Some DReal => Some DReal | _, _ => None  end
  | OpSubReal => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DReal, Some DReal => Some DReal | _, _ => None  end
  | OpDivReal => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DReal, Some DReal => Some DReal | _, _ => None  end
  | OpLtInt => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DBoolean | _, _ => None  end
  | OpEqInt => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DBoolean | _, _ => None  end
  | OpGtInt => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DBoolean | _, _ => None  end
  | OpLeInt => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DBoolean | _, _ => None  end
  | OpGeInt  => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DInteger, Some DInteger => Some DBoolean | _, _ => None  end
  | OpLtReal => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DReal, Some DReal => Some DBoolean | _, _ => None  end
  | OpGtReal => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DReal, Some DReal => Some DBoolean | _, _ => None  end
  | OpAnd => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DBoolean, Some DBoolean => Some DBoolean | _, _ => None  end
  | OpOr => fun τ₁ τ₂ => match τ₁, τ₂ with | Some DBoolean, Some DBoolean  => Some DBoolean | _, _ => None  end
  end.

Fixpoint unary_op_type (op : unary_op) :option datatype -> option datatype :=
  match op with
  | OpNot => fun τ => match τ with | Some DBoolean => Some DBoolean | _ => None  end
  | OpNegInt => fun τ => match τ with | Some DInteger => Some DInteger | _ => None  end
  | OpNegReal => fun τ => match τ with | Some DReal => Some DReal | _ => None  end
  | OpABS => fun τ => match τ with | Some DReal => Some DReal | _ => None end
  | OpPrec => fun τ => match τ with | Some DInteger => Some DReal | _ => None end
  end.



(* Variable and Context *)
Inductive variable := Id : string -> variable.
Definition typed_variable : Type := (variable * datatype).
Definition name_v (v : typed_variable) : string := let v := fst v in match v with Id s => s end.
Definition type_v (v : typed_variable) : datatype := snd v.

Definition context : Type := list (typed_variable * bool).
             


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
  
Definition empty_context : context := nil.

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
  
Require Import Reals.
(* Computations *)
Inductive comp :=
  | Var : string -> comp
  | Boolean : bool -> comp
  | Integer : Z -> comp
  | Real : R -> comp
  | BinOp : binary_op -> comp -> comp -> comp
  | UniOp : unary_op -> comp -> comp
  | Skip : comp
  | Sequence : comp -> comp -> comp
  | Case : comp -> comp -> comp -> comp -> comp
  | While : comp -> comp -> comp
  | Newvar : string -> comp -> comp -> comp
  | Assign : string -> comp -> comp
  | Lim : string -> comp -> comp.


(* Notations for writing clerical programs. *)

Notation "'VAR' s" := (Var s) (at level 30) : clerical_scope.

Notation "'TRUE'" := (Boolean true) : clerical_scope.

Notation "'FALSE'" := (Boolean false) : clerical_scope.

Notation "'INT' k" := (Integer k) (at level 30) : clerical_scope.

Notation "e1 '+z' e2" := (BinOp OpPlusInt e1 e2) (at level 60, right associativity) : clerical_scope.

Notation "e1 '-z' e2" := (BinOp OpSubInt e1 e2) (at level 60, right associativity) : clerical_scope.

Notation "e1 '*z' e2" := (BinOp OpMultInt e1 e2) (at level 55, right associativity) : clerical_scope.

Notation "e1 '+r' e2" := (BinOp OpPlusReal e1 e2) (at level 60, right associativity) : clerical_scope.

Notation "e1 '-r' e2" := (BinOp  OpSubReal  e1 e2) (at level 60, right associativity) : clerical_scope.

Notation "e1 '*r' e2" := (BinOp OpMultReal e1 e2) (at level 55, right associativity) : clerical_scope.

Notation "e1 '/r' e2" := (BinOp OpDivReal e1 e2) (at level 55, right associativity) : clerical_scope.

Notation "e1 '<z' e2" := (BinOp OpLtInt e1 e2) (at level 70, right associativity) : clerical_scope.

Notation "e1 '>z' e2" := (BinOp OpGtInt e1 e2) (at level 70, right associativity) : clerical_scope.

Notation "e1 '<r' e2" := (BinOp OpLtReal e1 e2) (at level 70, right associativity) : clerical_scope.

Notation "e1 '>r' e2" := (BinOp OpGtReal e1 e2) (at level 70, right associativity) : clerical_scope.

Notation "e1 'AND' e2" := (BinOp OpAnd e1 e2) (at level 75, right associativity) : clerical_scope.

Notation "e1 'Or' e2" := (BinOp OpAnd e1 e2) (at level 75, right associativity) : clerical_scope.

Notation "'ABS' e" := (UniOp OpABS e) (at level 30) : clerical_scope.

Notation "'Prec' e" := (UniOp OpPrec e) (at level 30) : clerical_scope.

Notation "'NOT' e" := (UniOp OpNot e) (at level 30) : clerical_scope.

Notation "'0-z' e" := (UniOp OpNegInt e) (at level 30) : clerical_scope.

Notation "'0-r' e" := (UniOp OpNegReal e) (at level 30) : clerical_scope.

Notation "'SKIP'" := (Skip) : clerical_scope.

Notation "c1 ;; c2" := (Sequence c1 c2) (at level 80, right associativity) : clerical_scope.

Notation "'MCASE' b1 '==>' c1 'OR' b2 '==>' c2 'END'" := (Case b1 c1 b2 c2) (at level 89)  : clerical_scope.

Notation "'WHEN' b 'THEN' c1 'ELSE' c2 'END'" :=
  (Newvar b (Case (Var 0) c1 (UniOp OpNot (Var 0)) c2)) (at level 85) : clerical_scope.

Notation "'WHILE' b 'DO' c 'END'" := (While b c) (at level 85) : clerical_scope.

Notation "'NEWVAR' s ':=' e 'IN' c" := (Newvar s e c) (at level 85) : clerical_scope.

Notation "'SET' s ':=' e" := (Assign s e) (at level 78) : clerical_scope.

Open Scope clerical_scope.

Delimit Scope clerical_scope with clerical.
