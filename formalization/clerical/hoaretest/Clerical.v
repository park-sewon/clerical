(* An initial attempt at defining a language for real number comptuations, based on
   converstations with Sewon Park and Alex Simspon *)

(* This version is just a simple command language, to get us started. *)

Require Import ZArith.
Require Import List.
Require Import String.
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
  | OpNot | OpNegInt | OpNegReal.

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
  end.



(* Variable and Context *)
Inductive variable := Id : string -> variable.


(* Context
   Note: 1) it would be nice if, like a set, the context is represented as a quotient type *)
Definition typed_variable : Type := (variable * datatype).

Definition context : Type := (list typed_variable * list typed_variable).
             
Definition name_v (v : typed_variable) : string := let v := fst v in match v with Id s => s end.
Definition type_v (v : typed_variable) : datatype := snd v.


Definition eq_name_v (v₁ v₂ : typed_variable) : bool :=
  let v₁ := fst v₁ in let v₂ := fst v₂ in match v₁, v₂ with Id s₁, Id s₂ => if string_dec s₁ s₂ then true else false end.

Definition eq_name_v_s (v₁ : typed_variable) (s : string) : bool :=
  let v₁ := fst v₁ in  match v₁ with Id s₁ => if string_dec s₁ s then true else false end.

Definition eq_name_type_v (v₁ v₂ : typed_variable) : bool :=
  if eq_name_v v₁ v₂ then eq_type (snd v₁) (snd v₂) else false.

Definition variable_same (v₁ v₂ : typed_variable) : bool :=
  if eq_name_v v₁ v₂ then if eq_type (type_v v₁) (type_v v₂) then true else false else false.

Definition empty_context : context := (nil, nil).

Definition add_rw (Γ : context) (s : string) (τ : datatype) := (cons (Id s, τ) (fst Γ), snd Γ).

Inductive in_context : context -> string -> Type :=
| triv₁ : forall Γ₁ Γ₂ s v, in_context (Γ₁, Γ₂) s -> in_context (cons v Γ₁, Γ₂) s
| triv₂ : forall Γ₁ Γ₂ s v, in_context (Γ₁, Γ₂) s -> in_context (Γ₁,cons v Γ₂) s
| base₁ : forall Γ₁ Γ₂ s v, eq_name_v_s v s = true -> in_context (cons v Γ₁, Γ₂) s
| base₂ : forall Γ₁ Γ₂ s v, eq_name_v_s v s = true -> in_context (Γ₁, cons v Γ₂) s.

Inductive in_context_t : context -> typed_variable -> Type :=
| triv_t₁ : forall Γ₁ Γ₂ v w, in_context_t (Γ₁, Γ₂) v -> in_context_t (cons w Γ₁, Γ₂) v
| triv_t₂ : forall Γ₁ Γ₂ v w, in_context_t (Γ₁, Γ₂) v -> in_context_t (Γ₁,cons w Γ₂) v
| base_t₁ : forall Γ₁ Γ₂ v w, eq_name_type_v v w = true -> in_context_t (cons w Γ₁, Γ₂) v
| base_t₂ : forall Γ₁ Γ₂ v w, eq_name_type_v v w = true -> in_context_t (Γ₁, cons w Γ₂) v.

Inductive not_in_context_t : context -> typed_variable -> Type :=
| n_triv_t₁ : forall Γ₁ Γ₂ v w, not_in_context_t (Γ₁, Γ₂) v -> eq_name_type_v v w = false -> not_in_context_t (cons w Γ₁, Γ₂) v
| n_triv_t₂ : forall Γ₁ Γ₂ v w, not_in_context_t (Γ₁, Γ₂) v -> eq_name_type_v v w = false -> not_in_context_t (Γ₁,cons w  Γ₂) v
| n_base_t : forall v, not_in_context_t empty_context v.


Definition in_context_trw : context -> typed_variable -> bool -> Type :=
  fun Γ v b => if b then in_context_t (fst Γ, nil) v else in_context_t (nil, snd Γ) v.

Fixpoint readonly_aux (A : Type) (Γ₁ Γ₂ : list A) : list A :=
  match Γ₁ with
  | nil => Γ₂
  | cons v Γ' => readonly_aux A Γ' (cons v Γ₂)
  end.

Definition readonly (Γ : context) : context := (nil, readonly_aux typed_variable (fst Γ) (snd Γ)).

Fixpoint is_in_context_aux  (Γ : list typed_variable) (s : string) : bool :=
  match Γ with
  | nil => false
  | cons v Γ => if (eq_name_v_s v s) then true else is_in_context_aux Γ s
  end.

Definition is_in_context (Γ : context) (s : string) : bool :=
  if (is_in_context_aux (fst Γ) s) then if (is_in_context_aux (snd Γ) s) then true else false else false.

Definition is_in_context_rw (Γ : context) (s : string) : bool :=
  if (is_in_context_aux (fst Γ) s) then true else false.

Definition is_in_context_ro (Γ : context) (s : string) : bool :=
  if (is_in_context_aux (snd Γ) s) then true else false.

Fixpoint locate_aux (Γ : list typed_variable) (s : string) : option typed_variable :=
  match Γ with
  | nil => None
  | cons v Γ => if eq_name_v_s v s then Some v else locate_aux Γ s
  end.

Definition locate (Γ : context) (s : string) : option (typed_variable * bool) :=
  let v := locate_aux (fst Γ) s in
  match v with
  | None => let v := locate_aux (snd Γ) s in
            match v with
            | None => None
            | Some v => Some (v, false)
            end
  | Some v => Some (v, true)
  end.
    
            
    

(* Computations *)
Inductive comp :=
  | Var : string -> comp
  | Boolean : bool -> comp
  | Integer : Z -> comp
  | BinOp : binary_op -> comp -> comp -> comp
  | UniOp : unary_op -> comp -> comp
  | Skip : comp
  | Sequence : comp -> comp -> comp
  | Case : comp -> comp -> comp -> comp -> comp
  | While : comp -> comp -> comp
  | Newvar : string -> comp -> comp -> comp
  | Assign : string -> comp -> comp.


(* Results of computations *)
Inductive result_type :=
  | RData : datatype -> result_type.

Fixpoint rev_type (τ : option result_type) : option datatype :=
  match τ with
  | Some (RData τ) => Some τ
  | _ => None
  end.

Fixpoint same_result_type (a b : result_type) : bool :=
  match a, b with
  | RData DUnit, RData DUnit => true
  | RData DBoolean, RData DBoolean => true
  | RData DInteger, RData DInteger => true
  | RData DReal, RData DReal => true
  | _, _ => false
  end.

Definition RCommand := RData DUnit.
Definition RBoolean := RData DBoolean.
Definition RInteger := RData DInteger.
Definition RReal := RData DReal.


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
