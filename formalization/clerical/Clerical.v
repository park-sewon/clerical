(* An initial attempt at defining a language for real number comptuations, based on
   converstations with Sewon Park and Alex Simspon *)

(* This version is just a simple command language, to get us started. *)

Require Import ZArith.
Require Import List.
Require Import String.
(*Require Import Delay.*)

(* Datatypes *)
Inductive datatype :=
  | DBoolean
  | DInteger
  | DReal.

(* Primitive oeprators  | todo: separate the operators by their operands' types? *)
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



(* Context *)
Inductive variables := variable_cons : string -> datatype -> bool -> variables. 

Definition context := list variables.
Definition empty_context : context := nil.

Definition add_rw (ΓΔ : context) (s : string) (τ : datatype) := cons (variable_cons s τ true) ΓΔ.
    
Inductive in_context : context -> string -> Type :=
| triv : forall Γ s v, in_context Γ s -> in_context (cons v Γ) s
| base : forall Γ s (v : variables), (let (a,b,c) := v in s =  a) -> in_context (cons v Γ) s.

Inductive in_context_t : context -> string -> datatype -> Type :=
| triv_t : forall Γ s v τ, in_context_t Γ s τ -> in_context_t (cons v Γ) s τ
| base_t : forall Γ s τ (v : variables), (let (a,b,c) := v in s = a) ->  (let (a,b,c) := v in b = τ) -> in_context_t (cons v Γ) s τ.

Inductive in_context_trw : context -> string -> datatype -> bool -> Type :=
| triv_trw :
    forall Γ s v τ b,
      in_context_trw Γ s τ b -> in_context_trw (cons v Γ) s τ b
| base_trw :
    forall Γ s τ t (v : variables),
      (let (a,b,c) := v in s = a) ->  (let (a,b,c) := v in b = τ) -> (let (a,b,c) := v in c = t) -> in_context_trw (cons v Γ) s τ t.

Fixpoint readonly (Γ : context) : context :=
  match Γ with
  | nil => nil
  | cons v Γ' => let (a,b,c) := v in
                 cons (variable_cons a b false) (readonly Γ')
  end.

Fixpoint is_in_context (c : context) (s : string) : bool :=
  match c with
  | nil => false
  | cons a b => let (a',b',c') := a in
                if (string_dec a' s) then true else is_in_context b s
  end.

Fixpoint locate (ΓΔ : context) (s : string) : option variables :=
  match ΓΔ with
  | nil => None
  | cons a b => let (a',b',c') := a in
                if (string_dec a' s) then Some a else locate b s
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
  | RData : datatype -> result_type
  | RCommand.

Fixpoint rev_type (τ : option result_type) : option datatype :=
  match τ with
  | Some (RData τ) => Some τ
  | _ => None
  end.

Fixpoint same_result_type (a b : result_type) : bool :=
  match a, b with
  | RData DBoolean, RData DBoolean => true
  | RData DInteger, RData DInteger => true
  | RData DReal, RData DReal => true
  | RCommand, RCommand => true
  | _, _ => false
  end.

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
