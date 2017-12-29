(* An initial attempt at defining a language for real number comptuations, based on
   converstations with Sewon Park and Alex Simspon *)

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


(* Primitive Operators *)
Inductive unary_op :=
  | OpNot | OpNegInt | OpNegReal | OpABS | OpPrec.

Inductive binary_op :=
  | OpPlusInt | OpMultInt | OpSubInt
  | OpPlusReal | OpMultReal | OpSubReal | OpDivReal
  | OpLtInt | OpEqInt | OpGtInt | OpLeInt | OpGeInt 
  | OpLtReal | OpGtReal
  | OpAnd | OpOr.


(* Variable and Context *)
Inductive variable := Id : string -> variable.
Definition typed_variable : Type := (variable * datatype).

Definition context : Type := list (typed_variable * bool).
Definition empty_context : context := nil.

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

Notation "'REAL' r" := (Integer r) (at level 30) : clerical_scope.

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

Notation "'WHILE' b 'DO' c 'END'" := (While b c) (at level 85) : clerical_scope.

Notation "'NEWVAR' s ':=' e 'IN' c" := (Newvar s e c) (at level 85) : clerical_scope.

Notation "'SET' s ':=' e" := (Assign s e) (at level 78) : clerical_scope.

Open Scope clerical_scope.

Delimit Scope clerical_scope with clerical.
