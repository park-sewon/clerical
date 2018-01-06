Require Import Aux0.
Require Import Clerical.
Require Import Aux_Clerical.
Require Import Typing.
Require Import Semantics.
Require Import Assertions.
Require Import ProofRules.

Print eq_ind.

Fixpoint wp {Γ : context} {c : comp} {τ : datatype} (h : has_type Γ c τ) (p : assertion (ctx_collapse Γ) τ) : assertion (ctx_collapse Γ) DUnit :=
  match c with
  | Skip => p 

  | Var s => fun _ δ => True
                            
  | Boolean b => fun _ δ => True
                                
  | Integer z => fun _ δ => True
                                
  | Real r => fun _ δ => True
                             
  | BinOp b e1 e2 => fun _ δ => True
                              
  | UniOp u e => fun _ δ => True
                              
  | Sequence c1 c2 => fun _ δ => True
                                 
  | Case e1 c1 e2 c2 => fun _ δ => True

  | While e c => fun _ δ => True

  | Newvar s e c => fun _ δ => True
                               
  | Assign s e => fun _ δ => True
                               
  | Lim s e => fun _ δ => True
  end.



                                                                                                      

Inductive wp (Γ : context) (c : comp) (τ : datatype) : has_type Γ c τ -> assertion (ctx_collapse Γ) τ -> assertion (ctx_collapse Γ) DUnit :=
  
| wp_Skip : forall h p, wp Γ SKIP DUnit h (p) (p) 

| wp_Var : forall h p, wp Γ SKIP DUnit h (p) (p) 

| wp_Boolean : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_Integer : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_Real : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_BinOp : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_UniOp : forall h p, wp Γ SKIP DUnit h (p) (p)                             
                           
| wp_Sequence : forall h p, wp Γ SKIP DUnit h (p) (p)   

| wp_Case : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_While : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_Newvar : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_Assign : forall h p, wp Γ SKIP DUnit h (p) (p)  

| wp_Lim : forall h p, wp Γ SKIP DUnit h (p) (p).

