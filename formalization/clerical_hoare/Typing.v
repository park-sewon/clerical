(* The file contians
   1. Type of operands and result of primitive operators
   2. Type judgement rules of Clerical computations 
 *)
Require Import Aux0.
Require Import Clerical.
Require Import Aux_Clerical.
Open Scope clerical_scope.


(* Type contract of primitive operators  *)
Definition bin_type (b : binary_op) (t : three) : datatype :=
  match b with  
  | OpPlusInt  => match t with | one => DInteger | two => DInteger | three => DInteger end 
  | OpMultInt  => match t with | one => DInteger | two => DInteger | three => DInteger end 
  | OpSubInt   => match t with | one => DInteger | two => DInteger | three => DInteger end 
  | OpPlusReal => match t with | one => DReal | two => DReal | three => DReal end 
  | OpMultReal => match t with | one => DReal | two => DReal | three => DReal end 
  | OpSubReal  => match t with | one => DReal | two => DReal | three => DReal end 
  | OpDivReal  => match t with | one => DReal | two => DReal | three => DReal end 
  | OpLtInt    => match t with | one => DInteger | two => DInteger | three => DBoolean end 
  | OpEqInt    => match t with | one => DInteger | two => DInteger | three => DBoolean end 
  | OpGtInt    => match t with | one => DInteger | two => DInteger | three => DBoolean end 
  | OpLeInt    => match t with | one => DInteger | two => DInteger | three => DBoolean end 
  | OpGeInt    => match t with | one => DInteger | two => DInteger | three => DBoolean end 
  | OpLtReal   => match t with | one => DReal | two => DReal | three => DBoolean end 
  | OpGtReal   => match t with | one => DReal | two => DReal | three => DBoolean end 
  | OpAnd      => match t with | one => DBoolean | two => DBoolean | three => DBoolean end
  | OpOr       => match t with | one => DBoolean | two => DBoolean | three => DBoolean end
  end.

Fixpoint binary_op_type (op : binary_op) : option datatype -> option datatype -> option datatype :=
  match op with
  | OpPlusInt => fun τ₁ τ₂ => match τ₁, τ₂ with
                              | Some DInteger, Some DInteger => Some DInteger | _, _ => None
                              end
  | OpMultInt => fun τ₁ τ₂ => match τ₁, τ₂ with
                              | Some DInteger, Some DInteger => Some DInteger
                              | _, _ => None
                              end
  | OpSubInt => fun τ₁ τ₂ => match τ₁, τ₂ with
                             | Some DInteger, Some DInteger => Some DInteger
                             | _, _ => None
                             end
  | OpPlusReal => fun τ₁ τ₂ => match τ₁, τ₂ with
                               | Some DReal , Some DReal => Some DReal
                               | _, _ => None
                               end
  | OpMultReal => fun τ₁ τ₂ => match τ₁, τ₂ with
                               | Some DReal, Some DReal => Some DReal
                               | _, _ => None
                               end
  | OpSubReal => fun τ₁ τ₂ => match τ₁, τ₂ with
                              | Some DReal, Some DReal => Some DReal
                              | _, _ => None
                              end
  | OpDivReal => fun τ₁ τ₂ => match τ₁, τ₂ with
                              | Some DReal, Some DReal => Some DReal
                              | _, _ => None
                              end
  | OpLtInt => fun τ₁ τ₂ => match τ₁, τ₂ with
                            | Some DInteger, Some DInteger => Some DBoolean | _, _ => None
                            end
  | OpEqInt => fun τ₁ τ₂ => match τ₁, τ₂ with
                            | Some DInteger, Some DInteger => Some DBoolean | _, _ => None
                            end
  | OpGtInt => fun τ₁ τ₂ => match τ₁, τ₂ with
                            | Some DInteger, Some DInteger => Some DBoolean | _, _ => None
                            end
  | OpLeInt => fun τ₁ τ₂ => match τ₁, τ₂ with
                            | Some DInteger, Some DInteger => Some DBoolean | _, _ => None
                            end
  | OpGeInt  => fun τ₁ τ₂ => match τ₁, τ₂ with
                             | Some DInteger, Some DInteger => Some DBoolean | _, _ => None
                             end
  | OpLtReal => fun τ₁ τ₂ => match τ₁, τ₂ with
                             | Some DReal, Some DReal => Some DBoolean | _, _ => None
                             end
  | OpGtReal => fun τ₁ τ₂ => match τ₁, τ₂ with
                             | Some DReal, Some DReal => Some DBoolean | _, _ => None
                             end
  | OpAnd => fun τ₁ τ₂ => match τ₁, τ₂ with
                          | Some DBoolean, Some DBoolean => Some DBoolean | _, _ => None
                          end
  | OpOr => fun τ₁ τ₂ => match τ₁, τ₂ with
                         | Some DBoolean, Some DBoolean  => Some DBoolean | _, _ => None
                         end
  end.

Fixpoint unary_op_type (op : unary_op) :option datatype -> option datatype :=
  match op with
  | OpNot => fun τ => match τ with | Some DBoolean => Some DBoolean | _ => None  end
  | OpNegInt => fun τ => match τ with | Some DInteger => Some DInteger | _ => None  end
  | OpNegReal => fun τ => match τ with | Some DReal => Some DReal | _ => None  end
  | OpABS => fun τ => match τ with | Some DReal => Some DReal | _ => None end
  | OpPrec => fun τ => match τ with | Some DInteger => Some DReal | _ => None end
  end.

Definition uni_type (u : unary_op) (b : bool) : datatype :=
  match u with
  | OpNot => match b with | true => DBoolean | false => DBoolean end 
  | OpNegInt => match b with | true => DInteger | false => DInteger end 
  | OpNegReal => match b with | true => DReal | false => DReal end 
  | OpABS => match b with | true => DReal | false => DReal end
  | OpPrec => match b with | true => DReal | false => DInteger end
  end.




Inductive has_type : context -> comp -> datatype -> Type :=
  | has_type_Var :
    forall Γ s τ,
      ctx_mem_tv Γ (Id s, τ) -> has_type Γ (VAR s) τ

  | has_type_True :
      forall Γ,
        has_type Γ TRUE DBoolean

  | has_type_False :
      forall Γ,
        has_type Γ FALSE DBoolean

  | has_type_Integer :
      forall Γ k,
        has_type Γ (INT k) DInteger

  | has_type_Real :
      forall Γ r,
        has_type Γ (Real r) DReal
                 
  | has_type_Skip :
      forall Γ,
        has_type Γ SKIP DUnit

  | has_type_Sequence :
      forall Γ c1 c2 ρ,
        has_type Γ c1 DUnit ->
        has_type Γ c2 ρ ->
        has_type Γ (c1 ;; c2)  ρ

  | has_type_while :
      forall Γ b c,
        has_type (readonly Γ) b DBoolean ->
        has_type Γ c DUnit ->
        has_type Γ (WHILE b DO c END) DUnit

  | has_type_Case :
      forall Γ b1 c1 b2 c2 ρ,
        has_type (readonly Γ) b1 DBoolean ->
        has_type Γ c1 ρ ->
        has_type (readonly Γ) b2 DBoolean ->
        has_type Γ c2 ρ ->
        has_type Γ (MCASE b1 ==> c1 OR b2 ==> c2 END) ρ

  | has_type_newvar :
      forall Γ s ρ τ e c,
        (ctx_mem_str Γ s -> False) ->
        has_type (readonly Γ) e τ ->
        has_type (add_rw Γ s τ) c ρ ->
        has_type Γ (NEWVAR s := e IN c) ρ

  | has_type_assign :
      forall Γ s τ e,
        ctx_mem_tv_rw Γ (Id s, τ) ->
        has_type (readonly Γ) e τ ->
        has_type Γ (SET s := e) DUnit

  | has_type_lim :
      forall Γ s e,
        (ctx_mem_str Γ s -> False) ->
        has_type (readonly (add_ro Γ s DInteger)) e DReal ->
        has_type Γ (Lim s e) DReal
.


(* Type checker: given a context it judeges type. if the given computation is not well-typed, it
   leads to None. *)
Fixpoint judge_type (Γ : context) (c : comp) : option datatype :=
  match c with
  | Var s =>
    match ctx_locate_str_fun Γ s with
    | None => None
    | Some v => Some (type_v (fst v))
    end
               
  | Boolean b => Some DBoolean
  | Integer z => Some DInteger
  | Real r => Some DReal
  | BinOp op a b =>
    let τ :=  binary_op_type op ((judge_type (readonly Γ) a))
                             ((judge_type (readonly Γ) b)) in
    match τ with
    | Some τ => Some  τ
    | None => None
    end
      
  | UniOp op a =>
    let τ := (unary_op_type op ((judge_type (readonly Γ) a))) in
    match τ with
    | Some τ => Some  τ
    | None => None
    end

  | Skip => Some DUnit

  | Sequence c1 c2 =>
    let τ := (judge_type Γ c1) in
    match τ with
    | Some τ => match τ with
                | DUnit => judge_type Γ c2
                | _ => None
                end
    | _ => None
    end

  | Case b1 c1 b2 c2 =>
    let Γ' := readonly Γ in
    let τ₁ := judge_type Γ' b1 in
    let τ₂ := judge_type Γ' b2 in
    match τ₁  with
    | Some DBoolean =>
      match τ₂ with
      | Some DBoolean => let ρ₁ := judge_type Γ c1 in
                         let ρ₂ := judge_type Γ c2 in
                         match ρ₁, ρ₂ with
                         | Some ρ₁', Some ρ₂' => if (eq_type ρ₁' ρ₂') then ρ₁ else None
                         | _, _ => None
                         end
      | _ => None
      end
        
    | _ => None
    end

  | While b c =>
    let τ := judge_type (readonly Γ) b in
    match τ with
    | Some DBoolean => let  ρ := judge_type Γ c in
                       match ρ with
                       | Some Rcommand => Some Rcommand
                       | _ => None
                       end
    | _ => None
    end
      
  | Newvar s e c =>
    if (ctx_mem_str_fun Γ s)
    then None
    else
      let τ := judge_type (readonly Γ) e in
      match τ with
      | Some τ => judge_type (add_rw Γ s τ) c
      | _ => None
      end

  | Assign s e =>
    let v := ctx_locate_str_fun Γ s in
    match v with
    | Some v => let c := (snd v) in
                if c then (
                    let ρ := judge_type (readonly Γ) e in
                    match ρ with
                    | Some ρ => if (eq_type ρ (type_v (fst v))) then Some DUnit else None
                    | _ => None
                    end)
                else None
    | _ => None
    end

  | Lim s e =>
    let v := ctx_locate_str_fun Γ s in
    match v with
    | None => let Γ := (readonly (add_ro Γ s DInteger)) in
              let ρ := judge_type Γ e in
              match ρ with
              | Some DReal => Some DReal
              | _ => None
              end
    | _ => None
    end
  end.

(* prove that the type judgement function is correct upto the inductive definition has_type *)
Theorem Type_judgement_is_correct : forall Γ c τ, has_type Γ c τ -> judge_type Γ c = Some τ.
Proof.
Admitted.


