Require Import Aux0.
Require Import Clerical.

Require Import String.
Require Import Bool.
Open Scope clerical_scope.


(* Variable and Context *)
Inductive variable := Id : string -> variable.
Definition typed_variable : Type := (variable * datatype).

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


Structure ctx := { ctx_rw : list typed_variable ; ctx_ro : list typed_variable }.
Definition empty_ctx : ctx := {| ctx_rw := nil ; ctx_ro := nil |}.

Definition add_rw_ctx (Γ : ctx) (v : typed_variable) : ctx := {| ctx_rw := v :: (ctx_rw Γ); ctx_ro := ctx_ro Γ |}.
Definition add_ro_ctx (Γ : ctx) (v : typed_variable) : ctx := {| ctx_rw := ctx_rw Γ; ctx_ro :=  v :: ctx_ro Γ |}.

Definition add_rw (Γ : ctx) (s : string) (τ : datatype) : ctx := {| ctx_rw := (Id s, τ) :: (ctx_rw Γ); ctx_ro := ctx_ro Γ |}.
Definition add_ro (Γ : ctx) (s : string) (τ : datatype) : ctx := {| ctx_rw := ctx_rw Γ; ctx_ro :=  (Id s, τ) :: ctx_ro Γ |}.

Inductive ctx_mem_str_rw : ctx -> string -> Type :=
| triv_rw_rw : forall Γ s v, ctx_mem_str_rw Γ s -> ctx_mem_str_rw (add_rw_ctx Γ v) s
| triv_rw_ro : forall Γ s v, ctx_mem_str_rw Γ s -> ctx_mem_str_rw (add_ro_ctx Γ v) s
| base_rw : forall Γ s v, eq_tv_str v s = true -> ctx_mem_str_rw (add_rw_ctx Γ v) s.

Inductive ctx_mem_str_ro : ctx -> string -> Type :=
| triv_ro_rw : forall Γ s v, ctx_mem_str_ro Γ s -> ctx_mem_str_ro (add_rw_ctx Γ v) s
| triv_ro_ro : forall Γ s v, ctx_mem_str_ro Γ s -> ctx_mem_str_ro (add_ro_ctx Γ v) s
| base_ro : forall Γ s v, eq_tv_str v s = true -> ctx_mem_str_ro (add_ro_ctx Γ v) s.

Inductive ctx_mem_str : ctx -> string -> Type :=
| at_rw : forall Γ s, ctx_mem_str_rw Γ s -> ctx_mem_str Γ s
| at_ro : forall Γ s, ctx_mem_str_ro Γ s -> ctx_mem_str Γ s.

Definition readonly (Γ : ctx) : ctx := {| ctx_rw := ctx_rw Γ ; ctx_ro := ctx_rw Γ ++ ctx_ro Γ |}. 

Inductive ctx_mem_tv_rw : ctx -> typed_variable -> Type :=
| triv_t_rw_rw : forall Γ v w, ctx_mem_tv_rw Γ v -> ctx_mem_tv_rw (add_rw_ctx Γ w) v
| triv_t_rw_ro : forall Γ v w, ctx_mem_tv_rw Γ v -> ctx_mem_tv_rw (add_ro_ctx Γ w) v
| base_t_rw : forall Γ v w, eq_tv_tv v w = true -> ctx_mem_tv_rw (add_rw_ctx Γ w) v.

Inductive ctx_mem_tv_ro : ctx -> typed_variable -> Type :=
| triv_t_ro_rw : forall Γ v w, ctx_mem_tv_ro Γ v -> ctx_mem_tv_ro (add_rw_ctx Γ w) v
| triv_t_ro_ro : forall Γ v w, ctx_mem_tv_ro Γ v -> ctx_mem_tv_ro (add_ro_ctx Γ w) v
| base_t_ro : forall Γ v w, eq_tv_tv v w = true -> ctx_mem_tv_ro (add_ro_ctx Γ w) v.

Inductive ctx_mem_tv : ctx -> typed_variable -> Type :=
| at_rw_t : forall Γ v, ctx_mem_tv_rw Γ v -> ctx_mem_tv Γ v
| at_ro_t : forall Γ v, ctx_mem_tv_ro Γ v -> ctx_mem_tv Γ v.

Require Import List.
Fixpoint string_mem (Γ : list typed_variable) (s : string) : bool :=
  match Γ with
  | v :: Γ' => if eq_tv_str v s then true else string_mem Γ' s
  | nil => false
  end.
Fixpoint tv_mem (Γ : list typed_variable) (w : typed_variable) : bool :=
  match Γ with
  | v :: Γ' => if eq_tv_tv v w then true else tv_mem Γ' w
  | nil => false
  end.

Fixpoint cctx_mem_fun (Γ : list typed_variable) (v : typed_variable) : bool :=
  match Γ with
  | w :: Γ => if eq_tv_tv v w then true else cctx_mem_fun Γ v
  | _ => false
  end.


Definition ctx_mem_str_fun (Γ : ctx) (s : string) : bool := string_mem (ctx_rw Γ ++ ctx_ro Γ) s.
Definition ctx_mem_str_fun_rw (Γ : ctx) (s : string) : bool := string_mem (ctx_rw Γ) s.
Definition ctx_mem_str_fun_ro (Γ : ctx) (s : string) : bool := string_mem (ctx_ro Γ) s.
Fixpoint string_loc (Γ : list typed_variable) (s : string) : option typed_variable :=
  match Γ with
  | v :: Γ' => if eq_tv_str v s then Some v else string_loc Γ' s
  | nil => None
  end.

Definition ctx_locate_str_fun (Γ : ctx) (s : string) : option (typed_variable * bool) :=
  match string_loc (ctx_rw Γ) s with
  | Some v => Some (v, true)
  | _ => match string_loc (ctx_ro Γ) s with
         | Some v => Some (v, false)
         | _ => None
         end
  end.

  
  
Definition ctx_mem_tv_rw_fun  (Γ : ctx) (v : typed_variable) : bool := cctx_mem_fun (ctx_rw Γ) v.
Definition ctx_mem_tv_fun (Γ : ctx) (v : typed_variable) : bool := if cctx_mem_fun (ctx_rw Γ) v then true else cctx_mem_fun (ctx_ro Γ) v.



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




Inductive has_type : ctx -> comp -> datatype -> Type :=
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
Fixpoint judge_type (Γ : ctx) (c : comp) : option datatype :=
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



