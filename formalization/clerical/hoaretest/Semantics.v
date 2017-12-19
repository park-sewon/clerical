Require Import ZArith.
Require Coq.Program.Equality.

Require Import Clerical.
Require Import Typing.

(* temp for datatype real *)

Definition sem_datatype (τ : datatype) : Set :=
  match τ with
  | DUnit => unit
  | DBoolean => bool
  | DInteger => Z
  | DReal => Z
  end.

Definition sem_result_type (ρ : result_type) :=
  match ρ with
  | RData τ => sem_datatype τ
  end.

(* sem of context should be a list of (sem) typed variables *)
Definition sorted_variable : Type := variable * Set.
Definition context_meaning : Type := list sorted_variable * list sorted_variable.

Fixpoint sem_context_aux (Γ : list typed_variable) :  list sorted_variable :=
  match Γ with
  | nil => nil
  | cons v Γ => cons (fst v, sem_datatype (snd v)) (sem_context_aux Γ)
  end.

Definition sem_context (Γ : context) : context_meaning :=
  (sem_context_aux (fst Γ), sem_context_aux (snd Γ)).
  
             

(* The monad of computations. *)

(* The partiality monad *)
Structure partial (X : Type) :=
  { p_value :> X -> Prop ;
    p_single : forall x y, p_value x -> p_value y -> x = y
  }.

Arguments p_value {X} _.
Arguments p_single {X} _ _ _ _.

(* The unit. *)
Definition total {X : Type} (x : X) : partial X.
Proof.
  exists (fun y => x = y).
  intros y z [] [].
  reflexivity.
Defined.

(* Binding for partiality monad. *)
Definition bind_partial {X Y : Type} (u : partial X) (f : X -> partial Y) : partial Y.
Proof.
  exists (fun y => exists x, u x /\ f x y).
  intros y z [x' [ux' fx'y]] [x'' [ux'' fx''z]].
  destruct (p_single u x' x'' ux' ux'').
  exact (p_single (f x') y z fx'y fx''z).
Defined.

(* The bottom. *)
Definition bottom (X : Type) : partial X.
Proof.
  exists (fun _ => False).
  now tauto.
Defined.

(* The total elements. *)
Definition is_total {X : Type} (u : partial X) := exists x, u x.

(* The monad for computations. *)
Definition M (X : Type) := partial X -> Prop.

Definition defined {X : Type} (v : M X) := exists x, v x.

(* The unit of M. *)
Definition singleton {X : Type} (x : X) : M X :=
  fun (u : partial X) => u x /\ forall y, u y -> x = y.

(* Non-termination. *)
Definition bottom_M {X : Type} : M X := fun (u : partial X) => forall x, ~ u x.

(* Bind for M *)
Definition bind_M {X Y : Type} (S : M X) (f : X -> M Y) : M Y :=
  fun (v : partial Y) => exists u, S u /\ forall x, u x -> f x v.

(* Undefined semantics *)
Definition undefined_M {X : Type} : M X := fun _ => False.

(* Check a computation with a boolean. *)
Definition check {X : Type} : M bool -> M X -> M X :=
  fun u v =>
    bind_M u (fun b => if b then v else bottom_M).

(* Join two computation. Note that this is not just union! *)
Definition join {X : Type} (u : M X) (v : M X) : M X :=
  fun x : partial X => defined u /\ defined v /\ (u x \/ v x).

(* [M X] has an order. *)
Definition le_M {X : Type} (S : M X) (T : M X) : Prop :=
  (forall u, S u -> is_total u -> T u) /\
  (forall v, T v -> exists u, S u /\ (forall x, u x -> v x)).

Lemma le_M_undefined_l {X : Type} (S : M X) :
  le_M undefined_M S <-> forall u, ~ S u.
Proof.
  split.
  - intros [L1 L2] u Su.
    destruct (L2 u Su) as [? [[] ?]].
  - intros H.
    split.
    + intros _ [].
    + intros v Sv.
      elim (H v Sv).
Qed.

Lemma le_M_undefined_r {X : Type} (S : M X) :
  le_M S undefined_M <-> forall u, S u -> ~ is_total u.
Proof.
  split.
  - intros [L1 L2] u Su [x ux].
    apply (L1 u Su).
    now exists x.
  - intro H.
    split.
    + intros u Su [x ux].
      apply (H u Su).
      now exists x.
    + intros v [].
Qed.

Lemma le_M_bottom_undefined {X : Type} : le_M (@bottom_M X) (@undefined_M X).
Proof.
  split.
  - intros u bu [x ux].
    now apply (bu x).
  - intros v [].
Qed.

(* [M X] is an ω-CPO. Here we just construct the (candidate for) sumpremum
   impredicatively. This is probably wrong. *)
Definition sup {X : Type} (c : nat -> M X) : M X :=
  fun (v : partial X) =>
    (forall n, defined (c n)) /\ (exists n, forall m, n <= m -> c n v).

Definition is_upper {X : Type} (c : nat -> M X) (v : M X) :=
  forall n, le_M (c n) v.

Definition is_sup {X : Type} (c : nat -> M X) (u : M X) :=
  is_upper c u /\
  forall v, is_upper c v -> le_M u v.

(* Cheap trick to get the a large inductive proof organized. Eventually
   we want to remove this. *)
Axiom magic_axiom : forall A : Type, A. (* every type is inhabited, use with care *)
Ltac unfinished := now apply magic_axiom.

(* The meaning of a well-typed program in relational form. 
Fixpoint sem_comp (Γ : context) (c : comp) (ρ : result_type) (D : has_type Γ c ρ):
  sem_context Γ -> M (sem_context_rw Γ * sem_result_type ρ).

Proof.
  intro γ.
  induction D.

  (* has_type_Var_0 *)
  {
    unfinished.
  }

  (* has_type_True *)
  {
    apply singleton.
    exact (fst γ, true).
  }

  (* has_type_False *)
  {
    apply singleton.
    exact (fst γ, false).
  }

  (* has_type_Integer *)
  {
    apply singleton.
    exact (fst γ, k).
  }

  (* has_type_Skip *)
  {
    apply singleton.
    exact (fst γ, tt).
  }

  (* has_type_Sequence *)
  {
    simple refine (bind_M _ IHD2).
    apply (bind_M (IHD1 γ)).
    intros [γ1 []].
    apply singleton.
    exact (γ1, snd γ).
  }

  (* has_type_while *)
  {
    unfinished.
  }

  (* has_type_Case *)
  {
    apply join.
    - apply check.
      + apply (bind_M (IHD1 (tt, γ))).
        intros [_ b].
        exact (singleton b).
      + apply (bind_M (IHD2 γ)).
        apply singleton.
    - apply check.
      + apply (bind_M (IHD3 (tt, γ))).
        intros [_ b].
        exact (singleton b).
      + apply (bind_M (IHD4 γ)).
        apply singleton.
  }

  (* has_type_newvar *)
  {
    apply (bind_M (IHD1 (tt, γ))).
    intros [[] x].
    apply (bind_M (IHD2 ((x, fst γ), snd γ))).
    intros [[_ γ1] y].
    apply singleton.
    exact (γ1, y).
  }

  (* has_type_assign *)
  {
    apply (bind_M (sem_comp _ _ _ D (tt, γ))).
    intros [[] val_e].
    apply singleton.
    simple refine (_, tt).
    apply (update k val_e (fst γ) i).
  }

Defined.
*)