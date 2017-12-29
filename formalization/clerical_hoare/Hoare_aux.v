Require Import Clerical.
Require Import Bool.
Require Import List.

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


Fixpoint ctx_mem_tv_fun (Γ : context) (v : typed_variable) : bool :=
  match Γ with
  | (w, b) :: Γ => if (eq_tv_tv v w) then true else ctx_mem_tv_fun Γ v
  | _ => false
  end.

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

Require Import Coq.Reals.Reals.
Require Import ZArith.
Require Import Coq.ZArith.Zorder.
Require Import Coq.PArith.Pnat.
Require Import Coq.NArith.Nnat.
Open Scope R_scope.


Fixpoint prec_embedding_nat (n:nat) : R :=
    match n with
    | O => 1
    | S n => 2 * prec_embedding_nat n
    end.

Definition prec_embedding (z:Z) : R :=
  match z with
  | 0%Z => 1
  | Zpos n => prec_embedding_nat (Pos.to_nat n)
  | Zneg n => 1 */ (prec_embedding_nat (Pos.to_nat n))
  end.

