Require Import Clerical.
Require Import Bool.
Require Import List.

Lemma eq_variable_has_same_type : forall v w, eq_name_type_v v w = true -> snd v = snd w.
Proof.
  intros.
  unfold eq_name_type_v in H.
  destruct (eq_name_v v w).
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


Fixpoint tv_mem_aux (Γ : list typed_variable) (v : typed_variable) : bool :=
  match Γ with
  | w :: Γ => if (eq_name_type_v v w) then true else tv_mem_aux Γ v
  | _ => false
  end.

Definition tv_mem (Γ : context) (v : typed_variable) : bool :=
  if (tv_mem_aux (fst Γ) v) then true else if (tv_mem_aux (snd Γ) v) then true else false.

Lemma typed_mem_dec : forall Γ v, {tv_mem Γ v = true} + {tv_mem Γ v = false}.
Proof.
  intros Γ v.
  pose proof (bool_dec (tv_mem Γ v) true).
  destruct H.
  left; trivial.
  pose proof (not_true_is_false (tv_mem Γ v) n).
  right; trivial.
Qed.


Lemma variable_name_type_dec : forall v w, {eq_name_type_v v w = true} + {eq_name_type_v v w = false}.
Proof.
  intros.
  pose proof (bool_dec (eq_name_type_v v w) true).
  destruct H.
  left; trivial.
  pose proof (not_true_is_false (eq_name_type_v v w) n).
  right; trivial.
Qed.


Definition origin_type (τ : result_type) : datatype := match τ with RData τ => τ end.

