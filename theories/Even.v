Require Import List Bool Arith Lia.
Import ListNotations.

Set Implicit Arguments.
Section Even.
Variable A : Type.
Implicit Type w : list A.

Inductive Even: list A -> Prop :=
| Even_nil: Even nil
| Even_cons_ends: forall w, Even w -> forall a b, Even (a::w++[b]).

Lemma length_cons_ends (x y: A) (l: list A):
  length (x::l++[y]) = S (S (length l)).
Proof. cbn. rewrite last_length. reflexivity. Qed.

Lemma exists_first_last w:
  1 < length w -> exists a b w', w = a::w'++[b].
Proof.
  intro H. destruct w as [|a w].
  - apply Nat.le_0_r in H. discriminate H.
  - exists a. assert (w <> []) as H0.
    + cbn in H. apply Nat.succ_lt_mono, Nat.neq_0_lt_0 in H.
      intro E. apply H. apply length_zero_iff_nil. assumption.
    + apply exists_last in H0 as [w' [b ->]].
      exists b, w'. reflexivity.
Qed.

Theorem Even_length_Even w:
  Nat.Even (length w) <-> Even w.
Proof.
  split; intro H.
  - destruct H as [n H].
    revert H. revert w. induction n; intros w H.
    + apply length_zero_iff_nil in H as ->. constructor.
    + assert (1 < length w) as Hw by lia.
      apply exists_first_last in Hw as [a [b [w' ->]]]. constructor.
      apply IHn. rewrite length_cons_ends in H. lia.
  - induction H.
    + exists 0. reflexivity.
    + rewrite length_cons_ends. apply Nat.Even_succ_succ. assumption.
Qed.

Lemma Even_app w1 w2:
  Even w1 -> Even w2 -> Even (w1 ++ w2).
Proof.
  intros H1 H2. apply Even_length_Even.
  rewrite app_length. apply Nat.Even_Even_add.
  all: apply Even_length_Even; assumption.
Qed.
End Even.

Notation "'#true' w" := (count_occ bool_dec w true) (at level 10).
Notation "'#false' w" := (count_occ bool_dec w false) (at level 10).

Lemma count_true_false_length w:
  #true w + #false w = length w.
Proof.
  induction w.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma count_eq_even w:
  #false w = #true w -> Even w.
Proof.
intro H. apply Even_length_Even.
rewrite <- count_true_false_length.
rewrite H. exists (#true w). lia.
Qed.