Require Import List Bool ZArith Permutation.
Require Import Lia.
Import ListNotations.

From BasicCombinatorics Require Import Even Binomial.

Inductive Dyck: word -> Prop :=
| Dyck_nil: Dyck nil
| Dyck_shift: forall w, Dyck w -> Dyck (true::w++[false])
| Dyck_app: forall w1, Dyck w1 -> forall w2, Dyck w2 -> Dyck (w1 ++ w2).

Lemma Dyck_count_eq w:
  Dyck w -> #false w = #true w.
Proof.
  intros D. induction D.
  - reflexivity.
  - cbn. rewrite !count_occ_app. cbn. lia.
  - rewrite !count_occ_app. congruence.
Qed.

Corollary Dyck_even w:
  Dyck w -> Even w.
Proof.
  intros D. induction D.
  - constructor.
  - constructor. assumption.
  - apply Even_app; assumption.
Qed.

Lemma div2_add_distr n m:
  Nat.Even n -> Nat.div2 (n + m) = Nat.div2 n + Nat.div2 m.
Proof.
  intros [q ->]. destruct (Nat.Even_or_Odd m) as [[p ->]|[p ->]].
  - rewrite <- Nat.mul_add_distr_l, !Nat.div2_double. reflexivity.
  - rewrite Nat.add_1_r, Nat.add_succ_r, Nat.div2_succ_double.
    rewrite <- Nat.mul_add_distr_l, Nat.div2_succ_double, Nat.div2_double.
    reflexivity.
Qed.

Lemma Dyck_Binomial w:
  Dyck w -> Binomial (Nat.div2 (length w)) w.
Proof.
  intro D. induction D.
  - constructor.
  - rewrite length_cons_ends. cbn. constructor.
    apply Binomial_false_end. assumption.
  - rewrite app_length.
    rewrite div2_add_distr by (apply Even_length_Even, Dyck_even; assumption).
    apply Binomial_app; assumption.
Qed.

Section level.

Open Scope Z.

Fixpoint level w: Z :=
match w with
| nil => 0
| true::w => (level w) + 1
| false::w => (level w) - 1
end.

Lemma level_app w1 w2:
  level (w1 ++ w2) = (level w1) + (level w2).
Proof.
  induction w1.
  - reflexivity.
  - rewrite <- app_comm_cons. destruct a; cbn; lia.
Qed.

Lemma level_count w:
   level w = Z.of_nat (#true w) - Z.of_nat (#false w).
Proof.
  induction w.
  - reflexivity.
  - destruct a; cbn -[Z.of_nat]; lia.
Qed.

Corollary level_count_le_iff w:
  0 <= level w <-> (#false w <= #true w)%nat.
Proof. rewrite level_count. lia. Qed.

Lemma level_firstn_false:
  forall n, -1 <= level (firstn n [false]).
Proof.
  intro n. destruct n.
  - cbn. lia.
  - cbn. rewrite firstn_nil. reflexivity.
Qed.

Lemma dyck_level_firstn w:
  Dyck w -> forall n, 0 <= level (firstn n w).
Proof.
  intros D. induction D; intro n.
  - rewrite firstn_nil. reflexivity.
  - destruct n; [reflexivity|].
    cbn. rewrite firstn_app, level_app.
    pose (level_firstn_false (n - length w)). specialize (IHD n). lia.
  - rewrite firstn_app, level_app.
    specialize (IHD1 n). specialize (IHD2 (n - length w1)%nat). lia.
Qed.

End level.

Corollary Dyck_firstn_le w:
  Dyck w -> forall n, #false (firstn n w) <= #true (firstn n w).
Proof. intros. apply level_count_le_iff, dyck_level_firstn. assumption. Qed.

Require Import Wellfounded.

Lemma count_occ_last {A: Type} (eq_dec: forall x y : A, {x = y} + {x <> y})
  (x a b: A) (l: list A):
  count_occ eq_dec (a::l++[b]) x = count_occ eq_dec (a::b::l) x.
Proof.
  apply Permutation_count_occ. constructor.
  symmetry. apply Permutation_cons_append.
Qed.

Lemma firstn_le_app {A: Type} n (l1 l2: list A):
  n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  intros H%Nat.sub_0_le. rewrite firstn_app.
  rewrite H, firstn_O, app_nil_r. reflexivity.
Qed.

Theorem firstn_le_Dyck w:
  #false w = #true w ->
  (forall i : nat, i < length w -> #false (firstn i w) <= #true (firstn i w)) ->
  Dyck w.
Proof.
  induction w as [w IH]
  using (well_founded_induction ((wf_inverse_image _ _ _ (@length _)) lt_wf)).
  intros H1 H2. pose (P i := #false (firstn i w) = #true (firstn i w)).
  assert (has_unique_least_element le P) as [i [[Hi i_min] i_uniq]]. {
    apply dec_inh_nat_subset_has_unique_least_element.
    * unfold P. intro n. apply dec_eq_nat.
    * exists (length w). unfold P. rewrite firstn_all. exact H1.
  }
  assert (Even w) as w_Even by now apply count_eq_even.
  destruct (dec_eq_nat i (length w)).
  - destruct w_Even; [constructor|].
    rewrite !count_occ_last in H1. destruct a.
    + destruct b; cbn in H1.
      * exfalso. revert H1 H2. clear. intros H1 H2.
        specialize (H2 (1 + length w + 0)). cbn in H2.
        rewrite firstn_app_2, firstn_O, app_nil_r in H2.
        rewrite H1 in H2. eapply Nat.nle_succ_diag_l, H2.
        rewrite app_length. cbn. lia.
      * constructor. apply IH.
        -- cbn. rewrite app_length. lia.
        -- injection H1. easy.
        -- intros j Hj. specialize (H2 (S j)).
           cbn in H2. rewrite firstn_le_app in H2.
           specialize (i_min (S j)). specialize (i_uniq (S j)).
Abort.