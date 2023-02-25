Require Import List Bool Arith.
Require Import Lia.
Import ListNotations.

From BasicCombinatorics Require Import Binomial.

Inductive Dyck: word -> Prop :=
| Dyck_nil: Dyck nil
| Dyck_shift: forall w, Dyck w -> Dyck (true::w++[false])
| Dyck_app: forall w1, Dyck w1 -> forall w2, Dyck w2 -> Dyck (w1 ++ w2).

Lemma length_cons_ends [A: Type] (x y: A) (l: list A):
  length (x::l++[y]) = S (S (length l)).
Proof. cbn. rewrite last_length. reflexivity. Qed.

Lemma Dyck_even w:
  Dyck w -> Nat.Even (length w).
Proof.
  intros D. induction D. (* good example for not inducting on w *)
  - exists 0. reflexivity.
  - rewrite length_cons_ends. apply Nat.Even_succ_succ. assumption.
  - rewrite app_length. apply Nat.Even_Even_add; assumption.
Qed.

Lemma div2_add_distr n m:
  Nat.Even m -> Nat.div2 (n + m) = Nat.div2 n + Nat.div2 m.
Proof.
  intros [q ->]. destruct (Nat.Even_or_Odd n) as [[p ->]|[p ->]].
  - rewrite <- Nat.mul_add_distr_l.
    rewrite !Nat.div2_double. reflexivity.
  - rewrite Nat.add_1_r, Nat.add_succ_l, Nat.div2_succ_double.
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
  - rewrite app_length. rewrite div2_add_distr by now apply Dyck_even.
    apply Binomial_app; assumption.
Qed.

Notation "'#true' w" := (count_occ bool_dec w true) (at level 10).
Notation "'#false' w" := (count_occ bool_dec w false) (at level 10).

Lemma Dyck_count_eq w:
  Dyck w -> #false w = #true w.
Proof.
  intros D. induction D.
  - reflexivity.
  - cbn. rewrite !count_occ_app. cbn. lia.
  - rewrite !count_occ_app. congruence.
Qed.

Lemma firstn_lt_length [A:Type] (P: list A -> Prop) l:
  (forall n, n < length l -> P (firstn n l)) /\ P l ->
  (forall n, P (firstn n l)).
Proof.
  intros H n. destruct (dec_lt n (length l)) as [Hn|Hn].
  + intuition.
  + apply not_lt in Hn. rewrite firstn_all2; intuition.
Qed.

Lemma Dyck_firstn_le w:
  Dyck w -> forall i, #false (firstn i w) <= #true (firstn i w).
Proof.
  intros D i. apply firstn_lt_length. clear i. split.
  + induction D; intros i Hi.
    * apply Nat.nlt_0_r in Hi. contradiction.
    * rewrite length_cons_ends in Hi. destruct i.
      -- rewrite firstn_O. reflexivity.
      -- rewrite firstn_cons. rewrite <- firstn_removelast.
          ++ rewrite removelast_last. cbn. constructor.
             apply firstn_lt_length. split.
             ** intros i' Hi'. apply IHD. assumption.
             ** apply Nat.eq_le_incl. now apply Dyck_count_eq.
          ++ rewrite last_length. now apply Nat.succ_lt_mono.
    * rewrite firstn_app, !count_occ_app.
      destruct (lt_dec i (length w1)) as [H1|H2%not_lt].
      -- replace (i - length w1) with 0 by lia. rewrite firstn_O, !Nat.add_0_r.
         apply firstn_lt_length. split.
         ++ apply IHD1.
         ++ apply Nat.eq_le_incl. now apply Dyck_count_eq.
      -- rewrite firstn_all2 by lia. rewrite Dyck_count_eq by assumption.
         apply Nat.add_le_mono_l. apply IHD2.
         rewrite app_length in Hi. lia.
  + apply Nat.eq_le_incl. now apply Dyck_count_eq.
Qed.

Lemma Dyck_nonempty w:
  w <> [] -> Dyck w -> exists w', w = true::w'++[false].
Proof. Abort.

Lemma count_true_false_length w:
  #false w + #true w = length w.
Proof.
  induction w.
  - reflexivity.
  - destruct a.
    * cbn. rewrite Nat.add_succ_r. f_equal. assumption.
    * cbn. f_equal. assumption.
Qed.

Lemma count_eq_even w:
  #false w = #true w -> Nat.Even (length w).
Proof.
intro H.

Admitted.

Require Import Wellfounded.

Lemma firstn_le_Dyck w:
  #false w = #true w ->
  (forall i : nat, #false (firstn i w) <= #true (firstn i w)) ->
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
  destruct (dec_eq_nat i (length w)).
  - apply count_eq_even in H1 as [n Hn].
Abort.