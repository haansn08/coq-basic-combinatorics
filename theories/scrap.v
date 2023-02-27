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