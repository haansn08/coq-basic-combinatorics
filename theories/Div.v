Require Import Arith Factorial Lia.
Import Nat.

Lemma div_mul_mul a b c:
  b <> 0 -> c <> 0 -> (b * c | a) ->
  (a / (b * c)) * b = a / c.
Proof.
  intros Hb Hc [x ->]. rewrite div_mul.
  - now rewrite mul_assoc, div_mul.
  - apply neq_mul_0; split; assumption.
Qed.

Lemma mul_div a b:
  b <> 0 -> (b | a) ->
  (a / b) * b = a.
Proof.
  intros Hb Hc.
  replace b with (b * 1) at 1 by apply mul_1_r.
  rewrite div_mul_mul.
  - apply div_1_r.
  - assumption.
  - auto.
  - rewrite mul_1_r. assumption.
Qed.

Lemma mul_div_mul a b c:
  b <> 0 -> (b | a) -> (b | c) ->
  (a / b) * c = a * (c / b).
Proof.
  intros H [x ->] [y ->].
  rewrite !div_mul; try exact H.
  lia.
Qed.

Section factorials.
Fixpoint falling_fact k n :=
match k, n with
| 0, _ => 1
| _, 0 => 0
| S k', S n' => n * falling_fact k' n'
end.

Fixpoint rising_fact k n :=
match k with
| 0 => 1
| S k' => n * rising_fact k' (S n)
end.

Lemma falling_fact_1_n n:
  falling_fact 1 n = n.
Proof.
  destruct n; [reflexivity|].
  cbn [falling_fact].
  rewrite mul_1_r. reflexivity.
Qed.

Lemma falling_fact_fact n: falling_fact n n = fact n.
Proof.
  induction n; [reflexivity|cbn].
  rewrite IHn. reflexivity.
Qed.

Lemma rising_fact_S n x:
  rising_fact (S n) x = (x + n) * rising_fact n x.
Proof.
  revert x. induction n; intros x.
  - cbn. auto.
  - remember (S n) as m. (* to avoid zealous cbn *)
    cbn. rewrite IHn by auto.
    subst m. cbn. lia. (* ??? *) 
Qed.

Lemma falling_raising_fact k n:
  k <= S n -> falling_fact k n = rising_fact k (S n-k).
Proof.
  revert n. induction k.
  - reflexivity.
  - intros n H%le_S_n. rewrite rising_fact_S. destruct n.
    + cbn. lia.
    + cbn [falling_fact]. rewrite IHk by assumption.
      rewrite sub_succ, Nat.sub_add by assumption. reflexivity.
Qed.

Lemma rising_fact_fact n: rising_fact n 1 = fact n.
Proof.
  induction n; [ reflexivity | ].
  rewrite rising_fact_S, IHn; constructor.
Qed.

Lemma falling_fact_n_0 n:
  falling_fact n 0 = if n then 1 else 0.
Proof. destruct n; reflexivity. Qed.

Lemma fact_falling_fact n k:
k <= n -> fact n = falling_fact k n * fact (n-k).
Proof.
  revert k. induction n; intros k H.
  - apply le_0_r in H. subst. reflexivity.
  - destruct k; cbn [falling_fact]; [auto with arith|].
    cbn [fact]. rewrite (IHn k).
    + rewrite sub_succ, mul_assoc. reflexivity.
    + apply le_S_n. assumption.
Qed.

Lemma minus_minus a b:
  b <= a -> a - (a - b) = b.
Proof. lia. Qed.

Lemma fact_divide n k:
  k <= n -> (fact k | fact n).
Proof.
  intro H.
  rewrite (fact_falling_fact n (n - k)).
  + rewrite minus_minus by assumption.
    apply divide_factor_r.
  + apply le_sub_l.
Qed.

Lemma fact_divide_S n:
  fact (S n) / fact n = S n.
Proof.
  cbn [fact]. rewrite div_mul.
  - reflexivity.
  - apply fact_neq_0.
Qed.

Lemma falling_fact_fact_divide n k:
  k <= n -> (fact k | falling_fact k n).
Proof.
  intro H.
  rewrite falling_raising_fact by (apply le_S; assumption).
  induction k.
  - apply divide_refl.
  - assert (k <= n) as H2 by (apply Le.le_Sn_le_stt; assumption).
    specialize (IHk H2).
    rewrite sub_succ_l in IHk by exact H2.
    rewrite sub_succ. cbn [rising_fact fact].
    destruct IHk as [x Hx]. rewrite Hx, mul_assoc.
    apply mul_divide_mono_r.
Admitted.

End factorials.

Lemma choose_divides n k:
  k <= n -> (fact k * fact (n - k) | fact n).
Proof.
  intros H. rewrite (fact_falling_fact n k) by assumption.
  apply mul_divide_mono_r, falling_fact_fact_divide.
  assumption.
Qed.