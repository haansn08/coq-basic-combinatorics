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

Section factorials.
Fixpoint falling_fact n x :=
match n, x with
| 0, _ => 1
| _, 0 => 0
| S n', S x' => x * falling_fact n' x'
end.

Fixpoint rising_fact n x :=
match n with
| 0 => 1
| S n' => x * rising_fact n' (S x)
end.

Lemma falling_fact_fact n: falling_fact n n = fact n.
Proof.
  induction n; [reflexivity|simpl].
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

Lemma falling_raising_fact n x:
  n <= S x -> falling_fact n x = rising_fact n (S x-n).
Proof.
  revert x. induction n.
  - reflexivity.
  - intros x H%le_S_n. rewrite rising_fact_S. destruct x.
    + cbn. lia.
    + cbn [falling_fact]. rewrite IHn by assumption.
      replace (S (S x) - S n) with (S x - n) by lia.
      rewrite Nat.sub_add by assumption. reflexivity.
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

End factorials.

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

Lemma choose_divides n k:
  k <= n -> (fact k * fact (n - k) | fact n).
Proof.
  intros H. rewrite (fact_falling_fact n k) by assumption.
  apply mul_divide_mono_r.
Admitted.