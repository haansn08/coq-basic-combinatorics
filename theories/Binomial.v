Require Import Bool FinFun.
From BasicCombinatorics Require Import List.

Definition word := list bool.

Inductive Binomial: nat -> word -> Prop :=
| Binomial_nil: Binomial 0 []
| Binomial_true: forall k w, Binomial k w -> Binomial (S k) (true::w)
| Binomial_false: forall k w, Binomial k w -> Binomial k (false::w).

Lemma Binomial_false_end:
  forall k w, Binomial k w -> Binomial k (w ++ [false]).
Proof.
  intros k w B. induction B.
  - repeat constructor.
  - cbn. constructor. assumption.
  - cbn. constructor. assumption.
Qed.

Lemma Binomial_spec:
  forall k w, Binomial k w <-> count_occ bool_dec w true = k.
Proof.
  intros k w. split.
  - intros H. induction H.
    + reflexivity.
    + cbn. f_equal. assumption.
    + cbn. assumption.
  - intros <-. induction w.
    + constructor.
    + destruct a; cbn; constructor; assumption.
Qed.

Lemma Binomial_app:
  forall k1 w1, Binomial k1 w1 -> forall k2 w2, Binomial k2 w2 ->
  Binomial (k1 + k2) (w1 ++ w2).
Proof.
  intros k1 w1 B1%Binomial_spec k2 w2 B2%Binomial_spec.
  apply Binomial_spec. rewrite count_occ_app. now rewrite B1, B2.
Qed.

Fixpoint binomials n k :=
match n, k with
| 0, 0 => [[]]
| 0, _ => []
| _, 0 => [ repeat false n ]
| S n', S k' => map (cons true) (binomials n' k') 
             ++ map (cons false) (binomials n' k) 
end.

Lemma Binomial_falses_iff w:
  Binomial 0 w <-> w = repeat false (length w).
Proof.
  split; intro H.
  - eapply count_occ_repeat_excl. destruct y.
    + intros _. apply Binomial_spec. exact H.
    + intro E. contradiction E. reflexivity.
  - rewrite H. clear. induction w.
    + constructor.
    + cbn. constructor. assumption.
Qed.

Corollary Binomial_falses n:
  Binomial 0 (repeat false n).
Proof.
  apply Binomial_falses_iff.
  rewrite repeat_length. reflexivity.
Qed.

Lemma binomials_falses n w:
  In w (binomials n 0) <-> repeat false n = w.
Proof.
  induction n.
  - cbn. tauto.
  - split; intro H.
    + cbn in H. tauto.
    + left. assumption.
Qed.

Lemma binomials_cons_true n k w:
  In (true::w) (binomials (S n) (S k)) <-> In w (binomials n k).
Proof.
  split; intro H.
  - cbn in H. apply In_app_map_cons in H as [[w' [H1 H2]]|[w' [H1 H2]]].
    + injection H1 as ->. assumption.
    + discriminate H1.
  - cbn. apply in_or_app. left.
    apply In_map_cons. assumption.
Qed.

Lemma binomials_cons_false n k w:
  In (false::w) (binomials (S n) k) <-> In w (binomials n k).
Proof.
  destruct k; split; intro H.
  - cbn in H. destruct H.
    + apply binomials_falses. injection H. easy.
    + contradiction.
  - apply binomials_falses in H as <-.
    left. reflexivity.
  - cbn in H. apply In_app_map_cons in H as [[w' [H1 H2]]|[w' [H1 H2]]].
    + discriminate H1.
    + injection H1 as ->. assumption.
  - cbn. apply in_or_app. right. apply In_map_cons. exact H.
Qed.

Lemma binomials_O_nil k w:
  In w (binomials 0 k) -> w = [].
Proof.
  intro H. cbn in H. destruct k.
  - now apply In_singleton in H.
  - exfalso. intuition.
Qed.

Lemma binomials_O_O k w:
  In w (binomials 0 k) -> k = 0.
Proof.
  intro H. cbn in H. destruct k.
  - reflexivity.
  - exfalso. intuition.
Qed.

Lemma binomials_length w n k:
  In w (binomials n k) -> length w = n.
Proof.
  revert n k. induction w; intros n k H.
  - destruct n; [reflexivity|exfalso].
    cbn in H. destruct k.
    + apply In_singleton in H. discriminate H.
    + apply In_app_map_cons in H as [[w' [H1 H2]]|[w' [H1 H2]]];
      discriminate H1.
  - destruct n.
    + apply binomials_O_nil in H. discriminate H.
    + destruct a, k; cbn; f_equal.
      * exfalso. destruct H; [discriminate H|contradiction].
      * apply -> binomials_cons_true in H.
        eapply IHw. exact H.
      * cbn in H. destruct H; [injection H as <-|contradiction].
        apply repeat_length.
      * apply -> binomials_cons_false in H. eapply IHw. exact H.
Qed.

Theorem binomials_correct n k w:
  In w (binomials n k) <-> length w = n /\ Binomial k w.
Proof.
  split.
  - intros H. split.
    + apply binomials_length in H. assumption.
    + revert H. revert w k. induction n; intros w k H.
      * rewrite (binomials_O_O _ _ H), (binomials_O_nil _ _ H). constructor.
      * cbn in H. destruct k.
        -- apply In_singleton in H. apply Binomial_falses_iff. rewrite <- H.
           cbn. rewrite repeat_length. reflexivity.
        -- apply In_app_map_cons in H as [[w' [-> H2]]|[w' [-> H2]]].
           ++ constructor. apply IHn. exact H2.
           ++ constructor. apply IHn. exact H2.
   - intros [<- B]. induction B.
     + now left.
     + cbn [length]. apply binomials_cons_true. assumption.
     + cbn [length]. apply binomials_cons_false. assumption.
Qed.

Theorem binomials_NoDup n k:
  NoDup (binomials n k).
Proof.
  revert k. induction n.
  - destruct k; [apply NoDup_singleton | constructor].
  - destruct k.
    + apply NoDup_singleton.
    + cbn. apply NoDup_app.
      * apply FinFun.Injective_map_NoDup.
        -- intros x y H. injection H. easy.
        -- apply IHn.
      * apply FinFun.Injective_map_NoDup.
        -- intros x y H. injection H. easy.
        -- apply IHn.
      * intros l H1%In_map_cons_elim H2%In_map_cons_elim.
        destruct H1 as [l1 [H1 _]]. destruct H2 as [l2 [H2 _]].
        subst l. discriminate H2.
Qed.

Require Import Factorial Arith Lia.

Lemma binomials_n_lt_k n k:
  n < k -> binomials n k = [].
Proof.
  revert k. induction n; destruct k.
  * intro E. destruct (Nat.lt_irrefl _ E).
  * reflexivity.
  * intros E%Nat.nle_succ_0. destruct E.
  * intros H%Nat.succ_lt_mono. cbn.
    now rewrite IHn, (IHn (S k)) by lia.
Qed.

Lemma binomials_n_n n:
  binomials n n = [repeat true n].
Proof.
  induction n.
  - reflexivity.
  - cbn. rewrite IHn, (binomials_n_lt_k n (S n)); auto.
Qed.

Definition choose n k := fact n / (fact k * fact (n - k)).

Lemma choose_n_0 n: choose n 0 = 1.
Proof.
  unfold choose. rewrite !Nat.mul_1_l, Nat.sub_0_r, Nat.div_same.
  - reflexivity.
  - apply Nat.neq_0_lt_0, lt_O_fact.
Qed.

Lemma choose_n_1 n: choose (S n) 1 = S n.
Proof.
  unfold choose. rewrite Nat.mul_1_l, Nat.sub_succ, Nat.sub_0_r.
  cbn [fact]. rewrite Nat.div_mul.
  + reflexivity.
  + apply fact_neq_0.
Qed.

Lemma choose_n_n n: choose n n = 1.
Proof.
  unfold choose.
  rewrite Nat.sub_diag, Nat.mul_1_r, Nat.div_same
    by apply Nat.neq_0_lt_0, lt_O_fact.
  reflexivity.
Qed.

Lemma div_eqn_multiply a b c:
  b <> 0 -> a = c * b -> a / b = c.
Proof. intros H ->. apply Nat.div_mul. assumption. Qed.

Lemma choose_recursion n k (H: k < n):
   choose (S n) (S k) = choose n k + choose n (S k).
Proof.
  unfold choose. apply div_eqn_multiply.
  - apply Nat.neq_mul_0. split; apply fact_neq_0.
  - rewrite Nat.mul_add_distr_r.
Admitted.

Theorem binomials_count n k:
  k <= n -> length (binomials n k) = choose n k.
Proof.
  revert k. induction n.
  - cbn. destruct k.
    + reflexivity.
    + intros H%Nat.nle_succ_0. contradiction.
  - cbn [binomials]. destruct k.
    + rewrite choose_n_0. reflexivity.
    + intros H%le_S_n%le_lt_eq_dec. destruct H.
      * rewrite app_length, !map_length.
        rewrite (IHn k), (IHn (S k)) by lia.
        symmetry. apply choose_recursion. assumption.
      * clear IHn. subst k.
        rewrite binomials_n_n, binomials_n_lt_k, choose_n_n; auto.
Qed.