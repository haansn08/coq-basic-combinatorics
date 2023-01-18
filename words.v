Require Import List Permutation Factorial Arith.
Require Import Lia.
Import ListNotations.

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

Lemma falling_raising_fact n k:
  k <= n -> falling_fact n k = rising_fact n (n-k).
Proof.
  induction n; intros H; [reflexivity | ].
  cbn.
Abort.

Lemma rising_fact_S n x:
  0 < x -> rising_fact (S n) x = (x + n) * rising_fact n x.
Proof.
  revert x. induction n; intros x H.
  - cbn. auto.
  - remember (S n) as m. (* to avoid zealous cbn *)
    cbn. rewrite IHn by auto.
    subst m. cbn. lia. (* ??? *) 
Qed.

Lemma rising_fact_fact n: rising_fact n 1 = fact n.
Proof.
  induction n; [ reflexivity | ].
  rewrite rising_fact_S, IHn; constructor.
Qed.
End factorials.

Variant alphabet := a|b|c|d.

Section permutations.

Definition insert_at {A} i x (l: list A) :=
  firstn i l ++ [x] ++ skipn i l.

Definition insert_all {A} x (l: list A) :=
  (fix f i :=
    match i with 
    | 0 => [ insert_at 0 x l ]
    | S i' => insert_at i x l :: f i'
    end
  ) (length l).

Lemma Add_nil {A} x (l: list A):
  Add x [] l <-> l = [x].
Proof.
  split; intro H.
  - remember [] as l'. destruct H.
    + reflexivity.
    + discriminate Heql'.
  - rewrite H. constructor.
Qed.

Lemma Add_insert_all {A} x:
  forall (l l': list A), Add x l l' <-> In l' (insert_all x l).
Proof.
  intros l l'. split; intro H.
  - induction H.
    + unfold insert_all. induction (length l).
      * left. reflexivity.
      * cbn. destruct l.
        -- left. reflexivity.
        -- right. assumption.
    + 
Abort. 

Lemma insert_all_length {A} x (l: list A):
  length (insert_all x l) = S (length l).
Proof.
  remember (length l) as n. revert Heqn. revert l. induction n.
  - intros l H. symmetry in H. apply length_zero_iff_nil in H.
    subst l. reflexivity.
  - intros l H. 
Abort.

Fixpoint permutations {A} (l: list A) :=
match l with
| nil => [[]]
| x::l' => flat_map (insert_all x) (permutations l')
end.

Lemma permutations_spec {A}:
  forall (l l': list A), Permutation l l' <-> In l' (permutations l).
Proof.
  intros l l'. split; intro H.
  - induction H.
    + left. reflexivity.
    + apply in_flat_map. exists l'.
Abort.

End permutations.
