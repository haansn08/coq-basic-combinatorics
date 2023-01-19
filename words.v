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
Variable A : Type.
Implicit Type l : list A.

Definition insert_at i x l :=
  firstn i l ++ [x] ++ skipn i l.

Lemma Add_nil x l:
  Add x [] l <-> l = [x].
Proof.
  split; intro H.
  - remember [] as l'. destruct H.
    + reflexivity.
    + discriminate Heql'.
  - rewrite H. constructor.
Qed.

Fixpoint insert_all0 x (left right: list A) :=
match right with
| nil => [left++[x]]
| y::right' => (left++x::right)::(insert_all0 x (left++[y]) right')
end.

Definition insert_all x l := insert_all0 x nil l.

Lemma insert_all0_length_left x l:
  forall left, length (insert_all0 x left l) = length (insert_all x l).
Proof.
  induction l.
  - reflexivity.
  - intro left. cbn. rewrite !IHl. reflexivity.
Qed. 

Lemma Add_insert_all x:
  forall (l l': list A), Add x l l' <-> In l' (insert_all x l).
Proof.
  intros l l'. split; intro H.
  - induction H.
    + destruct l; left; reflexivity.
    + apply Add_split in H. destruct H as [l1 [l2 [-> ->]]].
      cbn. right. 
Abort. 

Lemma insert_all_length x l:
  length (insert_all x l) = S (length l).
Proof.
  unfold insert_all. induction l.
  - reflexivity.
  - cbn. f_equal. rewrite insert_all0_length_left in *. assumption.
Qed.

Fixpoint permutations l :=
match l with
| nil => [[]]
| x::l' => flat_map (insert_all x) (permutations l')
end.

Lemma permutations_spec:
  forall l l', Permutation l l' <-> In l' (permutations l).
Proof.
  intros l l'. split; intro H.
  - induction H.
    + left. reflexivity.
    + apply in_flat_map. exists l'.
Abort.

End permutations.
