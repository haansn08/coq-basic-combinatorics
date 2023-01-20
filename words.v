Require Import List Permutation Factorial Arith.
Require Import Lia Setoid.
Import ListNotations.

Section flat_map.
(* TODO: remove when https://github.com/coq/coq/pull/17082 is released *)
Lemma concat_length A l:
  length (concat l) = list_sum (map (@length A) l).
Proof.
  induction l; [reflexivity|].
  simpl. rewrite app_length.
  f_equal. assumption.
Qed.

Lemma flat_map_length A B (f: A -> list B) l:
  length (flat_map f l) = list_sum (map (fun x => length (f x)) l).
Proof.
  rewrite flat_map_concat_map, concat_length, map_map. reflexivity.
Qed.

Corollary flat_map_constant_length A B c (f: A -> list B) l:
  (forall x, In x l -> length (f x) = c) -> length (flat_map f l) = (length l) * c.
Proof.
  intro H. rewrite flat_map_length.
  induction l; [reflexivity|].
  simpl. rewrite IHl, H.
  - reflexivity.
  - left. reflexivity.
  - intros x Hx. apply H. right. assumption.
Qed.
End flat_map.

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
      set (k := rising_fact n (S x - n)).
      rewrite Nat.sub_add by assumption. reflexivity.
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

Fixpoint additions0 x (left right: list A) :=
match right with
| nil => [left++[x]]
| y::right' => (left++x::right)::(additions0 x (left++[y]) right')
end.

Definition additions x l := additions0 x nil l.

Lemma additions0_length_left x l:
  forall left, length (additions0 x left l) = length (additions x l).
Proof.
  induction l.
  - reflexivity.
  - intro left. cbn. rewrite !IHl. reflexivity.
Qed.

Lemma additions0_left x l:
  forall left, In (left ++ l) (additions0 x left l) <-> In l (additions x l).
Proof. (* TODO: redo *)
  induction l.
  - intro left. cbn. split; intros [].
    + apply app_inv_head in H. left. assumption.
    + contradiction H.
    + left. f_equal. assumption.
    + contradiction H.
  - intro left. split; intro H.
    + cbn in *. destruct H.
      * left. apply app_inv_head in H. assumption.
      * right. apply (IHl [a0]). specialize (IHl (left ++ [a0])).
        replace ((left ++ [a0]) ++ l) with (left ++ a0 :: l) in IHl.
        -- apply IHl in H. assumption.
        -- rewrite app_assoc_reverse. reflexivity.
    + right. specialize (IHl (left ++ [a0])) as H1.
      replace ((left ++ [a0]) ++ l) with (left ++ a0 :: l) in H1.
      * apply H1. specialize (IHl [a0]). cbn in *. destruct H.
        -- exfalso. apply f_equal with (f := @length _) in H.
           cbn in H. injection H. clear. apply Nat.neq_succ_diag_l.
        -- apply IHl. assumption.
      * rewrite app_assoc_reverse. reflexivity.
Qed.

Lemma insert_all_in x (l1 l2: list A):
  In (l1++x::l2) (additions x (l1++l2)).
Proof.
  revert l2. induction l1.
  - destruct l2; left; reflexivity.
  - intros. right. cbn. 
Abort.

Lemma Add_insert_all x:
  forall (l l': list A), Add x l l' <-> In l' (additions x l).
Proof.
  intros l l'. split; intro H.
  - induction H.
    + destruct l; left; reflexivity.
    + apply Add_split in H. destruct H as [l1 [l2 [-> ->]]].
      right. induction l1.
      * destruct l2; left; reflexivity.
      * right. cbn. cbn in IHl1.
Abort. 

Lemma additions_length x l:
  length (additions x l) = S (length l).
Proof.
  unfold additions. induction l.
  - reflexivity.
  - cbn. f_equal. rewrite additions0_length_left in *. assumption.
Qed.

Fixpoint permutations l :=
match l with
| nil => [[]]
| x::l' => flat_map (additions x) (permutations l')
end.

Lemma permutations_spec:
  forall l l', Permutation l l' <-> In l' (permutations l).
Proof.
  intros l l'. split; intro H.
  - induction H.
    + left. reflexivity.
    + apply in_flat_map. exists l'.
Admitted.

Theorem permutations_fact l:
  length (permutations l) = fact (length l).
Proof.
  induction l.
  - reflexivity.
  - cbn. rewrite flat_map_constant_length with (c := S (length l)); [lia|].
    intros x Hx%permutations_spec. rewrite additions_length.
    f_equal. apply Permutation_length. symmetry. assumption.
Qed.

End permutations.
