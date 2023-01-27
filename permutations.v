Require Import List Permutation Factorial Arith.
Require Import Lia Setoid.
Import ListNotations.

(* TODO: remove when https://github.com/coq/coq/pull/17082 is released *)
Section flat_map.
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
      rewrite Nat.sub_add by assumption. reflexivity.
Qed.

Lemma rising_fact_fact n: rising_fact n 1 = fact n.
Proof.
  induction n; [ reflexivity | ].
  rewrite rising_fact_S, IHn; constructor.
Qed.
End factorials.

(* https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/seq.v#L4326 *)
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

Lemma insert_at_length i x l:
  length (insert_at i x l) = S (length l).
Proof.
  unfold insert_at. autorewrite with list. cbn.
  enough (length (firstn i l) + length (skipn i l) = length l) by lia.
  rewrite <- app_length, firstn_skipn. reflexivity.
Qed.

Lemma insert_at_cons i x l a:
  insert_at (S i) x (a :: l) = a :: insert_at i x l.
Proof. cbn. f_equal. Qed.

Lemma Add_insert_at x l:
  forall l', Add x l l' <-> exists i, i <= length l /\ l' = insert_at i x l.
Proof.
  intro l'. split; intro H.
  - induction H.
    + exists 0. split; [apply Nat.le_0_l | reflexivity].
    + destruct IHAdd as [i [Hi ->]]. exists (S i). split.
      * cbn. apply le_n_S. assumption.
      * cbn. f_equal.
  - destruct H as [i [Hi H]].
    revert Hi H. revert l l'. induction i; intros l l' Hi H.
    + rewrite H. constructor.
    + destruct l.
      * exfalso. eapply Nat.nle_succ_0. exact Hi.
      * rewrite H, insert_at_cons. constructor.
        apply IHi; [ | reflexivity]. apply le_S_n. assumption.
Qed.

Definition additions x l :=
  map (fun i => insert_at i x l) (seq 0 (S (length l))).

Lemma in_additions x l l':
  In l' (additions x l) <-> exists i, i <= length l /\ l' = insert_at i x l.
Proof. 
  split; intro H.
  - apply in_map_iff in H as [i [H0 H1]]. exists i.
    apply in_seq in H1 as [_ H1]. split.
    + apply le_S_n. exact H1.
    + symmetry. exact H0.
  - apply in_map_iff. destruct H as [i [H1 H0]].
    exists i. split.
    + symmetry. exact H0.
    + apply in_seq. split.
      * apply Nat.le_0_l.
      * apply le_n_S. exact H1.
Qed.

Corollary additions_spec x:
  forall (l l': list A), Add x l l' <-> In l' (additions x l).
Proof. intros l l'. rewrite Add_insert_at, in_additions. reflexivity. Qed.

Lemma seq_shift_n len start n:
  map (Nat.add n) (seq start len) = seq (n + start) len.
Proof.
  induction n.
  - now rewrite map_id.
  - cbn. now rewrite <- map_map, IHn, seq_shift.
Qed.

Lemma map_ext_seq {X} (f g: nat -> X) n start d:
  (forall j, start <= j < start + n -> f (d + j) = g j) ->
  map f (seq (start + d) n) = map g (seq start n).
Proof.
  intro H. rewrite Nat.add_comm, <- seq_shift_n.
  rewrite map_map. apply map_ext_in.
  intros j ?%in_seq. apply H. assumption.
Qed.

Lemma additions_cons x a l:
  additions x (a :: l) = (x::a::l)::map (cons a) (additions x l).
Proof.
  cbn. f_equal. f_equal. rewrite map_map.
  replace 2 with (1 + 1) by reflexivity.
  apply map_ext_seq. reflexivity.
Qed.

Lemma additions_length x l:
  length (additions x l) = S (length l).
Proof. unfold additions. now rewrite map_length, seq_length. Qed.

Fixpoint permutations l :=
match l with
| nil => [[]]
| x::l' => flat_map (additions x) (permutations l')
end.

Lemma permutations_refl l:
  In l (permutations l).
Proof.
  induction l; [now left|].
  cbn. apply in_flat_map. exists l.
  split; [assumption | now left].
Qed.

#[export] Instance Permutation_additions:
  Morphisms.Proper (eq ==> Permutation (A:=A) ==> Permutation (A:=list A)) additions.
Proof.
  intros _ x -> l l' H. induction H.
  - cbn. apply Permutation_refl.
  - 
Admitted.

#[export] Instance Permutation_permutations:
  Morphisms.Proper (Permutation (A:=A) ==> Permutation(A:=list A)) permutations.
Proof.
  intros l l' H. induction H.
  - repeat constructor.
  - cbn. rewrite IHPermutation. apply Permutation_refl.
  - cbn.  
Admitted.

Lemma permutations_spec:
  forall l l', Permutation l l' <-> In l' (permutations l).
Proof.
  intros l l'. split; intro H.
  - induction H.
    + apply permutations_refl.
    + cbn. apply in_flat_map. exists l'.
      split; [assumption | apply additions_spec; constructor].
    + cbn. apply in_flat_map. exists (x :: l). split.
      * apply in_flat_map. exists l.
        split; [apply permutations_refl | now left].
      * apply additions_spec. repeat constructor.
    + rewrite H, H0. apply permutations_refl.
  - revert H. revert l'. induction l.
    + intros l' [->|[]]. apply Permutation_refl.
    + intros l' H. cbn in H. apply in_flat_map in H as [x [H0 H1]].
      specialize (IHl x H0). rewrite IHl.
      apply Permutation_Add, additions_spec. assumption.
Qed.

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
