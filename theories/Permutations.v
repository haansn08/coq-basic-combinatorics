Require Import Permutation Factorial Arith.
Require Import Lia Setoid.


From BasicCombinatorics Require Import List.

(* see also:
  - https://github.com/clucas26e4/List_Permutation
  - https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/seq.v#L4326
*)

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

Section permutations.
Variable A : Type.
Implicit Type l : list A.

Definition insert_at i x l :=
  firstn i l ++ x :: skipn i l.

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
| nil => [ nil ]
| x::l' => flat_map (additions x) (permutations l')
end.

Lemma permutations_refl l:
  In l (permutations l).
Proof.
  induction l; [now left|].
  cbn. apply in_flat_map. exists l.
  split; [assumption | now left].
Qed.

Lemma permutations_spec:
  forall l l', Permutation l l' <-> In l' (permutations l).
Proof.
  intros l l'. split; intro H.
  - revert H. revert l'. induction l; intros l' H.
    + apply Permutation_nil in H as ->. apply permutations_refl.
    + cbn. apply in_flat_map. symmetry in H.
      destruct (Permutation_vs_elt_inv nil _ _ H) as [l1 [l2 ->]].
      exists (l1 ++ l2); split.
      * apply IHl. apply Permutation_cons_app_inv with (a:=a).
        symmetry. assumption.
      * apply additions_spec, Add_app.
  - revert H. revert l'. induction l; intros l' H.
    + apply In_singleton in H as <-. constructor.
    + cbn in H. apply in_flat_map in H as [l'' [Hl'' H%additions_spec]].
      specialize (IHl _ Hl''). rewrite IHl. apply Permutation_Add. assumption.
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

Lemma insert_at_inj x l i j:
  ~ In x l -> i <= length l -> j <= length l ->
  insert_at i x l = insert_at j x l -> i = j.
Proof.
  intros xInl Hi Hj H. unfold insert_at in H.
  apply app_inj_pivot in H as [H1 _].
  - apply (f_equal (@length _)) in H1.
    now rewrite !firstn_length, !Nat.min_l in H1.
  - intro E. apply xInl. clear -E.
    rewrite <- (firstn_skipn i). apply in_or_app.
    left. assumption.
  - intro E. apply xInl. clear -E.
    rewrite <- (firstn_skipn j). apply in_or_app.
    left. assumption.
Qed.

Lemma additions_NoDup x l:
  NoDup l -> ~ In x l -> NoDup (additions x l).
Proof.
  intros Hl Hx. unfold additions.
  apply (InjectiveOn_map_NoDup (fun i => i <= length l)).
  - intros i j Pi Pj Heq. eapply (insert_at_inj x l); try assumption.
  - apply Forall_forall. intros j H.
    apply in_seq in H as [_ H%le_S_n]. assumption.
  - apply seq_NoDup.
Qed.

Lemma additions_Proper x:
  Morphisms.Proper
  ((fun l1 l2 => (~ In x l1 /\ ~ In x l2) /\ l1 <> l2) ==>
   (fun l1 l2 : list (list A) =>
    forall a : list A, In a l1 -> ~ In a l2)) (additions x).
Admitted.

Theorem permutations_NoDup l:
  NoDup l -> NoDup (permutations l).
Proof.
  intros H. induction H.
  - constructor; [apply in_nil|constructor].
  - cbn. rewrite flat_map_concat_map. apply NoDup_concat.
    + apply Forall_forall. intros xl Hxl%in_map_iff.
      destruct Hxl as [l' [H1 H2%permutations_spec]]. subst xl.
      apply additions_NoDup; now rewrite <- H2.
    + apply (Pairwise_map (fun l1 l2 => (~ In x l1 /\ ~ In x l2) /\ l1 <> l2)).
      * apply additions_Proper.
      * apply Pairwise_and.
        -- apply Pairwise_and.
           ++ apply Forall_Pairwise1, Forall_forall.
              intros l' Hl%permutations_spec. rewrite <- Hl. assumption.
           ++ apply Forall_Pairwise2, Forall_forall.
              intros l' Hl%permutations_spec. rewrite <- Hl. assumption.
        -- apply Pairwise_NoDup. assumption.
Qed.

End permutations.