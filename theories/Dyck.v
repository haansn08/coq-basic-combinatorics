Require Import List Bool ZArith Permutation.
Require Import Wellfounded Morphisms.
Require Import Lia.
Import ListNotations.

(* already done in
   https://github.com/math-comp/Coq-Combi/blob/master/theories/Combi/Dyckword.v *)

From BasicCombinatorics Require Import Even Binomial.

(* putting this in Set gives us a
   "Case analysis on sort Set is not allowed for inductive definition ex."
*)
Inductive Dyck: word -> Prop :=
| Dyck_nil: Dyck nil
| Dyck_shift: forall w, Dyck w -> Dyck (true::w++[false])
| Dyck_app: forall w1, Dyck w1 -> forall w2, Dyck w2 -> Dyck (w1 ++ w2).

Section level.
Open Scope Z.

Fixpoint level w :=
match w with
| nil => 0
| true::w => (level w) + 1
| false::w => (level w) - 1
end.

Lemma level_app w1 w2:
  level (w1 ++ w2) = (level w1) + (level w2).
Proof.
  induction w1.
  - reflexivity.
  - rewrite <- app_comm_cons. destruct a; cbn; lia.
Qed.

Lemma level_permutation:
  Proper (@Permutation bool ==> eq) level.
Proof.
  intros w w' H. induction H.
  - reflexivity.
  - cbn. rewrite IHPermutation. reflexivity.
  - cbn. destruct x,y; lia.
  - congruence.
Qed.

Corollary level_ends a w b:
  level (a::w++[b]) = level [a;b] + level w.
Proof.
  rewrite <- level_app. apply level_permutation.
  apply perm_skip. symmetry. apply Permutation_cons_append.
Qed.

Coercion Z.of_nat : nat >-> Z.

Lemma level_count w:
   level w = #true w - #false w.
Proof.
  induction w.
  - reflexivity.
  - destruct a; cbn -[Z.of_nat]; lia.
Qed.

Corollary level_count_le_iff w:
  0 <= level w <-> (#false w <= #true w)%nat.
Proof. rewrite level_count. lia. Qed.

Corollary level_count_eq_iff w:
  level w = 0 <-> (#false w = #true w)%nat.
Proof. rewrite level_count. lia. Qed.

Lemma level_firstn_false:
  forall n, -1 <= level (firstn n [false]).
Proof.
  intro n. destruct n.
  - cbn. lia.
  - cbn. rewrite firstn_nil. reflexivity.
Qed.

Lemma dyck_level_firstn w:
  Dyck w -> forall n, 0 <= level (firstn n w).
Proof.
  intros D. induction D; intro n.
  - rewrite firstn_nil. reflexivity.
  - destruct n; [reflexivity|].
    cbn. rewrite firstn_app, level_app.
    pose (level_firstn_false (n - length w)). specialize (IHD n). lia.
  - rewrite firstn_app, level_app.
    specialize (IHD1 n). specialize (IHD2 (n - length w1)%nat). lia.
Qed.

Lemma dyck_level_zero w:
  Dyck w -> level w = 0.
Proof.
  intros D. induction D.
  - reflexivity.
  - rewrite level_ends. assumption.
  - rewrite level_app, IHD1, IHD2. reflexivity.
Qed.

Lemma level_zero_even w:
  level w = 0 -> Even w.
Proof.
  intros H. apply count_eq_even.
  rewrite level_count in H. lia.
Qed.

Lemma list_nil_decidable {A: Type} (l: list A):
  {l = nil} + {l <> nil}.
Proof.
  destruct l.
  - left. reflexivity.
  - right. discriminate.
Qed.

Lemma firstn_add_skipn {A: Type} (l: list A) (n m : nat):
  firstn (n+m)%nat l = firstn n l ++ (firstn m (skipn n l)).
Proof. (* possibly can be done much shorter *)
  destruct (Nat.le_decidable n (length l)) as [H|H].
  - rewrite <- (firstn_skipn n l), firstn_app at 1.
    rewrite firstn_length. rewrite min_l by assumption.
    replace (n + m - n)%nat with m by auto with arith.
    rewrite firstn_firstn. rewrite min_r by apply Nat.le_add_r.
    reflexivity.
  - apply Nat.nle_gt, Nat.lt_le_incl in H.
    rewrite !firstn_all2, skipn_all2 by lia.
    rewrite firstn_nil, app_nil_r. reflexivity.
Qed.

Section level_zero_at.
(* first time we return to ground level *)
Definition level_zero_at w n :=
  (0 < n)%nat /\ level (firstn n w) = 0.

Variable w : word.
Hypothesis Hnil: w <> nil.
Hypothesis Hzero: level w = 0.

Lemma level_zero_at_length:
  level_zero_at w (length w).
Proof.
  split.
  + apply Nat.neq_0_lt_0. intro H.
    apply Hnil,length_zero_iff_nil. assumption.
  + rewrite firstn_all. assumption.
Qed.

Lemma level_zero_at_least:
  has_unique_least_element le (level_zero_at w).
Proof.
  apply dec_inh_nat_subset_has_unique_least_element.
  - intro n. apply Decidable.dec_and.
    + apply Nat.lt_decidable.
    + apply Z.eq_decidable.
  - exists (length w). apply level_zero_at_length.
Qed.

End level_zero_at.

Lemma level_firstn_dyck w:
  level w = 0 ->
  (forall n, (n < length w)%nat -> 0 <= level (firstn n w)) ->
  Dyck w.
Proof.
  (* strong induction over w *)
  induction w as [w IH]
  using (well_founded_induction ((wf_inverse_image _ _ _ (@length _)) lt_wf)).
  (* consider first n where (firstn n w) returns to ground *)
  intros H0 H1.
  destruct (list_nil_decidable w) as [->|Hnil]; [constructor|].
  destruct (level_zero_at_least w Hnil H0) as [n [[[Hn0 Hn] n_min] n_uniq]].
  clear n_uniq.
  (* is it the very end? *)
  destruct (lt_eq_lt_dec n (length w)) as [[H|H]|H].
  - (*no: w if of form Dyck_app *)
    rewrite <- (firstn_skipn n). apply Dyck_app.
    + apply IH; clear IH.
      * rewrite firstn_length_le; auto with arith.
      * assumption.
      * intros k Hk. rewrite firstn_firstn. apply H1. lia.
    + apply IH; clear IH.
      * rewrite skipn_length. lia.
      * rewrite <- (firstn_skipn n w), level_app, Hn in H0. assumption.
      * intros k Hk. specialize (H1 (n + k)%nat).
        rewrite firstn_add_skipn, level_app, Hn in H1. apply H1.
        rewrite skipn_length in Hk. lia.
  - (*yes: w is of the form Dyck_nil or Dyck_shift *)
    subst n.
    apply level_zero_even in H0 as HEven. destruct HEven as [|w' H2 a b].
    + exact Dyck_nil.
    + assert (a = true) as ->. {
        destruct a; [reflexivity|exfalso].
        specialize (H1 1%nat). cut (0 <= -1).
        - lia.
        - apply H1. rewrite length_cons_ends. auto with arith.
      }
      assert (b = false) as ->. {
        destruct b; [exfalso|reflexivity]. clear - H0 H1.
        rewrite level_ends in H0.
        replace (level [true; true]) with 2 in H0 by reflexivity.

        specialize (H1 (1 + length w' + 0)%nat). cbn in H1.
        rewrite firstn_app_2, firstn_O, app_nil_r in H1.
        cut (0 <= level w' + 1).
        - lia.
        - apply H1. rewrite app_length. auto with arith.
      }
      rewrite level_ends in H0.
      apply Dyck_shift. apply IH; clear IH.
      * rewrite length_cons_ends. repeat constructor.
      * exact H0.
      * intros k H.
        destruct (Z.le_decidable 0 (level (firstn k w'))); [assumption|exfalso].
        (* we went to the bottom at k, in contradiction to minimality n *)
        assert (level_zero_at (true::w'++[false]) (S k)). {
          split; [apply Nat.lt_0_succ|]. apply Z.le_antisymm.
          - clear -H H3. cbn. rewrite firstn_app.
            replace (k - length w')%nat with 0%nat by lia.
            rewrite firstn_O, app_nil_r. lia.
          - apply H1. clear -H. rewrite length_cons_ends. lia.
        }
        specialize (n_min (S k) H4). clear -H n_min.
        rewrite length_cons_ends in n_min. lia.
  - exfalso.
    specialize (n_min (length w) (level_zero_at_length w Hnil H0)). lia.
Qed.
End level.

Theorem dyck_firstn_iff w:
  Dyck w <->
  (#false w = #true w) /\
  forall n, n < length w -> #false (firstn n w) <= #true (firstn n w).
Proof.
  split; intro H.
  - split.
    + apply level_count_eq_iff, dyck_level_zero. assumption.
    + intros n Hn. apply level_count_le_iff, dyck_level_firstn. assumption.
  - destruct H as [H1 H2]. apply level_firstn_dyck.
    + apply level_count_eq_iff. assumption.
    + intros n Hn. apply level_count_le_iff, H2, Hn.
Qed.

Require Import FunInd Recdef.

Lemma dyck_factorize w:
  w <> nil -> Dyck w ->
  exists ! w1 w2, Dyck w1 /\ Dyck w2 /\ w = true::w1++[false]++w2.
Proof.
  intros Hnil D. specialize (dyck_level_zero w D) as H0.
  destruct (level_zero_at_least w Hnil H0) as [n [[[Hn0 Hn] n_min] n_uniq]].
Abort.

(* enumerating Dyck words *)
(* from https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Enumerating.20Dyck.20words/near/340729664 *)

(* foldi_nat f x n = f n (f (n-1) .. (f 0 x) ..) *)
Definition foldi_nat {A : Type} (f : nat -> A -> A) (x : A) : nat -> A :=
  fix foldi (n : nat) :=
    f n (match n with
         | O => x
         | S n => foldi n
         end).

Notation "a >>= k" := (concat (map k a)) (at level 40).

Fixpoint dyck (n : nat) : list (list bool) :=
  match n with
  | O => [ [] ]
  | S n =>
    let prev := foldi_nat (fun k etc => dyck k :: etc) [] n in
    combine prev (rev prev) >>= fun '(dyck_k, dyck_n_k) =>
    list_prod dyck_k dyck_n_k >>= fun '(xs, ys) =>
    [true :: xs ++ false :: ys]
  end.
