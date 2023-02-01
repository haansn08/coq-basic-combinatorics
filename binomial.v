Require Import List Bool.
Import ListNotations.

Definition word := list bool.

Inductive binomial: nat -> word -> Prop :=
| binomial_nil: binomial 0 []
| binomial_true: forall k w, binomial k w -> binomial (S k) (true::w)
| binomial_false: forall k w, binomial k w -> binomial k (false::w).

Lemma binomial_spec:
  forall k w, binomial k w <-> count_occ bool_dec w true = k.
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

Fixpoint binomials n k :=
match n, k with
| 0, 0 => [[]]
| 0, _ => []
| _, 0 => [ repeat false n ]
| S n', S k' => map (cons true) (binomials n' k') 
             ++ map (cons false) (binomials n' k) 
end.

Compute binomials 4 2.

Lemma In_singleton [A : Type] (x y : A):
  In x [y] <-> y = x.
Proof.
  split; intro H.
  - destruct H; [assumption | contradiction H].
  - subst y. constructor. reflexivity.
Qed.

Lemma binomial_falses:
  forall n, binomial 0 (repeat false n).
Proof.
  induction n.
  - constructor.
  - cbn. constructor. assumption.
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

Lemma In_map_cons_elim [A: Type] (a : A) l ls:
  In l (map (cons a) ls) -> exists l', l=a::l' /\ In l' ls.
Proof.
  intros H%in_map_iff. destruct H as [l' [<- H]].
  exists l'. tauto.
Qed.

Lemma In_map_cons [A: Type] (a : A) l ls:
  In l ls -> In (a::l) (map (cons a) ls).
Proof. intro H. apply in_map_iff. exists l. tauto. Qed.

Lemma binomials_cons_true n k w:
  In (true::w) (binomials (S n) (S k)) <-> In w (binomials n k).
Proof.
  split; intro H.
  - cbn in H. apply in_app_or in H as [];
    apply In_map_cons_elim in H as [w' [H0 H1]].
    + injection H0 as ->. assumption.
    + discriminate H0.
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
  - cbn in H. apply in_app_or in H as [];
    apply In_map_cons_elim in H as [w' [H0 H1]].
    + discriminate H0.
    + injection H0 as ->. assumption.
  - cbn. apply in_or_app. right. apply In_map_cons. exact H.
Qed.

Lemma binomials_length w n k:
  In w (binomials n k) -> length w = n.
Proof.
  intro H. destruct k.
  - apply binomials_falses in H. subst. apply repeat_length.
  - revert H. revert k w. induction n.
    + intros k w H. contradiction H.
    + intros k w H. cbn in H. apply in_app_or in H. destruct H.
      * apply In_map_cons_elim in H as [l' [H0 H1]].
        rewrite H0. cbn. f_equal. eapply IHn.
Abort.

Lemma binomials_correct n k w:
  In w (binomials n k) <-> length w = n /\ binomial k w.
Proof.
  split.
  - intros H. split.
    + 
Abort.