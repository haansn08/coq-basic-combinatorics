Require Import List Bool.
Import ListNotations.

Definition word := list bool.

Inductive Binomial: nat -> word -> Prop :=
| Binomial_nil: Binomial 0 []
| Binomial_true: forall k w, Binomial k w -> Binomial (S k) (true::w)
| Binomial_false: forall k w, Binomial k w -> Binomial k (false::w).

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

Fixpoint binomials n k :=
match n, k with
| 0, 0 => [[]]
| 0, _ => []
| _, 0 => [ repeat false n ]
| S n', S k' => map (cons true) (binomials n' k') 
             ++ map (cons false) (binomials n' k) 
end.

Lemma In_singleton [A : Type] (x y : A):
  In x [y] <-> y = x.
Proof.
  split; intro H.
  - destruct H; [assumption | contradiction H].
  - subst y. constructor. reflexivity.
Qed.

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

Lemma In_map_cons_elim [A: Type] (a : A) l ls:
  In l (map (cons a) ls) -> exists l', l=a::l' /\ In l' ls.
Proof.
  intros H%in_map_iff. destruct H as [l' [<- H]].
  exists l'. tauto.
Qed.

Lemma In_map_cons [A: Type] (a : A) l ls:
  In l ls -> In (a::l) (map (cons a) ls).
Proof. intro H. apply in_map_iff. exists l. tauto. Qed.

Lemma In_app_map_cons w l1 l2:
  In w (map (cons true) l1 ++ map (cons false) l2) ->
  (exists w', w=true::w' /\ In w' l1) \/ (exists w', w=false::w' /\ In w' l2).
Proof.
  intros H%in_app_or. destruct H as [H1 | H2].
  - left. apply In_map_cons_elim in H1. exact H1.
  - right. apply In_map_cons_elim in H2. exact H2.
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
    + destruct a, k.
      * exfalso. destruct H; [discriminate H|contradiction].
      * apply -> binomials_cons_true in H. cbn; f_equal.
        eapply IHw. exact H.
      * cbn in H. destruct H; [injection H as <-|contradiction].
        cbn; f_equal. apply repeat_length.
      * apply -> binomials_cons_false in H. cbn; f_equal.
        eapply IHw. exact H.
Qed.

Lemma binomials_correct n k w:
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
