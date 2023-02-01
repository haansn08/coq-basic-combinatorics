Require Import List Bool Arith.
Require Import Lia.
Import ListNotations.

Definition word := list bool.

Inductive dyck: word -> Prop :=
| dyck_nil: dyck nil
| dyck_shift: forall w, dyck w -> dyck (true::w++[false])
| dyck_app: forall w1, dyck w1 -> forall w2, dyck w2 -> dyck (w1 ++ w2).

Lemma length_cons_ends [A: Type] (x y: A) (l: list A):
  length (x::l++[y]) = S (S (length l)).
Proof. cbn. rewrite last_length. reflexivity. Qed.

Lemma dyck_even w:
  dyck w -> Nat.Even (length w).
Proof.
  intros D. induction D. (* good example for not inducting on w *)
  - exists 0. reflexivity.
  - rewrite length_cons_ends. apply Nat.Even_succ_succ. assumption.
  - rewrite app_length. apply Nat.Even_Even_add; assumption.
Qed.

Lemma dyck_count_eq w:
  dyck w -> count_occ bool_dec w false = count_occ bool_dec w true.
Proof.
  intros D. induction D.
  - reflexivity.
  - cbn. rewrite !count_occ_app. cbn. lia.
  - rewrite !count_occ_app. congruence.
Qed.

Lemma firstn_lt_length [A:Type] (P: list A -> Prop) l:
  (forall n, n < length l -> P (firstn n l)) /\ P l ->
  (forall n, P (firstn n l)).
Proof.
  intros H n. destruct (dec_lt n (length l)) as [Hn|Hn].
  + intuition.
  + apply not_lt in Hn. rewrite firstn_all2; intuition.
Qed.

Lemma dyck_firstn_iff w:
  dyck w <-> forall i, count_occ bool_dec (firstn i w) false
          <= count_occ bool_dec (firstn i w) true.
Proof.
  split; intro H.
  - intro i. apply firstn_lt_length. clear i. split.
    + induction H; intros i Hi.
      * apply Nat.nlt_0_r in Hi. contradiction.
      * rewrite length_cons_ends in Hi. destruct i.
        -- rewrite firstn_O. reflexivity.
        -- rewrite firstn_cons. rewrite <- firstn_removelast.
            ++ rewrite removelast_last. cbn. constructor.
               apply firstn_lt_length. split.
               ** intros i' Hi'. apply IHdyck. assumption.
               ** apply Nat.eq_le_incl. now apply dyck_count_eq.
            ++ rewrite last_length. now apply Nat.succ_lt_mono.
      * rewrite firstn_app, !count_occ_app.
        destruct (lt_dec i (length w1)) as [H1|H2%not_lt].
        -- replace (i - length w1) with 0 by lia. rewrite firstn_O, !Nat.add_0_r.
           apply firstn_lt_length. split.
           ++ apply IHdyck1.
           ++ apply Nat.eq_le_incl. now apply dyck_count_eq.
        -- rewrite firstn_all2 by lia. rewrite dyck_count_eq by assumption.
           apply Nat.add_le_mono_l. apply IHdyck2.
           rewrite app_length in Hi. lia.
    + apply Nat.eq_le_incl. now apply dyck_count_eq.
  - give_up.
Abort.