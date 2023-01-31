Require Import List Bool Arith.
Require Import Lia.
Import ListNotations.

Definition word := list bool.

Inductive dyck: word -> Prop :=
| dyck_nil: dyck nil
| dyck_shift: forall w, dyck w -> dyck (true::w++[false])
| dyck_app: forall w1, dyck w1 -> forall w2, dyck w2 -> dyck (w1 ++ w2).

Goal dyck [true; false; true; true; true; false; false; true; false; false].
Proof. 
  apply (dyck_app [_;_]).
  - apply (dyck_shift []), dyck_nil.
  - apply (dyck_shift [_;_;_;_;_;_]), (dyck_app [_;_;_;_]).
    + apply (dyck_shift [_;_]), (dyck_shift []), dyck_nil.
    + apply (dyck_shift []). apply dyck_nil.
Qed.

Lemma length_cons_ends [A: Type] (x y: A) (l: list A):
  length (x::l++[y]) = S (S (length l)).
Proof. cbn. rewrite app_length. cbn. lia. Qed.

Lemma dyck_even:
  forall w, dyck w -> Nat.Even (length w).
Proof.
  intros w D. induction D. (* good example for not inducting on w *)
  - exists 0. reflexivity.
  - rewrite length_cons_ends. apply Nat.Even_succ_succ. assumption.
  - rewrite app_length. apply Nat.Even_Even_add; assumption.
Qed.