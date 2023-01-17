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

Section words.
Variable A: Type.
Variable alphabet: list A.
Notation word := (list A).

Definition combine_one_letter (words: list word) : list word :=
  flat_map (fun w: word => map (fun x => x::w) alphabet) words.

Lemma combine_one_letter_length words:
  length (combine_one_letter words) = length words * length alphabet.
Proof.
  induction words; [reflexivity | simpl].
  rewrite app_length, map_length. f_equal.
  assumption.
Qed.

(* Nat.iter n combine_one_letter *)
Fixpoint combine_n_letters n (words : list word) := 
match n with
| 0 => words
| S n => combine_n_letters n (combine_one_letter words)
end.

Lemma combine_n_letters_length n words:
  length (combine_n_letters n words) = length words * (length alphabet)^n.
Proof.
  revert words. induction n.
  - cbn. symmetry. apply Nat.mul_1_r.
  - intro words. cbn.
    rewrite IHn, combine_one_letter_length.
    symmetry. apply Nat.mul_assoc.
Qed.

End words.