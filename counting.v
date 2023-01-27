Require Import List ListDec Arith.
Import ListNotations.

Section card.
Variable X : Type.
Variable P: X -> Prop.

Class enum := {
  enumeration: list X;
  enum_spec: forall x, P x <-> In x enumeration;
  enum_nodup: NoDup enumeration
}.
Coercion enumeration: enum >-> list.

Definition count (e: enum) := length enumeration.
Inductive card n := cardI e: count e = n -> card n.

Lemma card_well_defined: forall n m, card n -> card m -> n = m.
Proof.
  intros n m [e1 H1] [e2 H2]. subst n m.
  apply PeanoNat.Nat.le_antisymm.
  - apply NoDup_incl_length.
    + apply enum_nodup.
    + intros x H. apply enum_spec. apply enum_spec in H. exact H.
  - apply NoDup_incl_length.
    + apply enum_nodup.
    + intros x H. apply enum_spec. apply enum_spec in H. exact H.
Qed.

End card.
Arguments enum {X}.
Arguments card {X}.

Definition all X := fun (x:X) => True.

(* ** Counting three things *)
Variant three := a | b | c.
Lemma decThree: forall (x y : three), {x = y} + {x <> y}.
Proof. decide equality. Defined.
#[export] Instance three_enum: enum (all three).
Proof.
  exists (a::b::c::nil).
  - intros []; compute; tauto.
  - apply <- (NoDup_count_occ decThree).
    intros []; reflexivity.
Defined.

Goal card (all three) 3.
Proof. econstructor. reflexivity. Qed.

(* ** Counting combinations of things *)
Fixpoint combinations {A : Type} (l: list A) d :=
match d with
| 0 => [[]]
| S d => map (fun '(x, combination) => x::combination)
             (list_prod l (combinations l d))
end.

Compute combinations three_enum 4.

Lemma combinations_length {A : Type} (l: list A) d:
  length (combinations l d) = (length l)^d.
Proof.
  induction d; [ reflexivity | ].
  cbn. now rewrite map_length, prod_length, IHd.
Qed.
