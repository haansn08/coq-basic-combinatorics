Require Import Arith Morphisms FinFun.
From Coq.Lists Require Export List ListDec.
Export ListNotations.

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

Lemma In_singleton [A : Type] (x y : A):
  In x [y] <-> y = x.
Proof.
  split; intro H.
  - destruct H; [assumption | contradiction H].
  - subst y. constructor. reflexivity.
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

Lemma NoDup_singleton {A : Type} (a: A):
  NoDup [a].
Proof. constructor; [apply in_nil|constructor]. Qed.

Lemma notin_app {A} a (l1 l2 : list A):
  ~ In a l1 -> ~ In a l2 -> ~ In a (l1 ++ l2).
Proof.
  intros H1 H2. induction l1 as [|b l1 IHl1].
  - exact H2.
  - cbn. intros [].
    + apply H1. subst a. apply in_eq.
    + apply not_in_cons in H1 as [].
      apply IHl1; assumption.
Qed.

Lemma NoDup_app [A] (l1 l2 : list A):
  NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros H1 H2 H. induction l1 as [|a l1 IHl1]; [assumption|].
  apply NoDup_cons_iff in H1 as [].
  cbn. constructor.
  - apply notin_app; [assumption|apply H, in_eq].
  - apply IHl1; [assumption|].
    intros. apply H. right. assumption.
Qed.

Inductive Pairwise [A] (P: A -> A -> Prop) : list A -> Prop :=
  Pairwise_nil: Pairwise P []
| Pairwise_cons: forall (x : A) (l : list A),
    Pairwise P l -> (forall y, In y l -> P x y) -> Pairwise P (x::l).

Lemma Pairwise_inv [A] (P: A -> A -> Prop) x l:
  Pairwise P (x::l) -> (forall y, In y l -> P x y).
Proof. intros H. inversion H. assumption. Qed.

Lemma Pairwise_singleton [A] (P: A -> A -> Prop) x:
  Pairwise P [x].
Proof.
  constructor; [constructor|].
  intros y E%in_nil. contradiction.
Qed.

Lemma Pairwise_NoDup [A] (l: list A):
  Pairwise (fun a b => a <> b) l <-> NoDup l.
Proof.
  split; intro H.
  - induction H; constructor.
    + intro Hx. now apply (H0 x).
    + assumption.
  - induction H; constructor.
    + assumption.
    + now intros y Hy ->.
Qed.

Lemma app_self_nil [A] (l1 l2: list A):
  l1 = l1 ++ l2 -> l2 = [].
Proof.
  intro H. induction l1.
  - rewrite H. reflexivity.
  - inversion H. apply IHl1. assumption.
Qed.

Lemma Pairwise_map [A B] P Q (f: A -> B) l:
  Proper (P ==> Q) f -> Pairwise P l -> Pairwise Q (map f l).
Proof.
  intros PfQ HP. induction HP; [constructor|].
  cbn. constructor; [assumption|].
  intros fy Hy%in_map_iff. destruct Hy as [y [<- H1]].
  apply PfQ. apply H. assumption.
Qed.

Lemma concat_self_false [A] (l : list (list A)):
  ~ In (concat l) l.
Proof. Abort.
(* counterexample: l = [[1],[],[]] *)

Lemma NoDup_concat [A] (L: list (list A)):
  Forall (@NoDup _) L ->
  Pairwise (fun l1 l2 => forall a, In a l1 -> ~ In a l2) L ->
  NoDup (concat L).
Proof.
  intros H1 H2. induction L as [|l1]; [constructor|].
  cbn. apply NoDup_app.
  - apply Forall_inv in H1. assumption.
  - apply IHL.
    + apply Forall_inv_tail in H1. assumption.
    + inversion H2. assumption.
  - intros a aInl1 ainL%in_concat. destruct ainL as [l2 [l2inL ainL2]].
    eapply Pairwise_inv in H2.
    + specialize (H2 a). apply H2; [assumption|exact ainL2].
    + assumption.
Qed.

Section ListDec.

Variable A : Type.
Hypothesis dec: forall x y : A, {x=y}+{x<>y}.

(* Coq 8.17? *)
Lemma not_NoDup (l: list A):
    ~ NoDup l -> exists a l1 l2 l3, l = l1++a::l2++a::l3.
Proof using A dec.
intro H0. induction l as [|a l IHl].
- contradiction H0; constructor.
- destruct (ListDec.NoDup_dec dec l) as [H1|H1].
  + destruct (ListDec.In_dec dec a l) as [H2|H2].
    * destruct (in_split _ _ H2) as (l1 & l2 & ->).
      now exists a, nil, l1, l2.
    * now contradiction H0; constructor.
  + destruct (IHl H1) as (b & l1 & l2 & l3 & ->).
    now exists b, (a::l1), l2, l3.
Qed.

End ListDec.

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

Lemma app_inj_r [A] (x y1 y2: list A):
  x ++ y1 = x ++ y2 -> y1 = y2.
Proof.
  intro H. induction x.
  - exact H.
  - apply IHx. injection H. trivial.
Qed.

Lemma not_in_app_nil [A] a (x y z: list A):
  ~ In a y -> a::x = y++z -> y = [].
Proof.
  intros aIny H. destruct y; [reflexivity|].
  exfalso. apply aIny. injection H.
  constructor. symmetry. assumption.
Qed.

Definition InjectiveOn [A B] (P: A -> Prop) (f: A -> B) :=
  forall x y: A, P x -> P y -> f x = f y -> x = y.

Lemma InjectiveOn_map_NoDup [A B] (P: A -> Prop) (f:A->B) (l:list A) :
 InjectiveOn P f -> Forall P l -> NoDup l -> NoDup (map f l).
Proof.
 intros HInj Pl Hl. induction Hl; [constructor|].
 cbn. constructor.
 - intros Hf. apply H. clear H.
   apply in_map_iff in Hf as [y [Heq Hy]]. enough (x = y) as H.
   + rewrite H. assumption.
   + apply HInj.
     * apply Forall_inv in Pl. assumption.
     * apply Forall_inv_tail in Pl. rewrite Forall_forall in Pl.
       apply Pl. assumption.
     * symmetry. assumption.
 - apply IHHl. apply Forall_inv_tail in Pl. assumption.
Qed.

Lemma elts_inj [A] a (lx1 lx2 ly1 ly2: list A):
  ~ In a (lx1) -> ~ In a (ly1) ->
  lx1++a::lx2 = ly1++a::ly2 -> lx1 = ly1 /\ lx2 = ly2.
Proof.
  intros Hx Hy H. enough (lx1 = ly1) as C1.
  - subst ly1. split; [reflexivity|].
    apply app_inj_r in H. injection H. trivial.
  - 
Admitted.

