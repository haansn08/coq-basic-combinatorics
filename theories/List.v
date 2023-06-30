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

Lemma ForallOrdPairs_inv [A] (P: A -> A -> Prop) x l:
  ForallOrdPairs P (x::l) -> Forall (P x) l.
Proof. intros H. inversion H. assumption. Qed.

Lemma ForallOrdPairs_inv_tail [A] (P: A -> A -> Prop) x l:
  ForallOrdPairs P (x::l) -> ForallOrdPairs P l.
Proof. intros H. inversion H. assumption. Qed.

Lemma ForallOrdPairs_singleton [A] (P: A -> A -> Prop) x:
  ForallOrdPairs P [x].
Proof. constructor; constructor. Qed.

Lemma ForallOrdPairs_and [A] (P Q: A -> A -> Prop) l:
  ForallOrdPairs P l -> ForallOrdPairs Q l ->
  ForallOrdPairs (fun a b => P a b /\ Q a b) l.
Proof.
  intros Hp Hq. induction l as [|a l IH]; constructor.
  - apply Forall_and.
    + apply ForallOrdPairs_inv in Hp. assumption.
    + apply ForallOrdPairs_inv in Hq. assumption.
  - apply IH.
    + apply ForallOrdPairs_inv_tail in Hp. assumption.
    + apply ForallOrdPairs_inv_tail in Hq. assumption.
Qed.

Lemma Forall_indep [A] (P: Prop) (l: list A):
  P -> Forall (fun x => P) l.
Proof. intros p. induction l; constructor; assumption. Qed.

Lemma Forall_ForallOrdPairs_l [A] (P: A -> Prop) l:
  Forall P l -> ForallOrdPairs (fun a b => P a) l.
Proof.
intro H. induction H; constructor.
- apply Forall_indep. assumption.
- assumption.
Qed.

Lemma Forall_ForallOrdPairs_r [A] (P: A -> Prop) l:
  Forall P l -> ForallOrdPairs (fun a b => P b) l.
Proof. intro H. induction H; constructor; assumption. Qed.

Lemma ForallOrdPairs_NoDup [A] (l: list A):
  ForallOrdPairs (fun a b => a <> b) l <-> NoDup l.
Proof.
  split; intro H.
  - induction H; constructor.
    + rewrite Forall_forall in H. intro E.
      contradiction (H a E). reflexivity.
    + assumption.
  - induction H; constructor.
    + apply Forall_forall. intros y Hy ->.
      contradiction.
    + assumption.
Qed.

Lemma app_self_nil [A] (l1 l2: list A):
  l1 = l1 ++ l2 -> l2 = [].
Proof.
  intro H. induction l1.
  - rewrite H. reflexivity.
  - inversion H. apply IHl1. assumption.
Qed.

Lemma ForallOrdPairs_map [A B] P Q (f: A -> B) l:
  Proper (P ==> Q) f -> ForallOrdPairs P l -> ForallOrdPairs Q (map f l).
Proof.
  intros Hpq Hp. induction Hp; [constructor|].
  cbn. constructor.
  - apply Forall_map. eapply Forall_impl.
    + apply Hpq.
    + assumption.
  - assumption.
Qed.

Lemma concat_self_false [A] (l : list (list A)):
  ~ In (concat l) l.
Proof. Abort.
(* counterexample: l = [[1],[],[]] *)

Lemma NoDup_concat [A] (L: list (list A)):
  Forall (@NoDup _) L ->
  ForallOrdPairs (fun l1 l2 => forall a, In a l1 -> ~ In a l2) L ->
  NoDup (concat L).
Proof.
  intros H1 H2. induction L as [|l1]; [constructor|].
  cbn. apply NoDup_app.
  - apply Forall_inv in H1. assumption.
  - apply IHL.
    + apply Forall_inv_tail in H1. assumption.
    + inversion H2. assumption.
  - intros a aInl1 ainL%in_concat. destruct ainL as [l2 [l2inL ainL2]].
    eapply ForallOrdPairs_inv in H2.
    rewrite Forall_forall in H2. eapply H2; eassumption.
Qed.

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

Lemma app_inj_pivot [A] a (lx1 lx2 ly1 ly2: list A):
  ~ In a (lx1) -> ~ In a (ly1) ->
  lx1++a::lx2 = ly1++a::ly2 -> lx1 = ly1 /\ lx2 = ly2.
Proof.
  intros Hx Hy H. enough (lx1 = ly1) as C1.
  - subst ly1. split; [reflexivity|].
    apply app_inj_r in H. injection H. trivial.
  - revert Hy H. revert ly1. induction lx1 as [|b lx1 IH].
    + intros. now apply not_in_app_nil in H.
    + apply not_in_cons in Hx as [Hab Hx]. specialize (IH Hx).
      intros ly1 Hy H. destruct ly1 as [|c ly1].
      * contradiction Hab. injection H. easy.
      * injection H. intros H2 <-. f_equal. apply IH.
        -- eapply not_in_cons. exact Hy.
        -- exact H2.
Qed.

Lemma rev_inj [A] (l1 l2: list A):
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intro H. apply (f_equal (@rev _)) in H.
  rewrite !rev_involutive in H. assumption.
Qed.

Lemma app_inj_pivot_tail [A] a (lx1 lx2 ly1 ly2: list A):
  ~ In a (lx2) -> ~ In a (ly2) ->
  lx1++a::lx2 = ly1++a::ly2 -> lx1 = ly1 /\ lx2 = ly2.
Proof.
  intros Hx Hy H. apply (f_equal (@rev _)) in H.
  rewrite !rev_app_distr in H. cbn in H.
  rewrite <- !app_assoc in H. cbn in H.
  apply app_inj_pivot in H as [H1%rev_inj H2%rev_inj].
  - split; assumption.
  - rewrite in_rev in Hx. assumption.
  - rewrite in_rev in Hy. assumption. 
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

