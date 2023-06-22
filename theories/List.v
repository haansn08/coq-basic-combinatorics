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