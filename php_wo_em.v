
(*
  Author: Ching-Tsun Chou (chingtsun.chou@gmail.com)
  Copyright (c) 2017-2019 Ching-Tsun Chou. All rights reserved.
  Released under MIT license as described in: https://opensource.org/licenses/MIT

  The following code was developed using Coq 8.6.1.
*)

Require Import Bool Arith List Omega.

Lemma nat_in_dec :
  forall (n : nat) (l : list nat), {(In n l)} + {~(In n l)}.
Proof.
  apply in_dec.
  apply Nat.eq_dec.
Qed.

Fixpoint remove_nth {X : Type} (n : nat) (l : list X) : list X :=
  match n, l with
  | O, nil => nil
  | O, x :: t => t
  | S m, nil => nil
  | S m, x :: t => x :: (remove_nth m t)
  end.

Lemma remove_nth_length_cons :
  forall (X : Type) (l : list X) (x : X),
    length (remove_nth (length l) (x :: l)) = length l.
Proof.
  intros X; induction l as [| a l' IHl']; simpl; intros x.
  - reflexivity.
  - rewrite (IHl' a). reflexivity.
Qed.

Lemma remove_nth_length :
  forall (X : Type) (l : list X) (n : nat),
    n < length l -> length (remove_nth n l) = pred (length l).
Proof.
  intros X; induction l; simpl; intros n H1.
  - omega.
  - assert ((n < length l) \/ (n = length l)) as H2.
    { omega. }
    destruct H2 as [H3 | H3].
    + destruct n as [| n']; simpl; try reflexivity.
      assert (n' < length l) as H4.
      { omega. }
      apply IHl in H4.
      rewrite H4. omega.
    + rewrite H3. rewrite remove_nth_length_cons. reflexivity.
Qed.

Lemma remove_nth_in :
  forall (X : Type) (d : X) (l : list X) (n1 n2 : nat),
    n1 < length l -> n2 < length l -> (n1 <> n2) -> In (nth n1 l d) (remove_nth n2 l).
Proof.
  intros X d; induction l as [| h t IHt]; simpl; intros n1 n2 H1 H2 H3.
  - omega.
  - destruct n1 as [| n1']; destruct n2 as [| n2']; simpl.
    + omega.
    + intuition.
    + apply nth_In. omega.
    + right. apply IHt; omega.
Qed.

Lemma In_nth_list :
  forall (X : Type) (d : X) (l1 l2 : list X),
    (forall x : X, In x l1 -> In x l2) ->
    (exists ln : list nat, length ln = length l1 /\
                           (forall n, n < length l1 -> nth n ln 0 < length l2 /\
                                                       nth n l1 d = nth (nth n ln 0) l2 d)).
Proof.
  intros X d; induction l1 as [| x1 l1' IHl1']; simpl; intros l2 H1.
  - exists nil. split; try reflexivity.
    intros n. omega.
  - assert (In x1 l2) as H2.
    { intuition. }
    assert (forall x, In x l1' -> In x l2) as H3.
    { intuition. }
    apply (In_nth l2 x1 d) in H2. destruct H2 as [n1 [H2a H2b]].
    apply (IHl1' l2) in H3. destruct H3 as [ln' [H3a H3b]].
    exists (n1 :: ln'). rewrite <- H3a. split; try reflexivity.
    destruct n as [| n']; simpl.
    + intuition.
    + intros H4. apply H3b. omega.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
| repeats_1 : forall x l, (In x l) -> repeats (x::l)
| repeats_2 : forall x l, repeats l -> repeats (x::l).

Theorem PHP :
  forall (X:Type) (l1 l2:list X),
    (forall x, In x l1 -> In x l2) -> length l2 < length l1 -> repeats l1.
Proof.
  intros X; induction l1 as [| x1 l1' IHl1']; simpl; intros l2 H1 H2.
  - omega.
  - assert (In x1 l2) as H3.
    { intuition. }
    assert (forall x : X, In x l1' -> In x l2) as H4.
    { intuition. }
    apply (In_nth l2 x1 x1) in H3. destruct H3 as [n1 [H3a H3b]].
    apply (In_nth_list X x1 l1' l2) in H4. destruct H4 as [ln1 [H4a H4b]].
    pose proof (nat_in_dec n1 ln1) as H5; destruct H5 as [H5 | H5].
    + apply (In_nth ln1 n1 0) in H5. destruct H5 as [n1' [H5a H5b]].
      rewrite H4a in H5a. pose proof (H4b n1' H5a) as [H6a H6b].
      rewrite H5b in H6b. rewrite H3b in H6b.
      apply repeats_1. rewrite <- H6b. apply nth_In. intuition.
    + apply repeats_2. apply (IHl1' (remove_nth n1 l2)).
      * intros x1' H1'.
        apply (In_nth l1' x1' x1) in H1'. destruct H1' as [n1' [H1'a H1'b]].
        pose proof (H4b n1' H1'a) as [H6a H6b]. rewrite H1'b in H6b. rewrite H6b.
        apply remove_nth_in; try assumption.
        intros H7. rewrite <- H4a in H1'a. apply (@nth_In nat n1' ln1 0) in H1'a.
        rewrite H7 in H1'a. intuition.
      * pose proof (remove_nth_length X l2 n1 H3a) as H6. rewrite H6. omega.
Qed.
