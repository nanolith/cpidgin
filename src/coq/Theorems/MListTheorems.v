Require Import CPidgin.Data.MList.
Require Import CPidgin.Data.Maybe.

(* head of [] returns Nothing. *)
Lemma list_head_nil_none:
    forall (A : Type),
        head ([] : MList A) = Nothing.
Proof.
    intros.
    unfold head.
    trivial.
Qed.

(* head of x :: xs returns x. *)
Lemma list_head_cons:
    forall (A : Type) (x : Maybe A) (xs : MList A),
        head (x :: xs) = x.
Proof.
    intros.
    unfold head.
    trivial.
Qed.

(* tail of [] is []. *)
Lemma list_tail_nil:
    forall (A : Type),
        tail ([] : MList A) = [].
Proof.
    intros.
    unfold tail.
    trivial.
Qed.

(* tail of x :: xs is xs. *)
Lemma list_tail_cons:
    forall (A : Type) (x : Maybe A) (xs : MList A),
        tail (x :: xs) = xs.
Proof.
    intros.
    unfold tail.
    trivial.
Qed.

(* helper to create a duplicate list of a given size. *)
Fixpoint dupList {A : Type} (n : nat) (m : Maybe A) (ls : MList A) : MList A :=
    match n with
        | 0 => ls
        | S n' => m :: dupList n' m ls
    end.

(* proof that we can unroll drop by 1. *)
Lemma list_drop_unroll:
    forall (A : Type) (n : nat) (x : Maybe A) (xs : MList A),
        drop (S n) (x :: xs) = drop n xs.
Proof.
    intros.
    unfold drop.
    trivial.
Qed.

(* proof that we can unroll dupList by 1. *)
Lemma list_dupList_unroll:
    forall (A : Type) (n : nat) (x : Maybe A) (xs : MList A),
        dupList (S n) x xs = x :: dupList n x xs.
Proof.
    intros.
    unfold dupList.
    trivial.
Qed.

(* proof that drop n drops n values from a list. *)
Lemma list_drop:
    forall (A : Type) (n : nat) (x : Maybe A) (xs : MList A),
        drop n (dupList n x xs) = xs.
Proof.
    intros.
    induction n.
    1: {
        unfold drop.
        unfold dupList.
        trivial.
    }
    1: {
        rewrite list_dupList_unroll.
        rewrite list_drop_unroll.
        rewrite IHn.
        trivial.
    }
Qed.

(* Proof that we can unroll length by one. *)
Lemma list_length_unroll:
    forall (A : Type) (l : MList A) (m : Maybe A),
        length (m :: l) = S (length l).
Proof.
    intros.
    unfold length.
    trivial.
Qed.

(* Proof that append and cons are commutative. *)
Lemma list_append_cons_commute:
    forall (A : Type) (l1 l2 : MList A) (m : Maybe A),
        (m :: l1) ++ l2 = m :: (l1 ++ l2).
Proof.
    intros.
    unfold append.
    trivial.
Qed.

(* Proof that succ is associative wrt addition. *)
Lemma nat_succ_plus_assoc:
    forall (n1 n2 : nat),
        S (n1 + n2) = S n1 + n2.
Proof.
    intros.
    unfold plus.
    trivial.
Qed.

(* Proof that the length of two lists appended is the same as their lengths
   added. *)
Lemma list_length_append:
    forall (A : Type) (l1 l2 : MList A),
        length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros.
    induction l1.
    unfold append.
    unfold length.
    trivial.
    rewrite list_append_cons_commute.
    rewrite list_length_unroll.
    rewrite list_length_unroll.
    rewrite IHl1.
    rewrite nat_succ_plus_assoc.
    trivial.
Qed.

(* Proof that we can unroll drop. *)
Lemma list_drop_unroll:
    forall (A : Type) (l : MList A) (m : Maybe A) (n : nat),
        drop (S n) (m :: l) = drop n l.
Proof.
    intros.
    unfold drop.
    unfold tail.
    trivial.
Qed.

(* Proof that dropping the length of a list results in an empty list. *)
Lemma list_drop_length_empty:
    forall (A : Type) (l : MList A),
        drop (length l) l = [].
Proof.
    intros.
    induction l.
    unfold length.
    unfold drop.
    trivial.
    rewrite list_length_unroll.
    rewrite list_drop_unroll.
    rewrite IHl.
    trivial.
Qed.

(* Proof that we can append two lists, drop the first list, and get the second
   list. *)
Lemma lst_drop_append_length:
    forall (A : Type) (l1 l2 : MList A),
        drop (length l1) (l1 ++ l2) = l2.
Proof.
    intros.
    induction l1.
    unfold length.
    unfold drop.
    unfold append.
    trivial.
    rewrite list_length_unroll.
    rewrite list_append_cons_commute.
    rewrite list_drop_unroll.
    rewrite IHl1.
    trivial.
Qed.
