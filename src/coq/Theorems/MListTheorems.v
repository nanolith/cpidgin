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
