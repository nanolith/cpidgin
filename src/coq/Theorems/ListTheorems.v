Require Import CPidgin.Data.List.
Require Import CPidgin.Data.Maybe.
Require Import CPidgin.Data.Semigroup.
Require Import Coq.Arith.Compare_dec.
Require Import PeanoNat.

Module ListTheorems.

Import Maybe.
Import List.
Import Semigroup.

(* head of [] returns Nothing. *)
Lemma list_head_nil_none:
    forall (A : Type),
        head ([] : List A) = Nothing.
Proof.
    intros.
    unfold head.
    trivial.
Qed.

(* head of x :: xs returns x. *)
Lemma list_head_cons:
    forall (A : Type) (x : A) (xs : List A),
        head (x :: xs) = Just x.
Proof.
    intros.
    unfold head.
    trivial.
Qed.

(* tail of [] is []. *)
Lemma list_tail_nil:
    forall (A : Type),
        tail ([] : List A) = [].
Proof.
    intros.
    unfold tail.
    trivial.
Qed.

(* tail of x :: xs is xs. *)
Lemma list_tail_cons:
    forall (A : Type) (x : A) (xs : List A),
        tail (x :: xs) = xs.
Proof.
    intros.
    unfold tail.
    trivial.
Qed.

(* helper to create a duplicate list of a given size. *)
Fixpoint dupList {A : Type} (n : nat) (m : A) (ls : List A) : List A :=
    match n with
        | 0 => ls
        | S n' => m :: dupList n' m ls
    end.

(* proof that we can unroll drop by 1. *)
Lemma list_drop_unroll:
    forall (A : Type) (n : nat) (x : A) (xs : List A),
        drop (S n) (x :: xs) = drop n xs.
Proof.
    intros.
    unfold drop.
    trivial.
Qed.

(* proof that we can unroll dupList by 1. *)
Lemma list_dupList_unroll:
    forall (A : Type) (n : nat) (x : A) (xs : List A),
        dupList (S n) x xs = x :: dupList n x xs.
Proof.
    intros.
    unfold dupList.
    trivial.
Qed.

(* proof that drop n drops n values from a list. *)
Lemma list_drop:
    forall (A : Type) (n : nat) (x : A) (xs : List A),
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
    forall (A : Type) (l : List A) (m : A),
        length (m :: l) = S (length l).
Proof.
    intros.
    unfold length.
    trivial.
Qed.

(* Proof that append and cons are commutative. *)
Lemma list_append_cons_commute:
    forall (A : Type) (l1 l2 : List A) (m : A),
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
    forall (A : Type) (l1 l2 : List A),
        length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros.
    induction l1.
    1: {
        unfold append.
        unfold length.
        trivial.
    }
    1: {
        rewrite list_append_cons_commute.
        rewrite list_length_unroll.
        rewrite list_length_unroll.
        rewrite IHl1.
        rewrite nat_succ_plus_assoc.
        trivial.
    }
Qed.

(* Proof that dropping the length of a list results in an empty list. *)
Lemma list_drop_length_empty:
    forall (A : Type) (l : List A),
        drop (length l) l = [].
Proof.
    intros.
    induction l.
    1: {
        unfold length.
        unfold drop.
        trivial.
    }
    1: {
        rewrite list_length_unroll.
        rewrite list_drop_unroll.
        rewrite IHl.
        trivial.
    }
Qed.

(* Proof that we can append two lists, drop the first list, and get the second
   list. *)
Lemma list_drop_append_length:
    forall (A : Type) (l1 l2 : List A),
        drop (length l1) (l1 ++ l2) = l2.
Proof.
    intros.
    induction l1.
    1: {
        unfold length.
        unfold drop.
        unfold append.
        trivial.
    }
    1: {
        rewrite list_length_unroll.
        rewrite list_append_cons_commute.
        rewrite list_drop_unroll.
        rewrite IHl1.
        trivial.
    }
Qed.

(* Proof that we can unroll take. *)
Lemma list_take_unroll:
    forall (A : Type) (l : List A) (m : A) (n : nat),
        take (S n) (m :: l) = m :: take n l.
Proof.
    intros.
    unfold take.
    trivial.
Qed.

(* Proof that taking the length from a list is that list. *)
Lemma list_take_length:
    forall (A : Type) (l : List A),
        take (length l) l = l.
Proof.
    intros.
    induction l.
    1: {
        unfold length.
        unfold take.
        trivial.
    }
    1: {
        rewrite list_length_unroll.
        rewrite list_take_unroll.
        rewrite IHl.
        trivial.
    }
Qed.

(* Proof that we can take the first list from apending two lists. *)
Lemma list_append_take:
    forall (A : Type) (l1 l2 : List A),
        take (length l1) (l1 ++ l2) = l1.
Proof.
    intros.
    induction l1.
    1: {
        unfold length.
        unfold append.
        unfold take.
        trivial.
    }
    1: {
        rewrite list_append_cons_commute.
        rewrite list_length_unroll.
        rewrite list_take_unroll.
        rewrite IHl1.
        trivial.
    }
Qed.

(* Proof that we can unroll nth. *)
Definition list_nth_unroll:
    forall (A : Type) (n : nat) (l : List A) (m : A),
        nth (S n) (m :: l) = nth n l.
Proof.
    intros.
    unfold nth.
    rewrite list_drop_unroll.
    destruct n.
    unfold drop.
    trivial.
    trivial.
Qed.

(* Proof that we can take the nth item from an arbitrary list. *)
Definition list_nth_append_concat:
    forall (A : Type) (l1 l2 : List A) (m : A),
        nth (length l1) (l1 ++ (m :: l2)) = Just m.
Proof.
    intros.
    unfold nth.
    destruct l1.
    unfold length.
    unfold append.
    unfold head.
    trivial.
    rewrite list_length_unroll.
    rewrite list_append_cons_commute.
    rewrite list_drop_unroll.
    rewrite list_drop_append_length.
    unfold head.
    trivial.
Qed.

(* Proof that we can unroll removeNth by one. *)
Lemma list_remove_nth_unroll:
    forall (A : Type) (n : nat) (l : List A) (m : A),
        removeNth (S n) (m :: l) = m :: removeNth n l.
Proof.
    intros.
    unfold removeNth.
    trivial.
Qed.

(* Proof that we can remove an element from a list. *)
Lemma list_remove_nth:
    forall (A : Type) (l1 l2 : List A) (m : A),
        removeNth (length l1) (l1 ++ (m :: l2)) = l1 ++ l2.
Proof.
    intros.
    induction l1.
    unfold length.
    unfold removeNth.
    unfold tail.
    unfold append.
    trivial.
    rewrite list_length_unroll.
    rewrite list_append_cons_commute.
    rewrite list_append_cons_commute.
    rewrite list_remove_nth_unroll.
    rewrite IHl1.
    trivial.
Qed.

(* Proof that removing the nth element from an empty list returns the empty
   list. *)
Lemma list_remove_nth_empty:
    forall (A : Type) (n : nat),
        removeNth n ([] : List A) = [].
Proof.
    intros.
    unfold removeNth.
    destruct n.
    unfold tail.
    trivial.
    trivial.
Qed.

(* Proof that a list can be destructed as a left append of an empty list and
   itself. *)
Lemma list_empty_left_append:
    forall (A : Type) (l : List A),
        l = [] ++ l.
Proof.
    intros.
    unfold append.
    trivial.
Qed.

(* Proof that a list can be destructed as a right append of an empty list and
   itself. *)
Lemma list_empty_right_append:
    forall (A : Type) (l : List A),
        l = l ++ [].
Proof.
    intros.
    induction l.
    unfold append.
    trivial.
    rewrite list_append_cons_commute.
    rewrite <- IHl.
    trivial.
Qed.

(* Proof that list append follows the Semigroup Associativity Law. *)
Lemma list_append_semigroup_associativity:
    forall (A : Type) (x y z : List A),
        (x <o> y) <o> z = x <o> (y <o> z).
Proof.
    intros.
    unfold op.
    unfold listSemigroup.
    unfold append.
    induction x.
    induction y.
    induction z.
    trivial.
    trivial.
    trivial.
    rewrite IHx.
    trivial.
Qed.

End ListTheorems.
