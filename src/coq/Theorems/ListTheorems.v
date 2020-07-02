Require Import CPidgin.Data.List.
Require Import CPidgin.Data.Maybe.

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
    forall (A : Type) (x : Maybe A) (xs : List A),
        head (x :: xs) = x.
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
    forall (A : Type) (x : Maybe A) (xs : List A),
        tail (x :: xs) = xs.
Proof.
    intros.
    unfold tail.
    trivial.
Qed.
