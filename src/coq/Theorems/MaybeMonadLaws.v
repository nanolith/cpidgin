Require Import CPidgin.Control.Monad.
Require Import CPidgin.Data.Maybe.

(* Monad Law 1: Left Identity. *)
Lemma Monad_Maybe_Law1:
    forall (A B : Type) (x : A) (f : A -> Maybe B),
        mret x >>= f
            = f x.
Proof.
    intros.
    unfold mret.
    unfold maybeMonad.
    unfold bind.
    trivial.
Qed.

(* Monad Law 2: Right Identity. *)
Lemma Monad_Maybe_Law2:
    forall (A : Type) (m : Maybe A),
        m >>= mret
            = m.
Proof.
    intros.
    unfold mret.
    unfold maybeMonad.
    unfold bind.
    induction m.
    trivial.
    trivial.
Qed.

(* Monad Law 3: Associativity. *)
Lemma Monad_Maybe_Law3:
    forall (A B C : Type) (m : Maybe A) (f : A -> Maybe B) (g : B -> Maybe C),
        (m >>= f) >>= g =
            m >>= (fun x => (f x >>= g)).
Proof.
    intros.
    unfold bind.
    unfold maybeMonad.
    induction m.
    trivial.
    trivial.
Qed.
