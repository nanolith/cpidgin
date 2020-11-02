Require Import CPidgin.Control.Monad.
Require Import CPidgin.Data.Maybe.

Module MaybeMonadLaws.

Import Maybe.Maybe.
Import Monad.

(* Monad Law 1: Left Identity. *)
Lemma MaybeMonadLeftIdentity:
    forall (A B : Type) (x : A) (f : A -> Maybe B),
        mret x >>= f
            = f x.
Proof.
    intros.
    unfold mret.
    unfold bind.
    unfold maybeMonad.
    trivial.
Qed.

(* Monad Law 2: Right Identity. *)
Lemma MaybeMonadRightIdentity:
    forall (A : Type) (m : Maybe A),
        m >>= mret
            = m.
Proof.
    intros.
    unfold mret.
    unfold bind.
    unfold maybeMonad.
    destruct m.
    trivial.
    trivial.
Qed.

(* Monad Law 3: Associativity. *)
Lemma MaybeMonadAssociativity:
    forall (A B C : Type) (m : Maybe A) (f : A -> Maybe B) (g : B -> Maybe C),
        (m >>= f) >>= g =
            m >>= (fun x => (f x >>= g)).
Proof.
    intros.
    unfold bind.
    unfold maybeMonad.
    destruct m.
    trivial.
    trivial.
Qed.

End MaybeMonadLaws.
