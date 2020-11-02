Require Import CPidgin.Control.Monad.
Require Import CPidgin.Data.Either.

Module EitherMonadLaws.

Import Either.Either.
Import Monad.

(* Monad Law 1: Left Identity. *)
Lemma EitherMonadLeftIdentity:
    forall (E A B : Type) (x : A) (f : A -> Either E B),
        mret x >>= f = f x.
Proof.
    intros.
    unfold mret.
    unfold bind.
    unfold eitherMonad.
    trivial.
Qed.

(* Monad Law 2: Right Identity. *)
Lemma EitherMonadRightIdentity:
    forall (E A : Type) (m : Either E A),
        m >>= mret = m.
Proof.
    intros.
    unfold mret.
    unfold bind.
    unfold eitherMonad.
    destruct m.
    trivial.
    trivial.
Qed.

(* Monad Law 3: Associativity. *)
Lemma EitherMonadAssociativity:
    forall (E A B C : Type) (m : Either E A) (f : A -> Either E B)
           (g : B -> Either E C),
        (m >>= f) >>= g
            = m >>= (fun x => (f x >>= g)).
Proof.
    intros.
    unfold bind.
    unfold eitherMonad.
    destruct m.
    trivial.
    trivial.
Qed.

End EitherMonadLaws.
