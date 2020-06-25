Require Import CPidgin.Control.Monad.
Require Import CPidgin.Data.Either.

(* Monad Law 1: Left Identity. *)
Lemma Monad_Either_Law1:
    forall (E A B : Type) (x : A) (f : A -> Either E B),
        mret x >>= f = f x.
Proof.
    intros.
    unfold mret.
    unfold eitherMonad.
    unfold bind.
    trivial.
Qed.

(* Monad Law 2: Right Identity. *)
Lemma Monad_Either_Law2:
    forall (E A : Type) (m : Either E A),
        m >>= mret = m.
Proof.
    intros.
    unfold mret.
    unfold eitherMonad.
    unfold bind.
    induction m.
    trivial.
    trivial.
Qed.

(* Monad Law 3: Associativity. *)
Lemma Monad_Either_Law3:
    forall (E A B C : Type) (m : Either E A) (f : A -> Either E B)
           (g : B -> Either E C),
        (m >>= f) >>= g
            = m >>= (fun x => (f x >>= g)).
Proof.
    intros.
    unfold bind.
    unfold eitherMonad.
    induction m.
    trivial.
    trivial.
Qed.
