Require Import CPidgin.Control.Functor.
Require Import CPidgin.Data.Either.

(* Helper function to act as an id function. *)
Definition fid {A : Type} (x : A): A :=
    x.

(* Functor Law 1: Identity. *)
Lemma Functor_Either_Law1:
    forall (E A : Type) (x : Either E A),
        fid <$> x = x.
Proof.
    intros.
    unfold fmap.
    unfold eitherFunctor.
    unfold fid.
    induction x.
    trivial.
    trivial.
Qed.

(* Functor Law 2: Composition. *)
Lemma Functor_Either_Law2:
    forall (E A B C : Type) (x : Either E A) (f : A -> B) (g : B -> C),
        (fun a => g (f a)) <$> x
            = g <$> (f <$> x).
Proof.
    intros.
    unfold fmap.
    unfold eitherFunctor.
    induction x.
    trivial.
    trivial.
Qed.
