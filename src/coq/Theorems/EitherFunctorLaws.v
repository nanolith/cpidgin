Require Import CPidgin.Control.Functor.
Require Import CPidgin.Data.Either.

(* Helper function to act as an id function. *)
Definition id' {A : Type} (x : A): A :=
    x.

(* Functor Law 1: Identity. *)
Lemma EitherFunctorPreservesIdentityMorphisms:
    forall (E A : Type) (x : Either E A),
        id' <$> x = x.
Proof.
    intros.
    unfold fmap.
    unfold eitherFunctor.
    unfold id'.
    destruct x.
    trivial.
    trivial.
Qed.

(* Functor Law 2: Composition. *)
Lemma EitherFunctorPreservesCompositionsOfMorphisms:
    forall (E A B C : Type) (x : Either E A) (f : A -> B) (g : B -> C),
        (fun a => g (f a)) <$> x
            = g <$> (f <$> x).
Proof.
    intros.
    unfold fmap.
    unfold eitherFunctor.
    destruct x.
    trivial.
    trivial.
Qed.
