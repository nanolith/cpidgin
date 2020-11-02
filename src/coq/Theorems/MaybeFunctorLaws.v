Require Import CPidgin.Control.Functor.
Require Import CPidgin.Data.Maybe.

Module MaybeFunctorLaws.

Import Functor.
Import Maybe.Maybe.

(* Helper function to act as an id function. *)
Definition id' {A : Type} (x : A): A :=
    x.

(* Functor Law 1: Identity. *)
Lemma MaybeFunctorPreservesIdentityMorphisms:
    forall (A : Type) (x : Maybe A),
        id' <$> x = x.
Proof.
    intros.
    unfold fmap.
    unfold maybeFunctor.
    unfold id'.
    destruct x.
    trivial.
    trivial.
Qed.

(* Functor Law 2: Composition. *)
Lemma MaybeFunctorPreservesCompositionOfMorphisms:
    forall (A B C : Type) (x : Maybe A) (f : A -> B) (g : B -> C),
        (fun a => g (f a)) <$> x
            = g <$> (f <$> x).
Proof.
    intros.
    unfold fmap.
    unfold maybeFunctor.
    destruct x.
    trivial.
    trivial.
Qed.

End MaybeFunctorLaws.
