Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Data.Either.

Module EitherApplicativeLaws.

Import Applicative.
Import Either.Either.

(* Helper function to act as an id function. *)
Definition id' {A : Type} (x : A) : A :=
    x.

(* Applicative Law 1: Identity. *)
Lemma EitherApplicativePreservesIdentityMorphisms:
    forall (E A : Type) (x : Either E A),
        pure id' <*> x = x.
Proof.
    intros.
    unfold id'.
    unfold pure.
    unfold app.
    unfold eitherApplicative.
    destruct x.
    trivial.
    trivial.
Qed.

(* Applicative Law 2: Homomorphism. *)
Lemma EitherApplicativeHomomorphismLaw:
    forall (E A B : Type) (x : A) (f : A -> B),
        pure f <*> pure x = (pure (f x) : Either E B).
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold eitherApplicative.
    trivial.
Qed.

(* Applicative Law 3: Interchange. *)
Lemma EitherApplicativeInterchangeLaw:
    forall (E A B : Type) (x : A) (f : Either E (A -> B)),
        f <*> pure x
            = pure (fun g => g x) <*> f.
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold eitherApplicative.
    destruct f.
    trivial.
    trivial.
Qed.

(* Applicative Law 4: Composition. *)
Lemma EitherApplicativeCompositionLaw:
    forall (E A B C : Type) (w : Either E A) (v : Either E (A -> B))
           (u : Either E (B -> C)),
        pure (fun f g x => f (g x)) <*> u <*> v <*> w
            = u <*> (v <*> w).
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold eitherApplicative.
    destruct u.
    destruct v.
    destruct w.
    4: {
        destruct v.
        destruct w.
        3: {
            destruct w.
            trivial.
            trivial.
        }
        trivial.
        trivial.
    }
    trivial.
    trivial.
    trivial.
Qed.

End EitherApplicativeLaws.
