Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Data.Maybe.

(* Helper function to act as an id function. *)
Definition id' {A : Type} (x : A) : A :=
    x.

(* Applicative Law 1: Identity. *)
Lemma MaybeApplicativePreservesIdentityMorphisms:
    forall (A : Type) (x : Maybe A),
        pure id' <*> x = x.
Proof.
    intros.
    unfold id'.
    unfold pure.
    unfold app.
    unfold maybeApplicative.
    destruct x.
    trivial.
    trivial.
Qed.

(* Applicative Law 2: Homomorphism. *)
Lemma MaybeApplicativeHomomorphismLaw:
    forall (A B : Type) (x : A) (f : A -> B),
        pure f <*> pure x = pure (f x).
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold maybeApplicative.
    trivial.
Qed.

(* Applicative Law 3: Interchange. *)
Lemma MaybeApplicativeInterchangeLaw:
    forall (A B : Type) (x : A) (f : Maybe (A -> B)),
        f <*> pure x
            = pure (fun g => g x) <*> f.
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold maybeApplicative.
    trivial.
Qed.

(* Applicative Law 4: Composition. *)
Lemma MaybeApplicativeCompositionLaw:
    forall (A B C : Type) (w : Maybe A) (v : Maybe (A -> B))
           (u : Maybe (B -> C)),
        pure (fun f g x => f (g x)) <*> u <*> v <*> w
            = u <*> (v <*> w).
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold maybeApplicative.
    destruct u.
    destruct v.
    destruct w.
    trivial.
    trivial.
    trivial.
    trivial.
Qed.
