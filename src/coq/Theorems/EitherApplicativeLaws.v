Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Data.Either.

(* Helper function to act as an id function. *)
Definition fid {A : Type} (x : A) : A :=
    x.

(* Applicative Law 1: Identity. *)
Lemma Applicative_Either_Law1:
    forall (E A : Type) (x : Either E A),
        pure fid <*> x = x.
Proof.
    intros.
    unfold fid.
    unfold pure.
    unfold app.
    unfold eitherApplicative.
    induction x.
    trivial.
    trivial.
Qed.

(* Applicative Law 2: Homomorphism. *)
Lemma Applicative_Either_Law2:
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
Lemma Applicative_Either_Law3:
    forall (E A B : Type) (x : A) (f : Either E (A -> B)),
        f <*> pure x
            = pure (fun g => g x) <*> f.
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold eitherApplicative.
    trivial.
Qed.

(* Applicative Law 4: Composition. *)
Lemma Applicative_Either_Law4:
    forall (E A B C : Type) (w : Either E A) (v : Either E (A -> B))
           (u : Either E (B -> C)),
        pure (fun f g x => f (g x)) <*> u <*> v <*> w
            = u <*> (v <*> w).
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold eitherApplicative.
    induction w.
    induction v.
    induction u.
    trivial.
    trivial.
    induction u.
    trivial.
    trivial.
    induction v.
    induction u.
    trivial.
    trivial.
    induction u.
    trivial.
    trivial.
Qed.
