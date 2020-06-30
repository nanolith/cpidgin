Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Data.Maybe.

(* Helper function to act as an id function. *)
Definition fid {A : Type} (x : A) : A :=
    x.

(* Applicative Law 1: Identity. *)
Lemma Applicative_Maybe_Law1:
    forall (A : Type) (x : Maybe A),
        pure fid <*> x = x.
Proof.
    intros.
    unfold fid.
    unfold pure.
    unfold app.
    unfold maybeApplicative.
    induction x.
    trivial.
    trivial.
Qed.

(* Applicative Law 2: Homomorphism. *)
Lemma Applicative_Maybe_Law2:
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
Lemma Applicative_Maybe_Law3:
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
Lemma Applicative_Maybe_Law4:
    forall (A B C : Type) (w : Maybe A) (v : Maybe (A -> B))
           (u : Maybe (B -> C)),
        pure (fun f g x => f (g x)) <*> u <*> v <*> w
            = u <*> (v <*> w).
Proof.
    intros.
    unfold pure.
    unfold app.
    unfold maybeApplicative.
    induction w.
    induction u.
    induction v.
    trivial.
    trivial.
    trivial.
    induction u.
    induction v.
    trivial.
    trivial.
    trivial.
Qed.