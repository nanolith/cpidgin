Require Import CPidgin.Control.Functor.
Require Import CPidgin.Data.Maybe.

Definition fid {A : Type} (x : A): A :=
    x.

(* Functor Law 1: Identity. *)
Lemma Functor_Maybe_Law1:
    forall (A : Type) (x : Maybe A),
        fid <$> x = x.
Proof.
    intros.
    unfold fmap.
    unfold maybeFunctor.
    unfold fid.
    induction x.
    trivial.
    trivial.
Abort.

(* Functor Law 2: Composition. *)
Lemma Functor_Maybe_Law2:
    forall (A B C : Type) (x : Maybe A) (f : A -> B) (g : B -> C),
        (fun a => g (f a)) <$> x
            = g <$> (f <$> x).
Proof.
    intros.
    unfold fmap.
    unfold maybeFunctor.
    induction x.
    trivial.
    trivial.
Qed.
