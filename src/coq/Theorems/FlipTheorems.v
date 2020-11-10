Require Import CPidgin.Control.Flip.

Module FlipTheorems.

Import Flip.

(* flip transforms a function that maps from A -> B -> C to one that maps *)
(* from B -> A -> C. *)
Lemma flip_spec:
    forall (A B C : Type) (fn : A -> B -> C) (a : A) (b : B),
        flip fn b a = fn a b.
Proof.
    intros.
    unfold flip.
    trivial.
Qed.

End FlipTheorems.
