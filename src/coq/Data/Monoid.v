Require Import CPidgin.Data.Semigroup.

Module Monoid.

Import Semigroup.

(* The Monoid typeclass provides a way to describe a binary operation with *)
(* identity. *)
Class Monoid M `{S : Semigroup M} : Type := {
    mempty : forall {t : Type}, M t;
}.

End Monoid.
