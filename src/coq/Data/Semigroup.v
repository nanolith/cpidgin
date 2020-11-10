Module Semigroup.

(* The Semigroup typeclass provides a single computation operation that has *)
(* associativity. *)
Class Semigroup (S: Type -> Type) : Type := {
    op : forall {a : Type}, a -> a -> a;
}.

(* The <o> operator maps to op. *)
Infix "<o>" := op (at level 65, left associativity).

End Semigroup.
