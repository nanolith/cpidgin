(* The Functor typeclass provides a mapping function to lift an arbitrary     *)
(* function to a functor space.                                               *)
Class Functor (F: Type -> Type) : Type := {
    fmap : forall {a b: Type}, (a -> b) -> F a -> F b
}.

(* The <$> operator maps to fmap. *)
Infix "<$>" := fmap (at level 65, left associativity).
