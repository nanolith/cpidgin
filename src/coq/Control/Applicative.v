(* The Applicative typeclass provides a means to lift both values and         *)
(* functions to an applicative functor space.                                 *)
Class Applicative (A: Type -> Type) : Type := {
    pure : forall {t: Type}, t -> A t;
    app : forall {a b: Type}, A (a -> b) -> A a -> A b
}.

(* The <*> operator maps to app. *)
Infix "<*>" := app (at level 65, left associativity).
