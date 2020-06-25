Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Control.Functor.
Require Import CPidgin.Control.Monad.

(* The Maybe inductive type describes an optional value. *)
Inductive Maybe (A : Type) : Type :=
    | Just : A -> Maybe A
    | Nothing : Maybe A.

(* The implicit type A maps to the type of the Just parameter. *)
Arguments Just {A} a.
(* Gather the type A parameter from implicit context. *)
Arguments Nothing {A}.

(* The Maybe inductive type can be mapped to an Applicative functor space, in *)
(* which operations on Maybe values can be mapped back to operations on       *)
(* regular values. *)
Instance maybeApplicative : Applicative Maybe := {
    pure t x := Just x;
    app a b af ax :=
        match af with
            Nothing => Nothing
          | Just f =>
                match ax with
                    Nothing => Nothing
                  | Just x => Just (f x)
                end
        end
}.

(* The Maybe inductive type can be mapped to a Functor space in which         *)
(* functions are either executed on values or map to nothing.                 *)
Instance maybeFunctor : Functor Maybe := {
    fmap a b f ax :=
        match ax with
            Nothing => Nothing
          | Just x => Just (f x)
        end
}.

(* The Maybe inductive type can be mapped to a Monad space in which           *)
(* computations on optional values can be short-circuited if these values do  *)
(* not exist.                                                                 *)
Instance maybeMonad : Monad Maybe := {
    mret t x := Just x;
    bind a b m f :=
        match m with
            Nothing => Nothing
          | Just x => f x
        end
}.
