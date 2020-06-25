Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Control.Functor.
Require Import CPidgin.Control.Monad.

(* The Either inductive type describes a disjunctive value. *)
Inductive Either (A B : Type) : Type :=
    | Left : A -> Either A B
    | Right : B -> Either A B.

(* The implicit type A maps to the Left type. *)
Arguments Left {A B} _ , [A] B _.
(* The implicit type B maps to the Right type. *)
Arguments Right {A B} _ , A [B] _.

(* The Either inductive type can be mapped to an Applicative functor space,   *)
(* in which operations on Either values can be mapped back to operations on   *)
(* regular values. *)
Instance eitherApplicative (e: Type) : Applicative (Either e) := {
    pure t x := Right x;
    app a b af ax :=
        match af with
            Left e => Left e
          | Right f =>
                match ax with
                    Left e => Left e
                  | Right x => Right (f x)
                end
        end
}.

(* The Either inductive type can be mapped to a Functor space in which        *)
(* functions are either executed on values or map to a left error value.      *)
Instance eitherFunctor (e: Type) : Functor (Either e) := {
    fmap a b f ax :=
        match ax with
            Left e => Left e
          | Right x => Right (f x)
        end
}.

(* The Either inductive type can be mapped to a Monad space in which          *)
(* computations on optional values can be short-circuited if these values do  *)
(* not exist. *)
Instance eitherMonad (e: Type) : Monad (Either e) := {
    mret t x := Right x;
    bind a b m f :=
        match m with
            Left x => Left x
          | Right y => f y
        end
}.
