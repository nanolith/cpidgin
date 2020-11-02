Module Monad.

(* The Monad typeclass provides a way to capture a computation entering a     *)
(* monadic space, as well as a way to lift values to this space and to bind   *)
(* the outputs of these computations to functions that enter this monadic     *)
(* space.                                                                     *)
Class Monad (M: Type -> Type) : Type := {
    mret : forall {t: Type}, t -> M t;
    bind : forall {a b: Type}, M a -> (a -> M b) -> M b
}.

(* The >>= operator maps to bind. *)
Infix ">>=" := bind (at level 65, left associativity).

End Monad.
