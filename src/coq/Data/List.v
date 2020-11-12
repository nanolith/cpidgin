Require CPidgin.Control.Flip.
Require CPidgin.Control.Monad.
Require CPidgin.Data.Either.
Require CPidgin.Data.Maybe.
Require CPidgin.Data.Monoid.
Require CPidgin.Data.Semigroup.

Module List.

Import Either.Either.
Import Flip.Flip.
Import Maybe.Maybe.
Import Monad.Monad.
Import Monoid.Monoid.
Import Semigroup.Semigroup.

(* Simple linked list of values. *)
Inductive List (A : Type) : Type :=
    | nil : List A
    | cons : A -> List A -> List A.

(* Gather the implicit type A parameter from implicit context. *)
Arguments nil {A}.
(* The implicit type A maps to the type of the cons parameter. *)
Arguments cons {A} a _.

(* Use [] notation to indicate nil. *)
Notation "[ ]" := nil (format "[ ]").
(* Use [ x ] notation to indicate a list of one item. *)
Notation "[ x ]" := (cons x nil).
(* Use [x ; y ; .. ; z ] notation to indicate a variable length list. *)
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
(* Use x :: y to break down a cons cell in a list. *)
Notation "x :: y" := (cons x y).

(* Get the head of a given List. *)
Definition head {A : Type} (lst : List A) : Maybe A :=
    match lst with
        | [] => Nothing
        | x :: xs => Just x
    end.

(* Get the tail of a given List. *)
Definition tail {A : Type} (lst : List A) : List A :=
    match lst with
        | [] => []
        | x :: xs => xs
    end.

(* Drop n elements from a List. *)
Fixpoint drop {A : Type} (n : nat) (lst : List A) : List A :=
    match n with
        | 0 => lst
        | S n' => drop n' (tail lst)
    end.

(* Append two Lists. *)
Fixpoint append {A : Type} (l1 l2 : List A) : List A :=
    match l1 with
        | [] => l2
        | (x :: xs) => x :: append xs l2
    end.

(* Use xs ++ ys to append these two lists. *)
Notation "xs ++ ys" := (append xs ys).

(* Get the length of a List. *)
Fixpoint length {A : Type} (l : List A) : nat :=
    match l with
        | [] => 0
        | (x :: xs) => S (length xs)
    end.

(* Take the first n elements in a List. *)
Fixpoint take {A : Type} (n : nat) (l : List A) : List A :=
    match n with
        | 0 => []
        | S n' =>
            match l with
                | [] => []
                | (x :: xs) => x :: take n' xs
            end
    end.

(* Take the nth item from a List. *)
Definition nth {A : Type} (n : nat) (l : List A) : Maybe A :=
    match n with
        | 0 => head l
        | S n' => head (drop n l)
    end.

(* Remove the nth item from a List. *)
Fixpoint removeNth {A : Type} (n : nat) (l : List A) : List A :=
    match n with
        | 0 => tail l
        | S n' =>
        match l with
            | [] => []
            | (x :: xs) => x :: removeNth n' xs
        end
    end.

(* Reverse a list. *)
Fixpoint reverse {A : Type} (l : List A) : List A :=
    match l with
        | [] => []
        | (x :: xs) => reverse xs ++ [x]
    end.

(* Perform a left fold over a list. *)
Fixpoint foldl {A B : Type} (fn : A -> B -> B) (b : B) (ys : List A) : B :=
    match ys with
        | [] => b
        | (x :: xs) => foldl fn (fn x b) xs
    end.

(* Perform a right fold over a list. *)
Fixpoint foldr {A B : Type} (fn : A -> B -> B) (b : B) (ys : List A) : B :=
    match ys with
        | [] => b
        | (x :: xs) => fn x (foldr fn b xs)
    end.

(* Perform a left fold over a list in an Either Monad space. *)
Fixpoint foldlM {A B E : Type} (fn : B -> A -> Either E B)
                (x : B) (ys : List A) : Either E B :=
    match ys with
        | [] => mret x
        | (s :: ss) => (fn x s) >>= flip (foldlM fn) ss
    end.

(* List forms a Semigroup with append. *)
Instance listSemigroup : Semigroup List := {
    op {a : Type} (x y : List a) := append x y;
}.

(* List forms a Monoid with append and the empty list. *)
Instance listMonoid : Monoid List := {
    mempty {a : Type} := [] : List a;
}.

End List.
