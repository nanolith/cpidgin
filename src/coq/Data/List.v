Require Import CPidgin.Data.Maybe.

(* Simple linked list of values of an optional type. *)
Inductive List (A : Type) : Type :=
    | nil : List A
    | cons : Maybe A -> List A -> List A.

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
        | x :: xs => x
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
