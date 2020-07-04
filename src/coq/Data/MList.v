Require Import CPidgin.Data.Maybe.

(* Simple linked list of values of an optional type. *)
Inductive MList (A : Type) : Type :=
    | nil : MList A
    | cons : Maybe A -> MList A -> MList A.

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

(* Get the head of a given MList. *)
Definition head {A : Type} (lst : MList A) : Maybe A :=
    match lst with
        | [] => Nothing
        | x :: xs => x
    end.

(* Get the tail of a given MList. *)
Definition tail {A : Type} (lst : MList A) : MList A :=
    match lst with
        | [] => []
        | x :: xs => xs
    end.

(* Drop n elements from a MList. *)
Fixpoint drop {A : Type} (n : nat) (lst : MList A) : MList A :=
    match n with
        | 0 => lst
        | S n' => drop n' (tail lst)
    end.

(* Append two MLists. *)
Fixpoint append {A : Type} (l1 l2 : MList A) : MList A :=
    match l1 with
        | [] => l2
        | (x :: xs) => x :: append xs l2
    end.

(* Use xs ++ ys to append these two lists. *)
Notation "xs ++ ys" := (append xs ys).

(* Get the length of an MList. *)
Fixpoint length {A : Type} (l : MList A) : nat :=
    match l with
        | [] => 0
        | (x :: xs) => S (length xs)
    end.

(* Take the first n elements in an MList. *)
Fixpoint take {A : Type} (n : nat) (l : MList A) : MList A :=
    match n with
        | 0 => []
        | S n' =>
            match l with
                | [] => []
                | (x :: xs) => x :: take n' xs
            end
    end.

(* Take the nth item from an MList. *)
Definition nth {A : Type} (n : nat) (l : MList A) : Maybe A :=
    match n with
        | 0 => head l
        | S n' => head (drop n l)
    end.

(* Remove the nth item from an MList. *)
Fixpoint removeNth {A : Type} (n : nat) (l : MList A) : MList A :=
    match n with
        | 0 => tail l
        | S n' =>
        match l with
            | [] => []
            | (x :: xs) => x :: removeNth n' xs
        end
    end.
