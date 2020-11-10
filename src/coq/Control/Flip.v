Module Flip.

(* Transform a function that maps a -> b -> c to one that maps b -> a -> c *)
Definition flip { A B C : Type } (fn : A -> B -> C) (b : B) (a : A) : C :=
    fn a b.

End Flip.
