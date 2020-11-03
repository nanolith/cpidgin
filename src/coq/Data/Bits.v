Require Import Coq.Bool.Bvector.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zdigits.

Module Bits.

(* An 8-bit binary number. *)
Definition B8 := Bvector 8.

(* A 64-bit binary number. *)
Definition B64 := Bvector 64.

(* Map a natural number to an 8-bit binary number. *)
Definition nat_to_B8 (n: nat) : B8 := Z_to_binary 8 (Z.of_nat n).

(* Map a natural number to a 64-bit binary number. *)
Definition nat_to_B64 (n: nat) : B64 := Z_to_binary 64 (Z.of_nat n).

(* Map an 8-bit number to an integer. *)
Definition B8_to_Z (bv : B8) : Z := binary_value 8 bv.

(* Map a 64-bit number to an integer. *)
Definition B64_to_Z (bv : B64) : Z := binary_value 64 bv.

(* Map an integer to a  64-bit number. *)
Definition Z_to_B64 (z : Z) : B64 := Z_to_binary 64 z.

Module ZStuff.

    Local Open Scope Z_scope.

    (* Do a left shift of a B64 value. *)
    Definition B64_shl (bv : B64) := Z_to_B64 ((B64_to_Z bv) * 2).

    (* Do an iterative left shift of a B64 value. *)
    Definition B64_shl_iter (n : nat) (bv : B64) :=
        Z_to_B64 ((B64_to_Z bv) * (two_power_nat n)).

    (* Do a right shift of a B64 value. *)
    Definition B64_shr (bv : B64) := Z_to_B64 ((B64_to_Z bv) / 2).

End ZStuff.

Export ZStuff.

End Bits.
