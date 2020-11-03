Require Import Coq.Bool.Bvector.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zdigits.
Require Import Coq.ZArith.Zdiv.
Require Import Coq.ZArith.Zorder.
Require Import Coq.micromega.Lia.
Require Import CPidgin.Data.Bits.

Module BitsTheorems.

Import Bits.

Module ZStuff.

    Local Open Scope Z_scope.

    (* 0 = 0 * 2. *)
    Lemma zero_2_mult:
        0 = 0 * 2.
    Proof.
        compute.
        trivial.
    Qed.

    (* Shifting a value to the left is the same as multiplying it by 2. *)
    Lemma bits_shl:
        forall (x : Z),
            0 <= x * 2 < two_power_nat 64 ->
                B64_to_Z (B64_shl (Z_to_B64 x)) = x * 2.
    Proof.
        intros.
        destruct H.
        unfold B64_shl.
        unfold Z_to_B64.
        unfold B64_to_Z.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        trivial.
        rewrite Z.ge_le_iff.
        rewrite zero_2_mult in H.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
    Qed.

    (* Shifting a value to the right is the same as dividing it by 2. *)
    Lemma bits_shr:
        forall (x : Z),
            0 < x < two_power_nat 64 ->
                B64_to_Z (B64_shr (Z_to_B64 x)) = x / 2.
    Proof.
        intros.
        destruct H.
        unfold B64_shr.
        unfold Z_to_B64.
        unfold B64_to_Z.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        trivial.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z.ge_le_iff.
        apply Z_div_pos.
        nia.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z_div_lt.
        nia.
        nia.
        nia.
        nia.
        nia.
    Qed.

End ZStuff.

End BitsTheorems.
