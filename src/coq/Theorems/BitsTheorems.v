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

    (* Left shifting a value by n is the same as multiplying it by 2^n. *)
    Lemma bits_shl_iter:
        forall (x : Z) (n : nat),
            0 <= x ->
            x < two_power_nat 64 ->
            0 <= x * (two_power_nat n) < two_power_nat 64 ->
            B64_to_Z (B64_shl_iter n (Z_to_B64 x)) = x * (two_power_nat n).
    Proof.
        intros x n H0 H1 H2.
        destruct H2.
        unfold B64_shl_iter.
        unfold Z_to_B64.
        unfold B64_to_Z.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        trivial.
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

    (* Right shifting a value by n is the same as dividing it by 2^n. *)
    Lemma bits_shr_iter:
        forall (x : Z) (n : nat),
            0 <= x ->
            x < two_power_nat 64 ->
            0 <= x / (two_power_nat n) < two_power_nat 64 ->
            B64_to_Z (B64_shr_iter n (Z_to_B64 x)) = x / (two_power_nat n).
    Proof.
        intros x n H0 H1 H2.
        destruct H2.
        unfold B64_shr_iter.
        unfold Z_to_B64.
        unfold B64_to_Z.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        trivial.
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

    (* If two values are equal, then B64_eql returns 1. *)
    Lemma B64_eql_Eq:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Eq ->
                B64_eql x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_eql.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Lt, then B64_eql returns 0. *)
    Lemma B64_eql_Lt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Lt ->
                B64_eql x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_eql.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Gt, then B64_eql returns 0. *)
    Lemma B64_eql_Gt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Gt ->
                B64_eql x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_eql.
        rewrite H.
        trivial.
    Qed.

    (* If two values are equal, then B64_lt returns 0. *)
    Lemma B64_lt_Eq:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Eq ->
                B64_lt x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_lt.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Lt, then B64_lt returns 1. *)
    Lemma B64_lt_Lt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Lt ->
                B64_lt x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_lt.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Gt, then B64_lt returns 0. *)
    Lemma B64_lt_Gt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Gt ->
                B64_lt x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_lt.
        rewrite H.
        trivial.
    Qed.


    (* If two values are equal, then B64_gt returns 0. *)
    Lemma B64_gt_Eq:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Eq ->
                B64_gt x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_gt.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Lt, then B64_gt returns 0. *)
    Lemma B64_gt_Lt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Lt ->
                B64_gt x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_gt.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Gt, then B64_gt returns 1. *)
    Lemma B64_gt_Gt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Gt ->
                B64_gt x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_gt.
        rewrite H.
        trivial.
    Qed.

    (* If two values are equal, then B64_le returns 1. *)
    Lemma B64_le_Eq:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Eq ->
                B64_le x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_le.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Lt, then B64_le returns 1. *)
    Lemma B64_le_Lt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Lt ->
                B64_le x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_le.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Gt, then B64_le returns 0. *)
    Lemma B64_le_Gt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Gt ->
                B64_le x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_le.
        rewrite H.
        trivial.
    Qed.

    (* If two values are equal, then B64_ge returns 1. *)
    Lemma B64_ge_Eq:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Eq ->
                B64_ge x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_ge.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Lt, then B64_ge returns 0. *)
    Lemma B64_ge_Lt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Lt ->
                B64_ge x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_ge.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Gt, then B64_ge returns 1. *)
    Lemma B64_ge_Gt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Gt ->
                B64_ge x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_ge.
        rewrite H.
        trivial.
    Qed.

    (* If two values are equal, then B64_neq returns 0. *)
    Lemma B64_neq_Eq:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Eq ->
                B64_neq x y = nat_to_B64 0.
    Proof.
        intros x y H.
        unfold B64_neq.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Lt, then B64_neq returns 1. *)
    Lemma B64_neq_Lt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Lt ->
                B64_neq x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_neq.
        rewrite H.
        trivial.
    Qed.

    (* If two values are Gt, then B64_neq returns 1. *)
    Lemma B64_neq_Gt:
        forall (x y : B64),
            (B64_to_Z x) ?= (B64_to_Z y) = Gt ->
                B64_neq x y = nat_to_B64 1.
    Proof.
        intros x y H.
        unfold B64_neq.
        rewrite H.
        trivial.
    Qed.

    (* We can add two values. *)
    Lemma B64_add:
        forall (x y : Z),
            0 <= x < two_power_nat 64 ->
            0 <= y < two_power_nat 64 ->
            x + y < two_power_nat 64 ->
            (B64_to_Z (B64_add (Z_to_B64 x) (Z_to_B64 y))) = x + y.
    Proof.
        intros x y Hx Hy Hxy.
        unfold B64_add.
        unfold B64_to_Z.
        unfold Z_to_B64.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        trivial.
        nia.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
        nia.
        nia.
    Qed.

    (* We can subtract two values. *)
    Lemma B64_sub:
        forall (x y : Z),
            0 <= x < two_power_nat 64 ->
            0 <= y < two_power_nat 64 ->
            x - y >= 0 ->
            (B64_to_Z (B64_sub (Z_to_B64 x) (Z_to_B64 y))) = x - y.
    Proof.
        intros x y Hx Hy Hxy.
        unfold B64_sub.
        unfold B64_to_Z.
        unfold Z_to_B64.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        trivial.
        nia.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
        nia.
        nia.
    Qed.

    (* We can multiply two values. *)
    Lemma B64_mul:
        forall (x y : Z),
            0 <= x < two_power_nat 64 ->
            0 <= y < two_power_nat 64 ->
            x * y < two_power_nat 64 ->
            (B64_to_Z (B64_mul (Z_to_B64 x) (Z_to_B64 y))) = x * y.
    Proof.
        intros x y Hx Hy Hxy.
        unfold B64_mul.
        unfold B64_to_Z.
        unfold Z_to_B64.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        trivial.
        nia.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
        nia.
        nia.
        rewrite Z_to_binary_to_Z.
        rewrite Z_to_binary_to_Z.
        nia.
        nia.
        nia.
        nia.
        nia.
    Qed.

End ZStuff.

End BitsTheorems.
