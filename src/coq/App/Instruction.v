Require Import CPidgin.Data.Bits.

Module Instruction.

Import Bits.

(* The Instruction inductive type represents a machine instruction. *)
Inductive Instruction : Type :=
    | NOP : Instruction
    | IMM : B64 -> Instruction.

(* The time to execute a NOP instruction. *)
Definition NOP_DELAY : nat := 1.

(* The time to execute an IMM instruction. *)
Definition IMM_DELAY : nat := 2.

End Instruction.
