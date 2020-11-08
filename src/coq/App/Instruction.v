Require Import CPidgin.Data.Bits.

Module Instruction.

Import Bits.

(* The Instruction inductive type represents a machine instruction. *)
Inductive Instruction : Type :=
    | NOP : Instruction
    | IMM : B64 -> Instruction
    | PUSH : Instruction
    | POP : Instruction
    | SEL : nat -> Instruction
    | SHL : nat -> Instruction
    | SHR : nat -> Instruction
    | AND : Instruction
    | OR : Instruction
    | XOR : Instruction
    | EQL : Instruction
    | LT : Instruction
    | GT : Instruction
    | LE : Instruction
    | GE : Instruction
    | NEQ : Instruction
    | ADD : Instruction.

(* The time to execute a NOP instruction. *)
Definition NOP_DELAY : nat := 1.

(* The time to execute an IMM instruction. *)
Definition IMM_DELAY : nat := 2.

(* The time to execute a PUSH instruction. *)
Definition PUSH_DELAY : nat := 2.

(* The time to execute a POP instruction. *)
Definition POP_DELAY : nat := 2.

(* The time to execute a SEL instruction. *)
Definition SEL_DELAY : nat := 3.

(* The time to execute a SHL instruction. *)
Definition SHL_DELAY : nat := 2.

(* The time to execute a SHR instruction. *)
Definition SHR_DELAY : nat := 2.

(* The time to execute an AND instruction. *)
Definition AND_DELAY : nat := 2.

(* The time to execute an OR instruction. *)
Definition OR_DELAY : nat := 2.

(* The time to execute an XOR instruction. *)
Definition XOR_DELAY : nat := 2.

(* The time to execute an EQL instruction. *)
Definition EQL_DELAY : nat := 2.

(* The time to execute a LT instruction. *)
Definition LT_DELAY : nat := 2.

(* The time to execute a GT instruction. *)
Definition GT_DELAY : nat := 2.

(* The time to execute a LE instruction. *)
Definition LE_DELAY : nat := 2.

(* The time to execute a GE instruction. *)
Definition GE_DELAY : nat := 2.

(* The time to execute a NEQ instruction. *)
Definition NEQ_DELAY : nat := 2.

(* The time to execute an ADD instruction. *)
Definition ADD_DELAY : nat := 3.

End Instruction.
