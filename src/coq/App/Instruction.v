Module Instruction.

(* The Instruction inductive type represents a machine instruction. *)
Inductive Instruction : Type :=
    | NOP : Instruction.

(* The time to execute a NOP instruction. *)
Definition NOP_DELAY : nat := 5.

End Instruction.
