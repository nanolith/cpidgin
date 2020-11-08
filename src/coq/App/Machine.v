Require Import Coq.Bool.Bvector.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zdigits.
Require Import CPidgin.App.Instruction.
Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Control.Functor.
Require Import CPidgin.Control.Monad.
Require Import CPidgin.Data.Bits.
Require Import CPidgin.Data.Either.
Require Import CPidgin.Data.List.
Require Import CPidgin.Data.Maybe.

Module Machine.

Import Bits.
Import Either.
Import Instruction.
Import List.
Import Maybe.
Import Monad.

(* Time in the machine model. *)
Definition Time := B64.

(* A stack in the machine model. *)
Definition Stack := List B64.

(* A register in the machine model. *)
Inductive Register : Type :=
    | Reg : B64 -> Register.

(* The machine state in the machine model. *)
Inductive Machine : Type :=
    | Mach : Stack -> Register -> Time -> Machine.

(* An empty machine state. *)
Definition emptyMachine : Machine :=
    Mach [] (Reg (nat_to_B64 0)) (nat_to_B64 0).

(* Module for the time delay function. *)
Module TimeDelay.

    Local Open Scope Z_scope.

    (* Delay the machine by a fixed amount of time. *)
    Definition timeDelay (m : Machine) (tn : nat) : Machine :=
        match m with
            | Mach s r t1 => Mach s r (Z_to_B64 ((Z.of_nat tn) + (B64_to_Z t1)))
        end.

End TimeDelay.

Export TimeDelay.

(* Possible errors during a computation. *)
Inductive MachineError : Type :=
    | MachineErrorUnknownInstruction
    | MachineErrorStackUnderflow.

(* The result of a computation can be a MachineError or a Machine state. *)
Definition MResult := Either MachineError Machine.

(* Return a MachineError as a computation result. *)
Definition exception (e : MachineError) : MResult :=
    Left e.

(* Evaluate a NOP instruction with the given machine state. *)
Definition evalNOP (mach : Machine) : MResult :=
    match mach with
        | Mach s r t => mret (timeDelay (Mach s r t) NOP_DELAY)
    end.

(* Evaluate an IMM instruction with the given machine state. *)
Definition evalIMM (mach : Machine) (v : B64) : MResult :=
    match mach with
        | Mach s r t => mret (timeDelay (Mach s (Reg v) t) IMM_DELAY)
    end.

(* Evaluate a PUSH instruction with the given machine state. *)
Definition evalPUSH (mach : Machine) : MResult :=
    match mach with
        | Mach s (Reg r) t =>
            mret (timeDelay (Mach (r :: s) (Reg r) t) PUSH_DELAY)
    end.

(* Evaluate a POP instruction with the given machine state. *)
Definition evalPOP (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t =>
            exception MachineErrorStackUnderflow
        | Mach (s :: ss) r t =>
            mret (timeDelay (Mach ss (Reg s) t) POP_DELAY)
    end.

(* Evaluate a SEL instruction with the given machine state. *)
Definition evalSEL (mach : Machine) (offset : nat) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach ss r t =>
            match (nth offset ss) with
                | Just a =>
                    mret
                        (timeDelay
                            (Mach (removeNth offset ss) (Reg a) t)
                            SEL_DELAY)
                | Nothing => exception MachineErrorStackUnderflow
            end
    end.

(* Evaluate a SHL instruction with the given machine state. *)
Definition evalSHL (mach : Machine) (n : nat) : MResult :=
    match mach with
        | Mach ss (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_shl_iter n r)) t) SHL_DELAY)
    end.

(* Evaluate a SHR instruction with the given machine state. *)
Definition evalSHR (mach : Machine) (n : nat) : MResult :=
    match mach with
        | Mach ss (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_shr_iter n r)) t) SHR_DELAY)
    end.

(* Evaluate an AND instruction with the given machine state. *)
Definition evalAND (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_and s r)) t) AND_DELAY)
    end.

(* Evaluate an OR instruction with the given machine state. *)
Definition evalOR (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_or s r)) t) OR_DELAY)
    end.

(* Evaluate an XOR instruction with the given machine state. *)
Definition evalXOR (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_xor s r)) t) XOR_DELAY)
    end.

(* Evaluate an EQL instruction with the given machine state. *)
Definition evalEQL (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_eql s r)) t) EQL_DELAY)
    end.

(* Evaluate a LT instruction with the given machine state. *)
Definition evalLT (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_lt s r)) t) LT_DELAY)
    end.

(* Evaluate a GT instruction with the given machine state. *)
Definition evalGT (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_gt s r)) t) GT_DELAY)
    end.

(* Evaluate a LE instruction with the given machine state. *)
Definition evalLE (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_le s r)) t) LE_DELAY)
    end.

(* Evaluate a GE instruction with the given machine state. *)
Definition evalGE (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_ge s r)) t) GE_DELAY)
    end.

(* Evaluate a NEQ instruction with the given machine state. *)
Definition evalNEQ (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_neq s r)) t) NEQ_DELAY)
    end.

(* Evaluate a ADD instruction with the given machine state. *)
Definition evalADD (mach : Machine) : MResult :=
    match mach with
        | Mach [] r t => exception MachineErrorStackUnderflow
        | Mach (s :: ss) (Reg r) t =>
            mret (timeDelay (Mach ss (Reg (B64_add s r)) t) ADD_DELAY)
    end.

(* Evaluate an instruction on the given machine state. *)
Definition eval (ins : Instruction) (mach : Machine) : MResult :=
        match ins with
            | NOP => evalNOP mach
            | IMM val => evalIMM mach val
            | PUSH => evalPUSH mach
            | POP => evalPOP mach
            | SEL n => evalSEL mach n
            | SHL n => evalSHL mach n
            | SHR n => evalSHR mach n
            | AND => evalAND mach
            | OR => evalOR mach
            | XOR => evalXOR mach
            | EQL => evalEQL mach
            | LT => evalLT mach
            | GT => evalGT mach
            | LE => evalLE mach
            | GE => evalGE mach
            | NEQ => evalNEQ mach
            | ADD => evalADD mach
        end.

End Machine.
