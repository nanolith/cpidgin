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

Module Machine.

Import Bits.
Import Either.
Import Instruction.
Import List.
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
    | MachineErrorUnknownInstruction.

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

(* Evaluate an instruction on the given machine state. *)
Definition eval (ins : Instruction) (mach : Machine) : MResult :=
        match ins with
            | NOP => evalNOP mach
            | IMM val => evalIMM mach val
        end.

End Machine.
