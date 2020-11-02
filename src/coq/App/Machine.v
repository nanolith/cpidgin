Require Import Coq.Bool.Bvector.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zdigits.
Require Import CPidgin.App.Instruction.
Require Import CPidgin.Control.Applicative.
Require Import CPidgin.Control.Functor.
Require Import CPidgin.Control.Monad.
Require Import CPidgin.Data.Bits.
Require Import CPidgin.Data.Either.
Require Import CPidgin.Data.MList.

Module Machine.

Import Bits.
Import Either.
Import Instruction.
Import MList.
Import Monad.

(* A stack in the machine model. *)
Definition Stack := MList B64.

(* A register in the machine model. *)
Inductive Register : Type :=
    | Reg : B64 -> Register.

(* The machine state in the machine model. *)
Inductive Machine : Type :=
    | Mach : Stack -> Register -> Machine.

(* An empty machine state. *)
Definition emptyMachine : Machine :=
    Mach [] (Reg (nat_to_B64 0)).

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
        | Mach s r => mret (Mach s r)
    end.

(* Evaluate an instruction on the given machine state. *)
Definition eval (ins : Instruction) (mach : Machine) : MResult :=
        match ins with
            | NOP => evalNOP mach
        end.

End Machine.
