Require Import CPidgin.App.Instruction.
Require Import CPidgin.App.Machine.
Require Import CPidgin.Data.Bits.
Require Import CPidgin.Data.Either.
Require Import CPidgin.Data.List.

Module MachineTheorems.

Import Bits.
Import Either.
Import Instruction.
Import List.
Import Machine.
Import Monad.

(* Evaluating a NOP instruction succeeds. *)
Lemma eval_nop:
    forall (mach : Machine),
        eval NOP mach = Right (timeDelay mach NOP_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalNOP.
    destruct mach.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* Evaluating an IMM instruction succeeds. *)
Lemma eval_imm:
    forall (s : Stack) (r : Register) (t : Time) (b : B64),
        eval (IMM b) (Mach s r t)
            = Right (timeDelay (Mach s (Reg b) t) IMM_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalIMM.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* Evaluating a PUSH instruction succeeds. *)
Lemma eval_push:
    forall (s : Stack) (r : B64) (t : Time),
        eval PUSH (Mach s (Reg r) t)
            = Right (timeDelay (Mach (r :: s) (Reg r) t) PUSH_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalPUSH.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* Evaluating a POP instruction on an empty stack fails. *)
Lemma eval_pop_empty_stack:
    forall (r : Register) (t : Time),
        eval POP (Mach [] r t)
            = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalPOP.
    unfold exception.
    trivial.
Qed.

(* Evaluating a POP instruction on a non-empty stack succeeds. *)
Lemma eval_pop:
    forall (r : Register) (s : Stack) (v : B64) (t : Time),
        eval POP (Mach (v :: s) r t)
            = Right (timeDelay (Mach s (Reg v) t) POP_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalPOP.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

End MachineTheorems.
