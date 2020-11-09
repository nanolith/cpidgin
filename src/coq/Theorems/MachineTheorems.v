Require Import Coq.Bool.Bvector.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zdigits.
Require Import Coq.ZArith.Zdiv.
Require Import Coq.ZArith.Zorder.
Require Import Coq.micromega.Lia.
Require Import CPidgin.App.Instruction.
Require Import CPidgin.App.Machine.
Require Import CPidgin.Data.Bits.
Require Import CPidgin.Data.Either.
Require Import CPidgin.Data.List.
Require Import CPidgin.Data.Maybe.

Module MachineTheorems.

Import Bits.
Import Either.
Import Instruction.
Import List.
Import Machine.
Import Maybe.
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

(* Evaluating a SEL instruction on an empty stack fails. *)
Lemma eval_sel_empty_stack:
    forall (r : Register) (t : Time) (n : nat),
        eval (SEL n) (Mach [] r t)
            = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalSEL.
    unfold exception.
    trivial.
Qed.

(* If nth returns Nothing, then SEL fails. *)
Lemma eval_sel_small_stack:
    forall (s : Stack) (r : Register) (t : Time) (n : nat),
        nth n s = Nothing ->
            eval (SEL n) (Mach s r t)
                = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalSEL.
    rewrite H.
    destruct s.
    unfold exception.
    trivial.
    unfold exception.
    trivial.
Qed.

(* If nth returns a valid value, then SEL succeeds. *)
Lemma eval_sel:
    forall (s : B64) (ss : Stack) (r : Register) (t : Time) (n : nat) (v : B64),
        nth n (s :: ss) = Just v ->
            eval (SEL n) (Mach (s :: ss) r t)
                = Right
                    (timeDelay
                        (Mach (removeNth n (s :: ss)) (Reg v) t)
                        SEL_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalSEL.
    rewrite H.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* If x is in range, then SHL x returns a valid result. *)
Lemma eval_shl:
    forall (ss : Stack) (t : Time) (n : nat) (x : Z),
        eval (SHL n) (Mach ss (Reg (Z_to_B64 x)) t)
            = Right
                (timeDelay
                    (Mach ss (Reg (B64_shl_iter n (Z_to_B64 x))) t) SHL_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalSHL.
    unfold B64_to_Z.
    unfold Z_to_B64.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* If x is in range, then SHR x returns a valid result. *)
Lemma eval_shr:
    forall (ss : Stack) (t : Time) (n : nat) (x : Z),
        eval (SHR n) (Mach ss (Reg (Z_to_B64 x)) t)
            = Right
                (timeDelay
                    (Mach ss (Reg (B64_shr_iter n (Z_to_B64 x))) t) SHR_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalSHR.
    unfold B64_to_Z.
    unfold Z_to_B64.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* AND with an empty stack causes a stack underflow exception. *)
Lemma eval_and_empty_stack:
    forall (t : Time) (r : Register),
        eval AND (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalAND.
    unfold exception.
    trivial.
Qed.

(* AND performs a bitwise and on two factors. *)
Lemma eval_and:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval AND (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_and s r)) t) AND_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalAND.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* OR with an empty stack causes a stack underflow exception. *)
Lemma eval_or_empty_stack:
    forall (t : Time) (r : Register),
        eval OR (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalOR.
    unfold exception.
    trivial.
Qed.

(* OR performs a bitwise or on two factors. *)
Lemma eval_or:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval OR (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_or s r)) t) OR_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalOR.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* XOR with an empty stack causes a stack underflow exception. *)
Lemma eval_xor_empty_stack:
    forall (t : Time) (r : Register),
        eval XOR (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalXOR.
    unfold exception.
    trivial.
Qed.

(* XOR performs a bitwise xor on two factors. *)
Lemma eval_xor:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval XOR (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_xor s r)) t) XOR_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalXOR.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* EQL with an empty stack causes a stack underflow exception. *)
Lemma eval_eql_empty_stack:
    forall (t : Time) (r : Register),
        eval EQL (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalEQL.
    unfold exception.
    trivial.
Qed.

(* EQL performs an equality check on two values. *)
Lemma eval_eql:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval EQL (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_eql s r)) t) EQL_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalEQL.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* LT with an empty stack causes a stack underflow exception. *)
Lemma eval_lt_empty_stack:
    forall (t : Time) (r : Register),
        eval LT (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalLT.
    unfold exception.
    trivial.
Qed.

(* LT performs an inequality check on two values. *)
Lemma eval_lt:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval LT (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_lt s r)) t) LT_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalLT.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* GT with an empty stack causes a stack underflow exception. *)
Lemma eval_gt_empty_stack:
    forall (t : Time) (r : Register),
        eval GT (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalGT.
    unfold exception.
    trivial.
Qed.

(* GT performs an inequality check on two values. *)
Lemma eval_gt:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval GT (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_gt s r)) t) GT_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalGT.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* LE with an empty stack causes a stack underflow exception. *)
Lemma eval_le_empty_stack:
    forall (t : Time) (r : Register),
        eval LE (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalLE.
    unfold exception.
    trivial.
Qed.

(* LE performs an inequality check on two values. *)
Lemma eval_le:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval LE (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_le s r)) t) LE_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalLE.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* GE with an empty stack causes a stack underflow exception. *)
Lemma eval_ge_empty_stack:
    forall (t : Time) (r : Register),
        eval GE (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalGE.
    unfold exception.
    trivial.
Qed.

(* GE performs an inequality check on two values. *)
Lemma eval_ge:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval GE (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_ge s r)) t) GE_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalGE.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* NEQ with an empty stack causes a stack underflow exception. *)
Lemma eval_neq_empty_stack:
    forall (t : Time) (r : Register),
        eval NEQ (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalNEQ.
    unfold exception.
    trivial.
Qed.

(* NEQ performs an inequality check on two values. *)
Lemma eval_neq:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval NEQ (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_neq s r)) t) NEQ_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalNEQ.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* ADD with an empty stack causes a stack underflow exception. *)
Lemma eval_add_empty_stack:
    forall (t : Time) (r : Register),
        eval ADD (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalADD.
    unfold exception.
    trivial.
Qed.

(* ADD adds two numbers. *)
Lemma eval_add:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval ADD (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_add s r)) t) ADD_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalADD.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* SUB with an empty stack causes a stack underflow exception. *)
Lemma eval_sub_empty_stack:
    forall (t : Time) (r : Register),
        eval SUB (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalSUB.
    unfold exception.
    trivial.
Qed.

(* SUB subtracts two numbers. *)
Lemma eval_sub:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval SUB (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_sub s r)) t) SUB_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalSUB.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

(* MUL with an empty stack causes a stack underflow exception. *)
Lemma eval_mul_empty_stack:
    forall (t : Time) (r : Register),
        eval MUL (Mach [] r t) = Left MachineErrorStackUnderflow.
Proof.
    intros.
    unfold eval.
    unfold evalMUL.
    unfold exception.
    trivial.
Qed.

(* MUL subtracts two numbers. *)
Lemma eval_mul:
    forall (s : B64) (ss : Stack) (t : Time) (r : B64),
        eval MUL (Mach (s :: ss) (Reg r) t)
            = Right (timeDelay (Mach ss (Reg (B64_mul s r)) t) MUL_DELAY).
Proof.
    intros.
    unfold eval.
    unfold evalMUL.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

End MachineTheorems.
