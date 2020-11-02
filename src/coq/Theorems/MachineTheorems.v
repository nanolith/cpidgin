Require Import CPidgin.App.Instruction.
Require Import CPidgin.App.Machine.
Require Import CPidgin.Data.Either.

Module MachineTheorems.

Import Either.
Import Instruction.
Import Machine.
Import Monad.

(* Evaluating a NOP instruction succeeds. *)
Lemma eval_nop:
    forall (mach : Machine),
        eval NOP mach = Right mach.
Proof.
    intros.
    unfold eval.
    unfold evalNOP.
    destruct mach.
    unfold Monad.mret.
    unfold eitherMonad.
    trivial.
Qed.

End MachineTheorems.
