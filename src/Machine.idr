module Machine

import Data.Bits
import Data.List
import Instruction

public export
data Register = Reg Bits64

public export
data Timer = Time Bits64

public export
data Stack = StackFromList (List Bits64)

public export
data Machine = Mach Stack Register Timer

public export
data MachineException =
      NotImplementedException String
    | StackUnderflowException

public export
comp : Machine -> Either MachineException Machine
comp = Right

public export
exception : MachineException -> Either MachineException Machine
exception = Left

public export
machineRegister : Machine -> Bits64
machineRegister (Mach _ (Reg a) _) = a

public export
emptyMachine : Machine
emptyMachine =
    (Mach (StackFromList []) (Reg 0) (Time 0))

public export
shl : Bits64 -> Nat -> Bits64
shl x Z = x
shl x (S n) = shl (x * 2) n

public export
eval : Instruction -> Machine -> Either MachineException Machine
eval NOP (Mach s r (Time t)) =
    comp (Mach s r (Time (t + Instruction.timeNOP)))
eval (IMM i) (Mach s _ (Time t)) =
    comp (Mach s (Reg i) (Time (t + Instruction.timeIMM)))
eval PUSH (Mach (StackFromList ss) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList (a :: ss))
            (Reg a)
            (Time (t + Instruction.timePUSH)))
eval POP (Mach (StackFromList (s :: ss)) _ (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg s)
            (Time (t + Instruction.timePOP)))
eval POP (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval DUP (Mach (StackFromList (s :: ss)) r (Time t)) =
    comp (Mach
            (StackFromList (s :: s :: ss))
            r
            (Time (t + Instruction.timeDUP)))
eval DUP (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval (SHL n) (Mach s (Reg a) (Time t)) =
    comp (Mach
            s
            (Reg (shl a n))
            (Time (t + Instruction.timeSHL)))
eval AND (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__andB64` s))
            (Time (t + Instruction.timeAND)))
eval AND (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval ADD (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a + s))
            (Time (t + Instruction.timeADD)))
eval ADD (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval MUL (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a * s))
            (Time (t + Instruction.timeMUL)))
eval MUL (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval _ _ = exception (NotImplementedException "Unknown instruction.")

--The NOP instruction takes one cycle and does not otherwise change machine
--state.
export
evalNOPSpec : {s : Stack} -> {r : Register} -> {t : Bits64}
                -> eval NOP (Mach s r (Time t))
                    = comp (Mach s r (Time (t + Instruction.timeNOP)))
evalNOPSpec = Refl

--The IMM instruction loads the given immediate value into the register.
export
evalIMMSpec : {s : Stack} -> {i, t : Bits64}
                -> eval (IMM i) (Mach s _ (Time t))
                    = comp (Mach s (Reg i) (Time (t + Instruction.timeIMM)))
evalIMMSpec = Refl

--The PUSH instruction writes the register to the stack.
export
evalPUSHSpec : {ss : List Bits64} -> {a, t : Bits64}
                -> eval PUSH (Mach (StackFromList ss) (Reg a) (Time t))
                    = comp (Mach
                                (StackFromList (a :: ss))
                                (Reg a)
                                (Time (t + Instruction.timePUSH)))
evalPUSHSpec = Refl

--The POP instruction reads the register from the stack.
export
evalPOPHappySpec : {ss : List Bits64} -> {s, t : Bits64}
                    -> eval POP (Mach (StackFromList (s :: ss)) _ (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg s)
                                    (Time (t + Instruction.timePOP)))
evalPOPHappySpec = Refl

--The POP instruction underflows the stack if the stack is empty.
export
evalPOPUnderflowSpec : eval POP (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalPOPUnderflowSpec = Refl

--The DUP instruction duplicates the top of the stack.
export
evalDUPHappySpec : {ss : List Bits64} -> {r : Register} -> {s, t : Bits64}
                    -> eval DUP (Mach (StackFromList (s :: ss)) r (Time t))
                        = comp (Mach
                                    (StackFromList (s :: s :: ss))
                                    r
                                    (Time (t + Instruction.timeDUP)))
evalDUPHappySpec = Refl

--The DUP instruction underflows the stack if the stack is empty.
export
evalDUPUnderflowSpec : eval DUP (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalDUPUnderflowSpec = Refl

--The SHL instruction shifts the register to the left by the IMM number of bits.
export
evalSHLHappySpec : {n : Nat} -> {s : Stack} -> {a, t : Bits64}
                    -> eval (SHL n)
                            (Mach s (Reg a) (Time t))
                        = comp (Mach
                                    s
                                    (Reg (shl a n))
                                    (Time (t + Instruction.timeSHL)))
evalSHLHappySpec = Refl

--The AND instruction performs a bitwise and between the top of stack and the
--register.
export
evalANDHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval AND
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__andB64` s))
                                    (Time (t + Instruction.timeAND)))
evalANDHappySpec = Refl

--The AND instruction underflows the stack if the stack is empty.
export
evalANDUnderflowSpec : eval AND (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalANDUnderflowSpec = Refl

--The ADD instruction adds the top of stack to the register.
export
evalADDHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval ADD
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a + s))
                                    (Time (t + Instruction.timeADD)))
evalADDHappySpec = Refl

--The ADD instruction underflows the stack if the stack is empty.
export
evalADDUnderflowSpec : eval ADD (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalADDUnderflowSpec = Refl

--The MUL instruction multiplies the top of stack with the register.
export
evalMULHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval MUL
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a * s))
                                    (Time (t + Instruction.timeMUL)))
evalMULHappySpec = Refl

--The MUL instruction underflows the stack if the stack is empty.
export
evalMULUnderflowSpec : eval MUL (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalMULUnderflowSpec = Refl
