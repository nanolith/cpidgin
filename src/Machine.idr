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
    | DivideByZeroException

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

public export total
shr : Bits64 -> Nat -> Bits64
shr x Z = x
shr x (S n) = shr (assert_total $ prim__sdivB64 x 2) n

public export total
evalMod : Bits64 -> Bits64 -> Either MachineException Bits64
--the zero case has a hole in urem, so we throw an exception
evalMod x 0 = Left DivideByZeroException
--since y is non-zero, there is no longer a hole. Force totality.
evalMod x y = assert_total $ Right $ x `prim__uremB64` y

public export total
evalDiv : Bits64 -> Bits64 -> Either MachineException Bits64
--the zero case has a hole in udiv, so we throw an exception
evalDiv x 0 = Left DivideByZeroException
--since y is non-zero, there is no longer a hole. Force totality.
evalDiv x y = assert_total $ Right $ x `prim__udivB64` y

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
eval (SHR n) (Mach s (Reg a) (Time t)) =
    comp (Mach
            s
            (Reg (shr a n))
            (Time (t + Instruction.timeSHR)))
eval AND (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__andB64` s))
            (Time (t + Instruction.timeAND)))
eval AND (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval OR (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__orB64` s))
            (Time (t + Instruction.timeOR)))
eval OR (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval XOR (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__xorB64` s))
            (Time (t + Instruction.timeXOR)))
eval XOR (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval EQ (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a == s then 1 else 0))
            (Time (t + Instruction.timeEQ)))
eval EQ (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval LT (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a < s then 1 else 0))
            (Time (t + Instruction.timeLT)))
eval LT (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval GT (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a > s then 1 else 0))
            (Time (t + Instruction.timeGT)))
eval GT (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval LE (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a <= s then 1 else 0))
            (Time (t + Instruction.timeLE)))
eval LE (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval GE (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a >= s then 1 else 0))
            (Time (t + Instruction.timeLE)))
eval GE (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval ADD (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a + s))
            (Time (t + Instruction.timeADD)))
eval ADD (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval SUB (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__subB64` s))
            (Time (t + Instruction.timeSUB)))
eval SUB (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval MUL (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a * s))
            (Time (t + Instruction.timeMUL)))
eval MUL (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval MOD (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) = do
    res <- evalMod a s
    comp (Mach
            (StackFromList ss)
            (Reg res)
            (Time (t + Instruction.timeMOD)))
eval MOD (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
eval DIV (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) = do
    res <- evalDiv a s
    comp (Mach
            (StackFromList ss)
            (Reg res)
            (Time (t + Instruction.timeDIV)))
eval DIV (Mach (StackFromList []) _ _) =
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

--The SHR instruction shifts the reg to the right by the IMM number of bits.
export
evalSHRHappySpec : {n : Nat} -> {s : Stack} -> {a, t : Bits64}
                    -> eval (SHR n)
                            (Mach s (Reg a) (Time t))
                        = comp (Mach
                                    s
                                    (Reg (shr a n))
                                    (Time (t + Instruction.timeSHR)))
evalSHRHappySpec = Refl

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

--The OR instruction performs a bitwise and between the top of stack and the
--register.
export
evalORHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval OR
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__orB64` s))
                                    (Time (t + Instruction.timeOR)))
evalORHappySpec = Refl

--The OR instruction underflows the stack if the stack is empty.
export
evalORUnderflowSpec : eval OR (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalORUnderflowSpec = Refl

--The XOR instruction performs a bitwise and between the top of stack and the
--register.
export
evalXORHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval XOR
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__xorB64` s))
                                    (Time (t + Instruction.timeXOR)))
evalXORHappySpec = Refl

--The XOR instruction underflows the stack if the stack is empty.
export
evalXORUnderflowSpec : eval XOR (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalXORUnderflowSpec = Refl

--The EQ instruction compares the register with top of stack, setting the
--register to 1 if equal, and 0 otherwise.
export
evalEQHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval EQ
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a == s then 1 else 0))
                                    (Time (t + Instruction.timeEQ)))
evalEQHappySpec = Refl

--The EQ instruction underflows the stack if the stack is empty.
export
evalEQUnderflowSpec : eval EQ (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalEQUnderflowSpec = Refl

--The LT instruction compares the register with top of stack, setting the
--register to 1 if the register is less than tos, and 0 otherwise.
export
evalLTHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval LT
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a < s then 1 else 0))
                                    (Time (t + Instruction.timeLT)))
evalLTHappySpec = Refl

--The LT instruction underflows the stack if the stack is empty.
export
evalLTUnderflowSpec : eval LT (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalLTUnderflowSpec = Refl

--The GT instruction compares the register with top of stack, setting the
--register to 1 if the register is greater than tos, and 0 otherwise.
export
evalGTHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval GT
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a > s then 1 else 0))
                                    (Time (t + Instruction.timeGT)))
evalGTHappySpec = Refl

--The GT instruction underflows the stack if the stack is empty.
export
evalGTUnderflowSpec : eval GT (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalGTUnderflowSpec = Refl

--The LE instruction compares the register with top of stack, setting the
--register to 1 if the register is less than or equal to tos, and 0 otherwise.
export
evalLEHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval LE
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a <= s then 1 else 0))
                                    (Time (t + Instruction.timeLE)))
evalLEHappySpec = Refl

--The LE instruction underflows the stack if the stack is empty.
export
evalLEUnderflowSpec : eval LE (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalLEUnderflowSpec = Refl

--The GE instruction compares the register with top of stack, setting the
--register to 1 if the register is greater than / equal to tos, and 0 otherwise.
export
evalGEHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval GE
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a >= s then 1 else 0))
                                    (Time (t + Instruction.timeGE)))
evalGEHappySpec = Refl

--The GE instruction underflows the stack if the stack is empty.
export
evalGEUnderflowSpec : eval GE (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalGEUnderflowSpec = Refl

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

--The SUB instruction subtracts the top of stack from the register.
export
evalSUBHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval SUB
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__subB64` s))
                                    (Time (t + Instruction.timeSUB)))
evalSUBHappySpec = Refl

--The SUB instruction underflows the stack if the stack is empty.
export
evalSUBUnderflowSpec : eval SUB (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalSUBUnderflowSpec = Refl

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

--The MOD instruction finds the modulus of the register with respect to the top
--of stack.
export
evalMODHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval MOD
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = do
                            res <- evalMod a s
                            comp (Mach
                                    (StackFromList ss)
                                    (Reg res)
                                    (Time (t + Instruction.timeMOD)))
evalMODHappySpec = Refl

--The MOD instruction underflows the stack if the stack is empty.
export
evalMODUnderflowSpec : eval MOD (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalMODUnderflowSpec = Refl

--The MOD instruction causes a DivideByZeroException the top of stack is zero.
export
evalMODDivideByZeroSpec : {ss : List Bits64} -> {s, a, t : Bits64}
                        -> eval MOD
                           (Mach (StackFromList (0 :: ss)) (Reg a) (Time t))
                            = exception DivideByZeroException
evalMODDivideByZeroSpec = Refl

--The DIV instruction divides the register by the top of stack.
export
evalDIVHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval DIV
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = do
                            res <- evalDiv a s
                            comp (Mach
                                    (StackFromList ss)
                                    (Reg res)
                                    (Time (t + Instruction.timeDIV)))
evalDIVHappySpec = Refl

--The DIV instruction underflows the stack if the stack is empty.
export
evalDIVUnderflowSpec : eval DIV (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalDIVUnderflowSpec = Refl

--The DIV instruction causes a DivideByZeroException the top of stack is zero.
export
evalDIVDivideByZeroSpec : {ss : List Bits64} -> {s, a, t : Bits64}
                        -> eval DIV
                           (Mach (StackFromList (0 :: ss)) (Reg a) (Time t))
                            = exception DivideByZeroException
evalDIVDivideByZeroSpec = Refl
