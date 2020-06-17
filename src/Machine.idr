module Machine

import Data.Bits
import Data.List
import Data.So
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
ushr : Bits64 -> Nat -> Bits64
ushr x Z = x
ushr x (S n) = ushr (assert_total $ prim__udivB64 x 2) n

public export total
evalMod : Bits64 -> Bits64 -> Either MachineException Bits64
evalMod x y with (y == 0)
--the zero case has a hole in urem, so we throw an exception
    | True  = Left DivideByZeroException
--since y is non-zero, there is no longer a hole. Force totality.
    | False = assert_total $ Right $ x `prim__uremB64` y

public export total
evalDiv : Bits64 -> Bits64 -> Either MachineException Bits64
evalDiv x y with (y == 0)
--the zero case has a hole in sdiv, so we throw an exception
    | True  = Left DivideByZeroException
--since y is non-zero, there is no longer a hole. Force totality.
    | False = assert_total $ Right $ x `prim__sdivB64` y

public export total
evalUDiv : Bits64 -> Bits64 -> Either MachineException Bits64
evalUDiv x y with (y == 0)
--the zero case has a hole in sdiv, so we throw an exception
    | True  = Left DivideByZeroException
--since y is non-zero, there is no longer a hole. Force totality.
    | False = assert_total $ Right $ x `prim__udivB64` y

public export total
dupList : Nat -> Bits64 -> List Bits64 -> List Bits64
dupList Z _ ss = ss
dupList (S n) s ss = dupList n s (s :: ss)

public export total
readNth : Nat -> List Bits64 -> Either MachineException Bits64
readNth Z (r :: rs) = Right r
readNth _ [] = Left StackUnderflowException
readNth (S n) (r :: rs) = readNth n rs

public export total
removeNth : Nat -> List Bits64 -> List Bits64
removeNth Z (r :: rs) = rs
removeNth _ [] = []
removeNth (S n) (r :: rs) = r :: removeNth n rs

--Evaluate a single instruction in our virtual machine, and update machine state
--accordingly.
public export
eval : Instruction -> Machine -> Either MachineException Machine
--execute the NOP instruction.
eval NOP (Mach s r (Time t)) =
    comp (Mach s r (Time (t + Instruction.timeNOP)))
--execute the IMM instruction.
eval (IMM i) (Mach s _ (Time t)) =
    comp (Mach s (Reg i) (Time (t + Instruction.timeIMM)))
--execute the PUSH instruction.
eval PUSH (Mach (StackFromList ss) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList (a :: ss))
            (Reg a)
            (Time (t + Instruction.timePUSH)))
--execute the POP instruction.
eval POP (Mach (StackFromList (s :: ss)) _ (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg s)
            (Time (t + Instruction.timePOP)))
--handle POP instruction stack underflow exception.
eval POP (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the SEL instruction
eval (SEL n) (Mach (StackFromList (s :: ss)) _ (Time t)) = do
    val <- readNth n (s :: ss)
    comp (Mach
            (StackFromList $ removeNth n (s :: ss))
            (Reg val)
            (Time (t + Instruction.timeSEL)))
--handle SEL instruction stack underflow exception.
eval (SEL _) (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the SHL instruction.
eval (SHL n) (Mach s (Reg a) (Time t)) =
    comp (Mach
            s
            (Reg (shl a n))
            (Time (t + Instruction.timeSHL)))
--execute the SHR instruction.
eval (SHR n) (Mach s (Reg a) (Time t)) =
    comp (Mach
            s
            (Reg (shr a n))
            (Time (t + Instruction.timeSHR)))
--execute the USHR instruction.
eval (USHR n) (Mach s (Reg a) (Time t)) =
    comp (Mach
            s
            (Reg (ushr a n))
            (Time (t + Instruction.timeUSHR)))
--execute the AND instruction.
eval AND (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__andB64` s))
            (Time (t + Instruction.timeAND)))
--handle AND instruction stack underflow exception.
eval AND (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the OR instruction.
eval OR (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__orB64` s))
            (Time (t + Instruction.timeOR)))
--handle OR instruction stack underflow exception.
eval OR (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the XOR instruction.
eval XOR (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__xorB64` s))
            (Time (t + Instruction.timeXOR)))
--handle XOR instruction stack underflow exception.
eval XOR (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the EQ instruction.
eval EQ (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a == s then 1 else 0))
            (Time (t + Instruction.timeEQ)))
--handle EQ instruction stack underflow exception.
eval EQ (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the LT instruction.
eval LT (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a < s then 1 else 0))
            (Time (t + Instruction.timeLT)))
--handle LT instruction stack underflow exception.
eval LT (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the GT instruction.
eval GT (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a > s then 1 else 0))
            (Time (t + Instruction.timeGT)))
--handle GT instruction stack underflow exception.
eval GT (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the LE instruction.
eval LE (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a <= s then 1 else 0))
            (Time (t + Instruction.timeLE)))
--handle LE instruction stack underflow exception.
eval LE (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the GE instruction.
eval GE (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (if a >= s then 1 else 0))
            (Time (t + Instruction.timeLE)))
--handle GE instruction stack underflow exception.
eval GE (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the ADD instruction.
eval ADD (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a + s))
            (Time (t + Instruction.timeADD)))
--handle ADD instruction stack underflow exception.
eval ADD (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the SUB instruction.
eval SUB (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a `prim__subB64` s))
            (Time (t + Instruction.timeSUB)))
--handle SUB instruction stack underflow exception.
eval SUB (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the MUL instruction.
eval MUL (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) =
    comp (Mach
            (StackFromList ss)
            (Reg (a * s))
            (Time (t + Instruction.timeMUL)))
--handle MUL instruction stack underflow exception.
eval MUL (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the MOD instruction.
eval MOD (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) = do
    res <- evalMod a s
    comp (Mach
            (StackFromList ss)
            (Reg res)
            (Time (t + Instruction.timeMOD)))
--handle MOD instruction stack underflow exception.
eval MOD (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the DIV instruction.
eval DIV (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) = do
    res <- evalDiv a s
    comp (Mach
            (StackFromList ss)
            (Reg res)
            (Time (t + Instruction.timeDIV)))
--handle DIV instruction stack underflow exception.
eval DIV (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--execute the UDIV instruction.
eval UDIV (Mach (StackFromList (s :: ss)) (Reg a) (Time t)) = do
    res <- evalUDiv a s
    comp (Mach
            (StackFromList ss)
            (Reg res)
            (Time (t + Instruction.timeUDIV)))
--handle UDIV instruction stack underflow exception.
eval UDIV (Mach (StackFromList []) _ _) =
    exception StackUnderflowException
--handle any other case
eval _ _ = exception (NotImplementedException "Unknown instruction.")

--evaluate a sequence of instructions
public export
evalSequence : List Instruction -> Machine -> Either MachineException Machine
evalSequence ins mach =
    foldlM (flip eval) mach ins

--push arguments into a machine
public export
pushArgs : List Bits64 -> Machine -> Either MachineException Machine
pushArgs [] mach = Right mach
pushArgs (x :: []) (Mach s (Reg _) (Time t)) =
    Right $ Mach s (Reg x) (Time (t + Instruction.timePUSH))
pushArgs (x :: xs) (Mach (StackFromList ss) r (Time t)) =
    pushArgs xs
            (Mach
                (StackFromList (x ::ss))
                r
                (Time (t + Instruction.timePUSH)))

--evaluate a function with a given list of arguments
public export
evalFunction : List Instruction -> List Bits64 -> Machine
                -> Either MachineException Machine
evalFunction ins args mach =
    pushArgs (reverse args) mach >>= evalSequence ins

--call a function, returning its return value according to the ABI.
public export
callFunction : List Instruction -> List Bits64 -> Either MachineException Bits64
callFunction ins args =
    evalFunction ins args emptyMachine >>= (\x => pure $ machineRegister x)

--The NOP instruction takes one cycle and does not otherwise change machine
--state.
export total
evalNOPSpec : {s : Stack} -> {r : Register} -> {t : Bits64}
                -> eval NOP (Mach s r (Time t))
                    = comp (Mach s r (Time (t + Instruction.timeNOP)))
evalNOPSpec = Refl

--The IMM instruction loads the given immediate value into the register.
export total
evalIMMSpec : {s : Stack} -> {i, t : Bits64}
                -> eval (IMM i) (Mach s _ (Time t))
                    = comp (Mach s (Reg i) (Time (t + Instruction.timeIMM)))
evalIMMSpec = Refl

--The PUSH instruction writes the register to the stack.
export total
evalPUSHSpec : {ss : List Bits64} -> {a, t : Bits64}
                -> eval PUSH (Mach (StackFromList ss) (Reg a) (Time t))
                    = comp (Mach
                                (StackFromList (a :: ss))
                                (Reg a)
                                (Time (t + Instruction.timePUSH)))
evalPUSHSpec = Refl

--The POP instruction reads the register from the stack.
export total
evalPOPHappySpec : {ss : List Bits64} -> {s, t : Bits64}
                    -> eval POP (Mach (StackFromList (s :: ss)) _ (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg s)
                                    (Time (t + Instruction.timePOP)))
evalPOPHappySpec = Refl

--The POP instruction underflows the stack if the stack is empty.
export total
evalPOPUnderflowSpec : eval POP (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalPOPUnderflowSpec = Refl

--helper lemma for reducing dupList
export total
dupListHelperLemma : (ss : List Bits64) -> (s : Bits64) -> (n : Nat)
                     -> (dupList (S n) s ss) = (s :: dupList n s ss)
dupListHelperLemma ss s Z = Refl
dupListHelperLemma ss s (S m) =
    let prf = dupListHelperLemma (s :: ss) s m in
    rewrite prf in Refl

--helper lemma for reducing readNth
export total
readNthDupListHelperLemma : (ss : List Bits64) -> (s : Bits64) -> (n : Nat)
                          -> readNth n (s :: dupList n s ss) = Right s
readNthDupListHelperLemma ss s Z = Refl
readNthDupListHelperLemma ss s (S m) =
    let h1 = dupListHelperLemma ss s m in
    rewrite h1 in
    let h2 = readNthDupListHelperLemma ss s m in
    rewrite h2 in Refl

--helper lemma for reducing removeNth
export total
removeNthDupListHelperLemma : (ss : List Bits64) -> (s : Bits64) -> (n : Nat)
                            -> removeNth n (dupList n s (s :: ss))
                                = dupList n s ss
removeNthDupListHelperLemma ss s Z = Refl
removeNthDupListHelperLemma ss s (S m) =
    let h1 = dupListHelperLemma (s :: ss) s m in
    rewrite h1 in
    let h2 = removeNthDupListHelperLemma ss s m in
    rewrite h2 in
    let h3 = dupListHelperLemma ss s m in
    rewrite h3 in Refl

--total proof for evalSELHappySpec... tracking down unification error in
--Idris.

--The SEL instruction reads the stack at the given offset into the register.
{--
export total
evalSELHappySpec : (ss : List Bits64) -> (s, t : Bits64) -> (r : Register)
                    -> (n : Nat)
                    -> eval (SEL n)
                            (Mach (StackFromList (dupList (S n) s ss))
                                   r (Time t))
                        = comp (Mach
                                    (StackFromList (dupList n s ss))
                                    (Reg s)
                                    (Time (t + Instruction.timeSEL)))
evalSELHappySpec ss s t r Z = Refl
evalSELHappySpec ss s t r (S m) =
    let h1 = dupListHelperLemma (s :: ss) s m in
    let h2 = removeNthDupListHelperLemma ss s m in
    let h3 = dupListHelperLemma ss s m in
    let h4 = readNthDupListHelperLemma ss s m in
    rewrite h1 in
    rewrite h2 in
    rewrite h3 in
    rewrite h4 in Refl
--}

--The SEL instruction underflows the stack if the stack is empty.
export total
evalSELUnderflowSpec : eval (SEL _) (Mach (StackFromList []) _ _)
                            = exception StackUnderflowException
evalSELUnderflowSpec = Refl

--The SHL instruction shifts the register to the left by the IMM number of bits.
export total
evalSHLHappySpec : {n : Nat} -> {s : Stack} -> {a, t : Bits64}
                    -> eval (SHL n)
                            (Mach s (Reg a) (Time t))
                        = comp (Mach
                                    s
                                    (Reg (shl a n))
                                    (Time (t + Instruction.timeSHL)))
evalSHLHappySpec = Refl

--The SHR instruction shifts the reg to the right by the IMM number of bits.
export total
evalSHRHappySpec : {n : Nat} -> {s : Stack} -> {a, t : Bits64}
                    -> eval (SHR n)
                            (Mach s (Reg a) (Time t))
                        = comp (Mach
                                    s
                                    (Reg (shr a n))
                                    (Time (t + Instruction.timeSHR)))
evalSHRHappySpec = Refl

--The USHR instruction shifts the reg to the right by the IMM number of bits,
--without sign extension.
export total
evalUSHRHappySpec : {n : Nat} -> {s : Stack} -> {a, t : Bits64}
                    -> eval (USHR n)
                            (Mach s (Reg a) (Time t))
                        = comp (Mach
                                    s
                                    (Reg (ushr a n))
                                    (Time (t + Instruction.timeUSHR)))
evalUSHRHappySpec = Refl

--The AND instruction performs a bitwise and between the top of stack and the
--register.
export total
evalANDHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval AND
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__andB64` s))
                                    (Time (t + Instruction.timeAND)))
evalANDHappySpec = Refl

--The AND instruction underflows the stack if the stack is empty.
export total
evalANDUnderflowSpec : eval AND (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalANDUnderflowSpec = Refl

--The OR instruction performs a bitwise and between the top of stack and the
--register.
export total
evalORHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval OR
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__orB64` s))
                                    (Time (t + Instruction.timeOR)))
evalORHappySpec = Refl

--The OR instruction underflows the stack if the stack is empty.
export total
evalORUnderflowSpec : eval OR (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalORUnderflowSpec = Refl

--The XOR instruction performs a bitwise and between the top of stack and the
--register.
export total
evalXORHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval XOR
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__xorB64` s))
                                    (Time (t + Instruction.timeXOR)))
evalXORHappySpec = Refl

--The XOR instruction underflows the stack if the stack is empty.
export total
evalXORUnderflowSpec : eval XOR (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalXORUnderflowSpec = Refl

--The EQ instruction compares the register with top of stack, setting the
--register to 1 if equal, and 0 otherwise.
export total
evalEQHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval EQ
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a == s then 1 else 0))
                                    (Time (t + Instruction.timeEQ)))
evalEQHappySpec = Refl

--The EQ instruction underflows the stack if the stack is empty.
export total
evalEQUnderflowSpec : eval EQ (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalEQUnderflowSpec = Refl

--The LT instruction compares the register with top of stack, setting the
--register to 1 if the register is less than tos, and 0 otherwise.
export total
evalLTHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval LT
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a < s then 1 else 0))
                                    (Time (t + Instruction.timeLT)))
evalLTHappySpec = Refl

--The LT instruction underflows the stack if the stack is empty.
export total
evalLTUnderflowSpec : eval LT (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalLTUnderflowSpec = Refl

--The GT instruction compares the register with top of stack, setting the
--register to 1 if the register is greater than tos, and 0 otherwise.
export total
evalGTHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval GT
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a > s then 1 else 0))
                                    (Time (t + Instruction.timeGT)))
evalGTHappySpec = Refl

--The GT instruction underflows the stack if the stack is empty.
export total
evalGTUnderflowSpec : eval GT (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalGTUnderflowSpec = Refl

--The LE instruction compares the register with top of stack, setting the
--register to 1 if the register is less than or equal to tos, and 0 otherwise.
export total
evalLEHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval LE
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a <= s then 1 else 0))
                                    (Time (t + Instruction.timeLE)))
evalLEHappySpec = Refl

--The LE instruction underflows the stack if the stack is empty.
export total
evalLEUnderflowSpec : eval LE (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalLEUnderflowSpec = Refl

--The GE instruction compares the register with top of stack, setting the
--register to 1 if the register is greater than / equal to tos, and 0 otherwise.
export total
evalGEHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval GE
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (if a >= s then 1 else 0))
                                    (Time (t + Instruction.timeGE)))
evalGEHappySpec = Refl

--The GE instruction underflows the stack if the stack is empty.
export total
evalGEUnderflowSpec : eval GE (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalGEUnderflowSpec = Refl

--The ADD instruction adds the top of stack to the register.
export total
evalADDHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval ADD
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a + s))
                                    (Time (t + Instruction.timeADD)))
evalADDHappySpec = Refl

--The ADD instruction underflows the stack if the stack is empty.
export total
evalADDUnderflowSpec : eval ADD (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalADDUnderflowSpec = Refl

--The SUB instruction subtracts the top of stack from the register.
export total
evalSUBHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval SUB
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a `prim__subB64` s))
                                    (Time (t + Instruction.timeSUB)))
evalSUBHappySpec = Refl

--The SUB instruction underflows the stack if the stack is empty.
export total
evalSUBUnderflowSpec : eval SUB (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalSUBUnderflowSpec = Refl

--The MUL instruction multiplies the top of stack with the register.
export total
evalMULHappySpec : {ss : List Bits64} -> {s, a, t : Bits64}
                    -> eval MUL
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (a * s))
                                    (Time (t + Instruction.timeMUL)))
evalMULHappySpec = Refl

--The MUL instruction underflows the stack if the stack is empty.
export total
evalMULUnderflowSpec : eval MUL (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalMULUnderflowSpec = Refl

--The MOD instruction finds the modulus of the register with respect to the top
--of stack.
export --total
evalMODHappySpec : {ss : List Bits64} -> {a, t : Bits64} -> (s : Bits64)
                    -> So (s /= 0)
                    -> eval MOD
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (prim__uremB64 a s))
                                    (Time (t + Instruction.timeMOD)))
evalMODHappySpec s l with (s == 0)
    | True  = absurd l
    | False = Refl

--The MOD instruction underflows the stack if the stack is empty.
export total
evalMODUnderflowSpec : eval MOD (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalMODUnderflowSpec = Refl

--The MOD instruction causes a DivideByZeroException the top of stack is zero.
export total
evalMODDivideByZeroSpec : {ss : List Bits64} -> {s, a, t : Bits64}
                        -> eval MOD
                           (Mach (StackFromList (0 :: ss)) (Reg a) (Time t))
                            = exception DivideByZeroException
evalMODDivideByZeroSpec = Refl

--The DIV instruction divides the register by the top of stack.
export --total
evalDIVHappySpec : {ss : List Bits64} -> {a, t : Bits64} -> (s : Bits64)
                    -> So (s /= 0)
                    -> eval DIV
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (prim__sdivB64 a s))
                                    (Time (t + Instruction.timeDIV)))
evalDIVHappySpec s l with (s == 0)
    | True  = absurd l
    | False = Refl

--The DIV instruction underflows the stack if the stack is empty.
export total
evalDIVUnderflowSpec : eval DIV (Mach (StackFromList []) _ _)
                        = exception StackUnderflowException
evalDIVUnderflowSpec = Refl

--The DIV instruction causes a DivideByZeroException the top of stack is zero.
export total
evalDIVDivideByZeroSpec : {ss : List Bits64} -> {s, a, t : Bits64}
                        -> eval DIV
                           (Mach (StackFromList (0 :: ss)) (Reg a) (Time t))
                            = exception DivideByZeroException
evalDIVDivideByZeroSpec = Refl

--The UDIV instruction does an unsigned divide of the register by the top of
--stack.
export --total
evalUDIVHappySpec : {ss : List Bits64} -> {a, t : Bits64} -> (s : Bits64)
                    -> So (s /= 0)
                    -> eval UDIV
                           (Mach (StackFromList (s :: ss)) (Reg a) (Time t))
                        = comp (Mach
                                    (StackFromList ss)
                                    (Reg (prim__udivB64 a s))
                                    (Time (t + Instruction.timeUDIV)))
evalUDIVHappySpec s l with (s == 0)
    | True  = absurd l
    | False = Refl

--The UDIV instruction underflows the stack if the stack is empty.
export total
evalUDIVUnderflowSpec : eval UDIV (Mach (StackFromList []) _ _)
                            = exception StackUnderflowException
evalUDIVUnderflowSpec = Refl

--The UDIV instruction causes a DivideByZeroException the top of stack is zero.
export total
evalUDIVDivideByZeroSpec : {ss : List Bits64} -> {s, a, t : Bits64}
                        -> eval UDIV
                           (Mach (StackFromList (0 :: ss)) (Reg a) (Time t))
                            = exception DivideByZeroException
evalUDIVDivideByZeroSpec = Refl
