module Instruction

import Data.Bits
import Data.List

--List of all instructions supported by cpidgin IR.
public export
data Instruction =
      NOP
    | IMM Bits64
    | PUSH
    | POP
    | DUP
    | SHL Nat
    | AND
    | OR
    | XOR
    | EQ
    | LT
    | GT
    | LE
    | GE
    | ADD
    | SUB
    | MUL

--The time to execute a NOP instruction.
--FETCH (1 ins)
export
timeNOP : Bits64
timeNOP = 1

--The time to execute an IMMediate instruction.
--READ IMM (1 ins)
--WRITE REG (1 ins)
--FETCH (1 ins)
export
timeIMM : Bits64
timeIMM = 3

--The time to execute a PUSH instruction
--WRITE STACK (1 ins)
--INCREMENT STACK (1 ins)
--FETCH (1 ins)
export
timePUSH : Bits64
timePUSH = 3

--The time to execute a POP instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--FETCH (1 ins)
export
timePOP : Bits64
timePOP = 3

--The time to execute a DUP instruction.
--READ STACK (1 ins)
--WRITE STACK (1 ins)
--INCREMENT STACK (1 ins)
--FETCH (1 ins)
export
timeDUP : Bits64
timeDUP = 3

--The time to execute a SHL instruction
--READ IMM (1 ins)
--SHIFT (1 ins)
export
timeSHL : Bits64
timeSHL = 2

--The time to execute an AND instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--ADD (1 ins)
--FETCH (1 ins)
export
timeAND : Bits64
timeAND = 4

--The time to execute an OR instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--OR (1 ins)
--FETCH (1 ins)
export
timeOR : Bits64
timeOR = 4

--The time to execute an XOR instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--XOR (1 ins)
--FETCH (1 ins)
export
timeXOR : Bits64
timeXOR = 4

--The time to execute an EQ instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--EQ (1 ins)
--FETCH (1 ins)
export
timeEQ : Bits64
timeEQ = 4

--The time to execute an LT instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--LT (1 ins)
--FETCH (1 ins)
export
timeLT : Bits64
timeLT = 4

--The time to execute an LE instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--LE (1 ins)
--FETCH (1 ins)
export
timeLE : Bits64
timeLE = 4

--The time to execute a GE instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--GE (1 ins)
--FETCH (1 ins)
export
timeGE : Bits64
timeGE = 4

--The time to execute a GT instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--GT (1 ins)
--FETCH (1 ins)
export
timeGT : Bits64
timeGT = 4

--The time to execute an ADD instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--ADD (1 ins)
--FETCH (1 ins)
export
timeADD : Bits64
timeADD = 4

--The time to execute a SUB instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--SUB (1 ins)
--FETCH (1 ins)
export
timeSUB : Bits64
timeSUB = 4

--The time to execute a MUL instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--MUL (5 ins)
--FETCH (1 ins)
export
timeMUL : Bits64
timeMUL = 8
