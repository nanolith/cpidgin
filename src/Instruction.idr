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
    | ADD
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

--The time to execute an ADD instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--ADD (1 ins)
--FETCH (1 ins)
export
timeADD : Bits64
timeADD = 4

--The time to execute a MUL instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--MUL (5 ins)
--FETCH (1 ins)
export
timeMUL : Bits64
timeMUL = 8
