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
    | SEL Nat
    | SHL Nat
    | SHR Nat
    | USHR Nat
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
    | DIV
    | UDIV
    | MOD

--The time to execute a NOP instruction.
--FETCH (1 ins)
public export
timeNOP : Bits64
timeNOP = 1

--The time to execute an IMMediate instruction.
--READ IMM (1 ins)
--WRITE REG (1 ins)
--FETCH (1 ins)
public export
timeIMM : Bits64
timeIMM = 3

--The time to execute a PUSH instruction
--WRITE STACK (1 ins)
--INCREMENT STACK (1 ins)
--FETCH (1 ins)
public export
timePUSH : Bits64
timePUSH = 3

--The time to execute a POP instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--FETCH (1 ins)
public export
timePOP : Bits64
timePOP = 3

--The time to execute a SEL instruction.
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--FETCH (1 ins)
public export
timeSEL : Bits64
timeSEL = 3

--The time to execute a SHL instruction
--READ IMM (1 ins)
--SHIFT (1 ins)
public export
timeSHL : Bits64
timeSHL = 2

--The time to execute a SHR instruction
--READ IMM (1 ins)
--SHIFT (1 ins)
public export
timeSHR : Bits64
timeSHR = 2

--The time to execute a USHR instruction
--READ IMM (1 ins)
--SHIFT (1 ins)
public export
timeUSHR : Bits64
timeUSHR = 2

--The time to execute an AND instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--ADD (1 ins)
--FETCH (1 ins)
public export
timeAND : Bits64
timeAND = 4

--The time to execute an OR instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--OR (1 ins)
--FETCH (1 ins)
public export
timeOR : Bits64
timeOR = 4

--The time to execute an XOR instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--XOR (1 ins)
--FETCH (1 ins)
public export
timeXOR : Bits64
timeXOR = 4

--The time to execute an EQ instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--EQ (1 ins)
--FETCH (1 ins)
public export
timeEQ : Bits64
timeEQ = 4

--The time to execute an LT instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--LT (1 ins)
--FETCH (1 ins)
public export
timeLT : Bits64
timeLT = 4

--The time to execute an LE instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--LE (1 ins)
--FETCH (1 ins)
public export
timeLE : Bits64
timeLE = 4

--The time to execute a GE instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--GE (1 ins)
--FETCH (1 ins)
public export
timeGE : Bits64
timeGE = 4

--The time to execute a GT instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--GT (1 ins)
--FETCH (1 ins)
public export
timeGT : Bits64
timeGT = 4

--The time to execute an ADD instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--ADD (1 ins)
--FETCH (1 ins)
public export
timeADD : Bits64
timeADD = 4

--The time to execute a SUB instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--SUB (1 ins)
--FETCH (1 ins)
public export
timeSUB : Bits64
timeSUB = 4

--The time to execute a MUL instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--MUL (5 ins)
--FETCH (1 ins)
public export
timeMUL : Bits64
timeMUL = 8

--The time to execute a DIV instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--DIV (5 ins)
--FETCH (1 ins)
public export
timeDIV : Bits64
timeDIV = 8

--The time to execute a UDIV instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--UDIV (5 ins)
--FETCH (1 ins)
public export
timeUDIV : Bits64
timeUDIV = 8

--The time to execute a MOD instruction
--READ STACK (1 ins)
--DECREMENT STACK (1 ins)
--MOD (5 ins)
--FETCH (1 ins)
public export
timeMOD : Bits64
timeMOD = 8
