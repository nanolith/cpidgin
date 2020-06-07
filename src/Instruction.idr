module Instruction

import Data.Bits
import Data.List

--List of all instructions supported by cpidgin IR.
public export
data Instruction =
      NOP
    | IMM Bits64

--The time to execute a NOP instruction.
export
timeNOP : Bits64
timeNOP = 1

--The time to execute an IMMediate instruction.
export
timeIMM : Bits64
timeIMM = 2
