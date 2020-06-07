module Instruction

import Data.Bits
import Data.List

--List of all instructions supported by cpidgin IR.
public export
data Instruction =
      NOP

--The time to execute a NOP instruction.
export
timeNOP : Bits64
timeNOP = 1
