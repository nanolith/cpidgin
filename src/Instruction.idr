module Instruction

import Data.Bits
import Data.List

public export
data Instruction =
      NOP

export
timeNOP : Bits64
timeNOP = 1
