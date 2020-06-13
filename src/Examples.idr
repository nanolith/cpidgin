module Examples

import Instruction
import Machine
import Prelude.Monad

--one plus one instructions
private
onePlusOneInstr : List Instruction
onePlusOneInstr =
    [IMM 1,
     PUSH,
     ADD]

--simple function that adds one and one, saving the result in a.
onePlusOne : Either MachineException Bits64
onePlusOne =
    callFunction onePlusOneInstr []

--proof that running this example results in 2.
private
onePlusOneSpec : Examples.onePlusOne = Right 2
onePlusOneSpec = Refl

--x * y + z instructions
private
xyPlusZInsttr : List Instruction
xyPlusZInsttr =
    [MUL,
     ADD]

--proof that running this example results in the symbol x * y + z
private
xyPlusZSpec : {x, y, z : Bits64}
                -> callFunction Examples.xyPlusZInsttr [x, y, z]
                        = Right (x * y + z)
xyPlusZSpec = Refl
