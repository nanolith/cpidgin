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
    foldlM (flip eval) emptyMachine onePlusOneInstr
        >>= (\x => pure $ machineRegister x)

--proof that running this example results in 2.
private
onePlusOneSpec : Examples.onePlusOne = Right 2
onePlusOneSpec = Refl
