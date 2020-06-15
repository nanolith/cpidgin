module Examples

import Data.So
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
xyPlusZInstr : List Instruction
xyPlusZInstr =
    [MUL,
     ADD]

--proof that running this example results in the symbol x * y + z
private
xyPlusZSpec : {x, y, z : Bits64}
                -> callFunction Examples.xyPlusZInstr [x, y, z]
                        = Right (x * y + z)
xyPlusZSpec = Refl

--x / y instructions
private
xDivYInstr : List Instruction
xDivYInstr =
    [DIV]

--proof that we can divide x by y when y is not 0.
private
xDivYSpec : (x : Bits64) -> (y : Bits64) -> So (y /= 0)
            -> callFunction Examples.xDivYInstr [x, y]
                = Right (prim__sdivB64 x y)
xDivYSpec x y l with (y == 0)
    | True = absurd l
    | False = Refl

--proof that if we attempt to divide by zero, we get an exception.
private
xDivZeroSpec : (x : Bits64)
            -> callFunction Examples.xDivYInstr [x, 0]
                = Left DivideByZeroException
xDivZeroSpec x = Refl

--x*x*z + y*y*z + x*y*z instructions
private
xxzPlusyyzPlusxyzInstr : List Instruction
xxzPlusyyzPlusxyzInstr =
    [PUSH,
     PUSH,
     MUL,
     PUSH,
     SEL 3,
     PUSH,
     PUSH,
     SEL 2,
     MUL,
     PUSH,
     SEL 3,
     PUSH,
     PUSH,
     MUL,
     PUSH,
     SEL 3,
     PUSH,
     PUSH,
     SEL 2,
     MUL,
     PUSH,
     SEL 3,
     ADD,
     PUSH,
     SEL 1,
     PUSH,
     SEL 2,
     PUSH,
     SEL 3,
     MUL,
     MUL,
     PUSH,
     SEL 1,
     ADD]

--proof that running this example results in the symbol x*x*z + y*y*z + x*y*z
private
xxzPlusyyzPlusxyzSpec : {x, y, z : Bits64}
                -> callFunction Examples.xxzPlusyyzPlusxyzInstr [x, y, z]
                        = Right (x*x*z + y*y*z + x*y*z)
xxzPlusyyzPlusxyzSpec = Refl
