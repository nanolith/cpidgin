module ParserTheorems

import AST
import Parser
import ParserCombinator

-- Parse a positive integer and turn it into a NumericConst.
parseNumericPositiveSpec : 
    runParser Parser.parseNumeric (unpack "47")
        = Right (NumericConst 47 Nothing)
parseNumericPositiveSpec = Refl

-- Parse a negative integer and turn it into a NumericConst.
parseNumericNegativeSpec : 
    runParser Parser.parseNumeric (unpack "-47")
        = Right (NumericConst (-47) Nothing)
parseNumericNegativeSpec = Refl

-- Parse an integer starting with a space.
parseNumericWithSpaceSpec : 
    runParser Parser.parseNumeric (unpack "47 ")
        = Right (NumericConst 47 Nothing)
parseNumericWithSpaceSpec = Refl
