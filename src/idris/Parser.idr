module Parser

import AST
import ParserCombinator

%access public export
%default total

mutual
    --parse a number as an AST element.
    parseNumeric : Parser AST
    parseNumeric = NumericConst <$> token integer <*> pure Nothing
