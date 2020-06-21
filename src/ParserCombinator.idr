module ParserCombinator

%access public export
%default total

--Simple parser record.
record Parser (a : Type) where
    constructor MkParser
    parse : (List Char -> List (Pair a (List Char)))

--Run a parser, returning either an error message or the type.
runParser : Parser a -> String -> Either String a
runParser (MkParser p) s =
    case p (unpack s) of
        [(res, [])] => Right res
        [(res, rs)] => Left "Did not consume all input."
        _ => Left "Parser error."

--Parser to consume a single character.
char : Char -> Parser Char
char ch =
        MkParser charParser
    where
        charParser : (List Char -> List (Pair Char (List Char)))
        charParser [] = []
        charParser (c :: cs) =
            if c == ch
                then [(c, cs)]
                else []
