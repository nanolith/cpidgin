module ParserCombinator

import Data.So

%access public export
%default total

--Simple parser record.
record Parser (a : Type) where
    constructor MkParser
    parse : (List Char -> List (Pair a (List Char)))

--Run a parser, returning either an error message or the type.
runParser : Parser a -> List Char -> Either String a
runParser (MkParser p) cs =
    case p cs of
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

--Proof that char consumes one input.
charHappySpec : (ch : Char) -> So (ch == ch)
                -> runParser (char ch) [ch] = Right ch
charHappySpec ch l with (ch == ch)
    | True = Refl
    | False = absurd l

--Proof that char fails if the two inputs don't match.
charNoMatchFailureSpec : (ch, notch : Char) -> So (notch /= ch)
                        -> runParser (char ch) [notch] = Left "Parser error."
charNoMatchFailureSpec ch notch l with (notch == ch)
    | True = absurd l
    | False = Refl

--Proof that char fails if the input is empty.
charEmptyFailureSpec : (ch : Char)
                     -> runParser (char ch) [] = Left "Parser error."
charEmptyFailureSpec ch = Refl

--Proof that char fails if it does not consume all input.
charNotEOFFailureSpec : (ch,notch : Char) -> So (ch == ch)
                     -> runParser (char ch) [ch,notch]
                            = Left "Did not consume all input."
charNotEOFFailureSpec ch notch l with (ch == ch)
    | True = Refl
    | False = absurd l
