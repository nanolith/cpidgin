module ParserCombinatorTheorems

import Data.So
import ParserCombinator

%default total

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

--Helper function for singleStringParseAppSpec
singleStringHelperApp : Parser String
singleStringHelperApp = pure singleton <*> char 'x'

--Proof that we can build a string using our single string helper.
singleStringParseAppSpec :
    runParser ParserCombinatorTheorems.singleStringHelperApp ['x'] = Right "x"
singleStringParseAppSpec = Refl

--Helper function for singleStringParseMonadSpec
singleStringHelperMonad : Parser String
singleStringHelperMonad = do
    x <- char 'x'
    pure $ singleton x

--Proof that we can build a string using our single string helper.
singleStringParseMonadSpec :
    runParser ParserCombinatorTheorems.singleStringHelperMonad ['x'] = Right "x"
singleStringParseMonadSpec = Refl
