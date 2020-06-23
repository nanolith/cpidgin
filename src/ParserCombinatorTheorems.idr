module ParserCombinatorTheorems

import Data.So
import ParserCombinator

%default total

--Proof that item consumes one character.
itemHappySpec : (ch : Char)
             -> runParser ParserCombinator.item [ch] = Right ch
itemHappySpec ch = Refl

--Proof that item fails on empty input.
itemEmptyFailureSpec : 
                runParser ParserCombinator.item []
                    = Left UnexpectedEndOfInputError
itemEmptyFailureSpec = Refl

--Proof that char consumes one character.
charHappySpec : (ch : Char) -> So (ch == ch)
                -> runParser (char ch) [ch] = Right ch
charHappySpec ch l with (ch == ch)
    | True = Refl
    | False = absurd l

--Proof that char fails if the two inputs don't match.
charNoMatchFailureSpec : (ch, notch : Char) -> So (notch /= ch)
                        -> runParser (char ch) [notch]
                            = Left (GeneralError
                                ("Expecting " ++ singleton ch ++ " and got "
                                    ++ singleton notch))
charNoMatchFailureSpec ch notch l with (notch == ch)
    | True = absurd l
    | False = Refl

--Proof that char fails if the input is empty.
charEmptyFailureSpec : (ch : Char)
                     -> runParser (char ch) [] = Left UnexpectedEndOfInputError
charEmptyFailureSpec ch = Refl

--Proof that char fails if it does not consume all input.
charNotEOFFailureSpec : (ch,notch : Char) -> So (ch == ch)
                     -> runParser (char ch) [ch,notch]
                            = Left NotAllInputConsumedError
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

--Proof that parsing a value with two alternatives passes.
alternativeParseLHSSpec : 
    runParser (char 'x' <|> char 'y') ['x'] = Right 'x'
alternativeParseLHSSpec = Refl

--Proof that parsing a value with two alternatives passes.
alternativeParseRHSSpec : 
    runParser (char 'x' <|> char 'y') ['y'] = Right 'y'
alternativeParseRHSSpec = Refl

--Many against an empty list produces an empty list.
manyEmptyStringSpec :
    runParser (many (char 'x')) [] = Right []
manyEmptyStringSpec = Refl

--A sequence is parsed in the right order.
manySequenceOrderSpec :
    runParser (many (char 'a' <|> char 'b' <|> char 'c')) (unpack "abc")
        = Right (unpack "abc")
manySequenceOrderSpec = Refl

--An arbitrary long sequence is processed with many.
manySpec :
    runParser (many (char 'x')) (unpack "xxxxxxxxxxxxxxxx")
        = Right (unpack "xxxxxxxxxxxxxxxx")
manySpec = Refl

--Some against an empty list produces an error.
someEmptyStringSpec :
    runParser (some (char 'x')) [] = Left UnexpectedEndOfInputError
someEmptyStringSpec = Refl

--A sequence is parsed in the right order.
someSequenceOrderSpec :
    runParser (some (char 'a' <|> char 'b' <|> char 'c')) (unpack "cba")
        = Right (unpack "cba")
someSequenceOrderSpec = Refl

--An arbitrary long sequence is processed with some.
someSpec :
    runParser (some (char 'y')) (unpack "yyyyyyyyyyyyyyyy")
        = Right (unpack "yyyyyyyyyyyyyyyy")
someSpec = Refl

--Satisfy returns an UnexpectedEndOfInputError on empty.
satisfyEOFSpec : 
    runParser (satisfy Prelude.Chars.isDigit) []
        = Left UnexpectedEndOfInputError
satisfyEOFSpec = Refl

--Satisfy consumes a matching character.
satisfyNumSpec : 
    runParser (satisfy Prelude.Chars.isDigit) ['9']
        = Right '9'
satisfyNumSpec = Refl

--Satisfy errors on a non-matching character.
satisfyNoMatchSpec : 
    runParser (satisfy Prelude.Chars.isDigit) ['A']
        = Left UnsatisfiedPredicateError
satisfyNoMatchSpec = Refl

--Satisfy works with some.
satisfySomeSpec : 
    runParser (some $ satisfy Prelude.Chars.isDigit) (unpack "0123456789")
        = Right $ unpack "0123456789"
satisfySomeSpec = Refl

--oneOf returns an UnexpectedEndOfInputError on empty.
oneOfEOFSpec : 
    runParser (oneOf ['a', 'b', 'c']) []
        = Left UnexpectedEndOfInputError
oneOfEOFSpec = Refl

--oneOf consumes a matching character.
oneOfMatchingCharSpec : 
    runParser (oneOf ['a', 'b', 'c']) ['c'] = Right 'c'
oneOfMatchingCharSpec = Refl

--oneOf errors on a non-matching character.
oneOfNoMatchSpec : 
    runParser (oneOf ['a', 'b', 'c']) ['x'] = Left UnsatisfiedPredicateError
oneOfNoMatchSpec = Refl

--oneOf works with some.
oneOfSomeSpec : 
    runParser (some $ oneOf ['a', 'b', 'c']) (unpack "abcba")
        = Right $ unpack "abcba"
oneOfSomeSpec = Refl
