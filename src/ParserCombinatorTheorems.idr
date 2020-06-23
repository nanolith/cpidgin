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

--Proof that natural consumes a number.
naturalHappySpec : 
    runParser ParserCombinator.natural (unpack "77") = Right 77
naturalHappySpec = Refl

--Proof that natural fails if the input is not a number.
naturalNoMatchFailureSpec : 
    runParser ParserCombinator.natural ['a']
                            = Left UnsatisfiedPredicateError
naturalNoMatchFailureSpec = Refl

--Proof that natural fails if the input is empty.
naturalEmptyFailureSpec : 
    runParser ParserCombinator.natural [] = Left UnexpectedEndOfInputError
naturalEmptyFailureSpec = Refl

--Proof that natural fails if it does not consume all input.
naturalNotEOFFailureSpec : 
    runParser ParserCombinator.natural ['5', '.']
                            = Left NotAllInputConsumedError
naturalNotEOFFailureSpec = Refl

--Proof that string consumes a string.
stringHappySpec : 
    runParser (string "combinator") (unpack "combinator") = Right "combinator"
stringHappySpec = Refl

--Proof that string fails if the input is not a matching string.
stringNoMatchFailureSpec : 
    runParser (string "combinator") ['a']
                            = Left (GeneralError "Expecting c and got a")
stringNoMatchFailureSpec = Refl

--Proof that string fails if the input is empty.
stringEmptyFailureSpec : 
    runParser (string "combinator") [] = Left UnexpectedEndOfInputError
stringEmptyFailureSpec = Refl

--Proof that string fails if it does not consume all input.
stringNotEOFFailureSpec : 
    runParser (string "beach") (unpack "beaches")
                            = Left NotAllInputConsumedError
stringNotEOFFailureSpec = Refl

--Proof that spaces consumes a string of spaces.
spacesHappySpec : 
    runParser ParserCombinator.spaces (unpack "\n\r\t ") = Right "\n\r\t "
spacesHappySpec = Refl

--Proof that spaces doesn't chew up non-spaces.
spacesNoMatchSpec : 
    runParser (ParserCombinator.spaces *> char 'a') ['a']
                            = Right 'a'
spacesNoMatchSpec = Refl

--Proof that spaces fails if it does not consume all input.
spacesNotEOFFailureSpec : 
    runParser ParserCombinator.spaces (unpack " abc")
                            = Left NotAllInputConsumedError
spacesNotEOFFailureSpec = Refl

--Proof that reserved consumes a string.
reservedHappySpec : 
    runParser (reserved "combinator") (unpack "combinator") = Right "combinator"
reservedHappySpec = Refl

--Proof that reserved fails if the input is not a matching keyword.
reservedNoMatchFailureSpec : 
    runParser (reserved "if") (unpack "while")
                            = Left (GeneralError "Expecting i and got w")
reservedNoMatchFailureSpec = Refl

--Proof that reserved fails if the input is empty.
reservedEmptyFailureSpec : 
    runParser (reserved "combinator") [] = Left UnexpectedEndOfInputError
reservedEmptyFailureSpec = Refl

--Proof that reserved fails if it does not consume all input.
reservedNotEOFFailureSpec : 
    runParser (reserved "beach") (unpack "beaches")
                            = Left NotAllInputConsumedError
reservedNotEOFFailureSpec = Refl

--Proof that reserved successfully clears whitespace at the end of input.
reservedSpacesEOFSpec : 
    runParser (reserved "beach") (unpack "beach\n    ")
                            = Right "beach"
reservedSpacesEOFSpec = Refl

--Proof that digit consumes a digit.
digitHappySpec : 
    runParser ParserCombinator.digit ['7'] = Right '7'
digitHappySpec = Refl

--Proof that digit fails if the input is not a digit.
digitNoMatchFailureSpec : 
    runParser ParserCombinator.digit ['a']
                            = Left UnsatisfiedPredicateError
digitNoMatchFailureSpec = Refl

--Proof that digit fails if the input is empty.
digitEmptyFailureSpec : 
    runParser ParserCombinator.digit [] = Left UnexpectedEndOfInputError
digitEmptyFailureSpec = Refl

--Proof that digit fails if it does not consume all input.
digitNotEOFFailureSpec : 
    runParser ParserCombinator.natural ['5', '.']
                            = Left NotAllInputConsumedError
digitNotEOFFailureSpec = Refl
