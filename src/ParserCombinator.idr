module ParserCombinator

import Data.String

%access public export
%default total

--Errors that the Parser can return.
data ParserError =
      UnexpectedEndOfInputError
    | NotAllInputConsumedError
    | NoAlternativesError
    | UnsatisfiedPredicateError
    | GeneralError String

--Simple parser record.
record Parser (a : Type) where
    constructor MkParser
    parse : (List Char -> Either ParserError (Pair a (List Char)))

--Run a parser, returning either an error message or the type.
runParser : Parser a -> List Char -> Either ParserError a
runParser (MkParser p) cs =
    case p cs of
        Right (res, []) => Right res
        Right (res, rs) => Left NotAllInputConsumedError
        Left err => Left err

--We can make the Parser a Functor.
Functor Parser where
    map f (MkParser cs) = MkParser (\s =>
        case cs s of
            Right (a, s') => Right (f a, s')
            Left err => Left err)

--We can make the Parser an Applicative.
Applicative Parser where
    pure a = MkParser (\s => Right (a, s))
    (MkParser cs1) <*> (MkParser cs2) =
        MkParser $ (\s =>
            case cs1 s of
                Left err => Left err
                Right (f, s') =>
                    case cs2 s' of
                        Left err => Left err
                        Right (a, s'') => Right (f a, s''))

--We can make the Parser a Monad.
Monad Parser where
    (MkParser cs) >>= f =
        MkParser (\s =>
            case cs s of
                Left err => Left err
                Right (a, s') =>
                    parse (f a) s')

Alternative Parser where
    empty = MkParser (\s => Left NoAlternativesError)
    p <|> q =
        MkParser (\s =>
            case parse p s of
                Left err => parse q s
                Right res => Right res)

--Parser to consume a single character.
item : Parser Char
item =
        MkParser itemParser
    where
        itemParser : (List Char -> Either ParserError (Pair Char (List Char)))
        itemParser [] = Left UnexpectedEndOfInputError
        itemParser (c :: cs) =
            Right (c, cs)

--Parser to match a single character.
char : Char -> Parser Char
char ch =
        MkParser charParser
    where
        charParser : (List Char -> Either ParserError (Pair Char (List Char)))
        charParser [] = Left UnexpectedEndOfInputError
        charParser (c :: cs) =
            if c == ch
                then Right (c, cs)
                else Left (GeneralError
                    ("Expecting " ++ singleton ch ++ " and got "
                        ++ singleton c))

--Parse zero or more.
many : Parser a -> Parser (List a)
many v = MkParser (mv [])
    where
        mv : List a -> List Char
            -> Either ParserError (Pair (List a) (List Char))
        mv xs s =
            case parse v s of
                Left err => Right (reverse xs, s)
                Right (x, s') => mv (x :: xs) (assert_smaller s s')

--Parse one or more.
some : Parser a -> Parser (List a)
some v =
    pure (::) <*> v <*> many v

--Satisfy consumes and returns a character if it matches a given predicate.
satisfy : (Char -> Bool) -> Parser Char
satisfy p = do
    c <- item
    if p c
        then pure c
        else MkParser (\s => Left UnsatisfiedPredicateError)

--Match against one of the characters in the list.
oneOf : List Char -> Parser Char
oneOf s = satisfy $ flip elem s

--chainl1 matches one or more occurrences of a value interspersed with an op.
chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op =
        p >>= rest
    where
        rest : a -> Parser a
        rest x = do
            f <- op
            y <- p
            assert_total $ rest (f x y) <|> pure x

--chainl matches zero ormore occurrences of a value interspersed with an op.
chainl : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op x = (p `chainl1` op) <|> pure x

--parse a natural number
natural : Parser Nat
natural = (fromMaybe Z) <$> parsePositive <$> pack <$> some (satisfy isDigit)
