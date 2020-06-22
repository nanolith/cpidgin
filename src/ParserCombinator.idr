module ParserCombinator

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

--We can make the Parser a Functor.
Functor Parser where
    map f (MkParser cs) = MkParser (\s => [(f a, b) | (a, b) <- cs s])

--We can make the Parser an Applicative.
Applicative Parser where
    pure a = MkParser (\s => [(a, s)])
    (MkParser cs1) <*> (MkParser cs2) =
        MkParser (\s =>
            [(f a, s2) | (f, s1) <- cs1 s, (a, s2) <- cs2 s1])

--We can make the Parser a Monad.
Monad Parser where
    p >>= f =
        MkParser $ (\s => concatMap (\(a, s') => parse (f a) s') $ parse p s)

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
