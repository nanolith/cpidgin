module ParserCombinator

%access public export
%default total

--Errors that the Parser can return.
data ParserError =
      UnexpectedEndOfInputError
    | NotAllInputConsumedError
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
            case cs2 s of
                Left err => Left err
                Right (a, s') =>
                    case cs1 s' of
                        Left err => Left err
                        Right (f, s'') => Right (f a, s''))

--We can make the Parser a Monad.
Monad Parser where
    (MkParser cs) >>= f =
        MkParser (\s =>
            case cs s of
                Left err => Left err
                Right (a, s') =>
                    parse (f a) s')

--Parser to consume a single character.
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
