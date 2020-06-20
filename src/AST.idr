module AST

--Primitive Types
public export
data CType =
      Int8
    | UInt8
    | Int16
    | UInt16
    | Int32
    | UInt32
    | Int64
    | UInt64
    | UserDefined String
    | Pointer CType
    | Const CType

--Show implementation for CType
public export
Show CType where
    show Int8 = "int8"
    show UInt8 = "uint8"
    show Int16 = "int16"
    show UInt16 = "uint16"
    show Int32 = "int32"
    show UInt32 = "uint32"
    show Int64 = "int64"
    show UInt64 = "uint64"

--Expressions that are part of the AST
public export
data AST =
      NumericConst Integer (Maybe CType)
    | AddExpr AST AST
    | SubExpr AST AST
    | MulExpr AST AST
    | AndExpr AST AST
    | OrExpr AST AST
    | XorExpr AST AST
    | ReturnExpr AST

--show an AST node wrapped in parenthesis
showParen : Show a => a -> String
showParen x = "(" ++ (show x) ++ ")"

--Show implementation for AST
public export
Show AST where
    show (NumericConst i Nothing) = show i
    show (NumericConst i (Just ty)) = (showParen ty) ++ (showParen i)
    show (AddExpr lhs rhs) = (showParen lhs) ++ "+" ++ (showParen rhs)
    show (SubExpr lhs rhs) = (showParen lhs) ++ "-" ++ (showParen rhs)
    show (MulExpr lhs rhs) = (showParen lhs) ++ "*" ++ (showParen rhs)
    show (AndExpr lhs rhs) = (showParen lhs) ++ "&" ++ (showParen rhs)
    show (OrExpr lhs rhs)  = (showParen lhs) ++ "|" ++ (showParen rhs)
    show (XorExpr lhs rhs) = (showParen lhs) ++ "^" ++ (showParen rhs)
    show (ReturnExpr x) = "return " ++ (showParen x)
