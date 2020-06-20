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

--Show implementation for AST
public export
Show AST where
    show (NumericConst i Nothing) = show i
    show (NumericConst i (Just ty)) = "(" ++ show ty ++ ")"
    show (AddExpr lhs rhs) = (show lhs) ++ "+" ++ (show rhs)
    show (SubExpr lhs rhs) = (show lhs) ++ "-" ++ (show rhs)
    show (AndExpr lhs rhs) = (show lhs) ++ "&" ++ (show rhs)
    show (OrExpr lhs rhs) = (show lhs) ++ "|" ++ (show rhs)
    show (XorExpr lhs rhs) = (show lhs) ++ "^" ++ (show rhs)
    show (ReturnExpr x) = "return " ++ (show x)
