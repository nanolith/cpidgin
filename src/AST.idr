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

--Expressions that are part of the AST
public export
data AST =
      ReturnExpr AST
