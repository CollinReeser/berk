open Typing


(*
AST for the berk language.
*)

type ident_t = string

and bin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | NotEq
  | Less
  | LessEq
  | Greater
  | GreaterEq

and maybe_bounds_check =
  | NoBoundsCheck
  | DoBoundsCheck
  | Undecided

and expr =
  | ValU64 of int
  | ValU32 of int
  | ValU16 of int
  | ValU8  of int
  | ValI64 of int
  | ValI32 of int
  | ValI16 of int
  | ValI8  of int
  | ValF128 of string
  | ValF64 of float
  | ValF32 of float
  | ValBool of bool
  | ValVar of berk_t * ident_t
  | ValCastTrunc of berk_t * expr
  | ValCastBitwise of berk_t * expr
  | BinOp of berk_t * bin_op * expr * expr
  | BlockExpr of berk_t * stmt list
  | IfThenElseExpr of berk_t * expr * expr * expr
  | FuncCall of berk_t * ident_t * expr list
  | ArrayExpr of (berk_t * expr list)
  (* Bool decides adding bounds-check, first expr is index, second is array *)
  | IndexExpr of (berk_t * maybe_bounds_check * expr * expr)
  | TupleExpr of berk_t * expr list

and stmt =
  | DeclStmt of ident_t * var_qual * berk_t * expr
  | DeclDeconStmt of (ident_t * var_qual) list * berk_t * expr
  | AssignStmt of ident_t * expr
  | AssignDeconStmt of ident_t list * expr
  | ExprStmt of expr
  | BlockStmt of stmt list
  | IfThenElseStmt of expr * stmt * stmt
  | ResolveStmt of expr
  | ReturnStmt of expr
;;

let expr_type typ =
  match typ with
  | ValU64(_) -> U64
  | ValU32(_) -> U32
  | ValU16(_) -> U16
  | ValU8(_)  -> U8
  | ValI64(_) -> I64
  | ValI32(_) -> I32
  | ValI16(_) -> I16
  | ValI8(_)  -> I8
  | ValF128(_) -> F128
  | ValF64(_)  -> F64
  | ValF32(_)  -> F32
  | ValBool(_) -> Bool
  | ValVar(typ, _) -> typ
  | ValCastTrunc(typ, _) -> typ
  | ValCastBitwise(typ, _) -> typ
  | BinOp(typ, _, _, _) -> typ
  | BlockExpr(typ, _) -> typ
  | IfThenElseExpr(typ, _, _, _) -> typ
  | FuncCall(typ, _, _) -> typ
  | ArrayExpr(typ, _) -> typ
  | IndexExpr(typ, _, _, _) -> typ
  | TupleExpr(typ, _) -> typ
;;

type module_decl =
  | FuncDecl of func_ast

and func_ast = {
  f_name: string;
  f_params: (ident_t * var_qual * berk_t) list;
  f_stmts: stmt list;
  f_ret_t: berk_t;
}
