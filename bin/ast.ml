open Typing


(*
AST for the berk language.
*)

type ident_t = string

and bin_op =
  | Add
  | Sub
  | Mul

and expr =
  | ValI64 of int
  | ValI32 of int
  | ValF32 of float
  | ValBool of bool
  | ValVar of berk_t * ident_t
  | BinOp of berk_t * bin_op * expr * expr
  | BlockExpr of berk_t * stmt list
  | IfThenElseExpr of berk_t * expr * expr * expr

and stmt =
  | DeclStmt of ident_t * berk_t * expr
  | ExprStmt of expr
  | ResolveStmt of expr
  | ReturnStmt of expr
;;

let expr_type = function
  | ValI64(_) -> I64
  | ValI32(_) -> I32
  | ValF32(_) -> F32
  | ValBool(_) -> Bool
  | ValVar(typ, _) -> typ
  | BinOp(typ, _, _, _) -> typ
  | BlockExpr(typ, _) -> typ
  | IfThenElseExpr(typ, _, _, _) -> typ
;;


type func_param = {
  p_name: string;
  p_type: berk_t;
}

type func_ast = {
  f_name: string;
  f_params: func_param list;
  f_stmts: stmt list;
}
