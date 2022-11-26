open Typing


(*
AST for the berk language.
*)

type ident_t = string

type cond_block = {
  cond: expr;
  stmts: stmt list;
}

and expr =
  | ValI64 of int
  | ValI32 of int
  | ValBool of bool
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | IfExpr of {
      if_block: cond_block;
      else_if_blocks: cond_block list;
      else_block: (stmt list) option;
    }

and stmt =
  | DeclDef of ident_t * berk_type * expr
  | ExprStmt of expr
  | IfStmt of {
      if_block: cond_block;
      else_if_blocks: cond_block list;
      else_block: (stmt list) option;
    }
  | ResolveStmt of expr
;;

type func_param = {
  p_name: string;
  p_type: berk_type;
}

type func_ast = {
  f_name: string;
  f_params: func_param list;
  f_stmts: stmt list;
}
