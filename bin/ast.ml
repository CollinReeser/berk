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
  | ValNil
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
  | ValStr of string
  | ValVar of berk_t * ident_t
  | ValCastTrunc of berk_t * expr
  | ValCastBitwise of berk_t * expr
  | BinOp of berk_t * bin_op * expr * expr
  (* Sequence of statements followed by an expression, where if the expression
  is None, then the BlockExpr resolves to a nil value. *)
  | BlockExpr of berk_t * stmt list * expr
  (* if expr, then expr, else expr *)
  | IfThenElseExpr of berk_t * expr * expr * expr
  (* while expr, then stmts, else expr *)
  | WhileExpr of berk_t * expr * stmt list * expr
  | FuncCall of berk_t * ident_t * expr list
  | ArrayExpr of (berk_t * expr list)
  (* First expr is index, second is array *)
  | IndexExpr of (berk_t * expr * expr)
  (* int is index, expr is array *)
  | StaticIndexExpr of (berk_t * int * expr)
  | TupleExpr of berk_t * expr list
  (* Top-level variant type, ctor name, ctor expr,  *)
  | VariantCtorExpr of berk_t * string * expr

and stmt =
  | DeclStmt of ident_t * var_qual * berk_t * expr
  | DeclDeconStmt of (ident_t * var_qual) list * berk_t * expr
  | AssignStmt of ident_t * expr
  | AssignDeconStmt of ident_t list * expr
  | ExprStmt of expr
  | ReturnStmt of expr
;;

let expr_type exp =
  match exp with
  | ValNil -> Nil
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
  | ValStr(_) -> String
  | ValVar(typ, _) -> typ
  | ValCastTrunc(typ, _) -> typ
  | ValCastBitwise(typ, _) -> typ
  | BinOp(typ, _, _, _) -> typ
  | BlockExpr(typ, _, _) -> typ
  | IfThenElseExpr(typ, _, _, _) -> typ
  | WhileExpr(typ, _, _, _) -> typ
  | FuncCall(typ, _, _) -> typ
  | ArrayExpr(typ, _) -> typ
  | IndexExpr(typ, _, _) -> typ
  | StaticIndexExpr(typ, _, _) -> typ
  | TupleExpr(typ, _) -> typ
  | VariantCtorExpr(typ, _, _) -> typ
;;

let inject_type_into_expr typ exp =
  match exp with
  | ValNil
  | ValU64 (_)
  | ValU32 (_)
  | ValU16 (_)
  | ValU8  (_)
  | ValI64 (_)
  | ValI32 (_)
  | ValI16 (_)
  | ValI8  (_)
  | ValF128(_)
  | ValF64 (_)
  | ValF32 (_)
  | ValBool(_)
  | ValStr (_) -> exp

  | ValVar         (_, a)       -> ValVar         (typ, a)
  | ArrayExpr      (_, a)       -> ArrayExpr      (typ, a)
  | TupleExpr      (_, a)       -> TupleExpr      (typ, a)
  | ValCastTrunc   (_, a)       -> ValCastTrunc   (typ, a)
  | ValCastBitwise (_, a)       -> ValCastBitwise (typ, a)
  | FuncCall       (_, a, b)    -> FuncCall       (typ, a, b)
  | BlockExpr      (_, a, b)    -> BlockExpr      (typ, a, b)
  | IndexExpr      (_, a, b)    -> IndexExpr      (typ, a, b)
  | StaticIndexExpr(_, a, b)    -> StaticIndexExpr(typ, a, b)
  | VariantCtorExpr(_, a, b)    -> VariantCtorExpr(typ, a, b)
  | BinOp          (_, a, b, c) -> BinOp          (typ, a, b, c)
  | WhileExpr      (_, a, b, c) -> WhileExpr      (typ, a, b, c)
  | IfThenElseExpr (_, a, b, c) -> IfThenElseExpr (typ, a, b, c)
;;

type v_ctor = (string * berk_t)

and variant_decl_t = {
  v_name: string;
  v_ctors: v_ctor list;
  v_typ_vars: string list;
}

type f_param = (ident_t * var_qual * berk_t)

and func_decl_t = {
  f_name: string;
  f_params: f_param list;
  f_ret_t: berk_t;
}

and func_def_t = {
  f_decl: func_decl_t;
  f_stmts: stmt list;
}

type module_decl =
  | FuncExternDecl of func_decl_t
  | FuncDef of func_def_t
  | VariantDecl of variant_decl_t

(* Return the pair of all the non-variadic function parameter types, and whether
the parameter list ends with a variadic-args sentinel. Fails if ill-formed. *)
let rec get_static_f_params (f_params : f_param list) =
  begin match f_params with
  | [] -> ([], false)
  | [(_, _, VarArgSentinel)] -> ([], true)
  | (_, _, VarArgSentinel)::_ ->
      failwith "Variadic arguments may exist only once, at end of param list"
  | (_, _, x)::xs ->
      let (rest, is_vararg) = get_static_f_params xs in
      (x::rest, is_vararg)
  end
