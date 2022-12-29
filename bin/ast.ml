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
  | ArrayExpr of berk_t * expr list
  (* First expr is index, second is array *)
  | IndexExpr of berk_t * expr * expr
  (* int is index, expr is array *)
  | StaticIndexExpr of berk_t * int * expr
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

(* Force-apply a top-level type to the given expression, recursively. Fails
if any component subtype disagrees with what the expression had already
determined was its type. *)
let rec inject_type_into_expr typ exp =
  let exp_t = expr_type exp in
  if not (type_convertible_to exp_t typ) then
    failwith (
      "Injection type [[" ^ (fmt_type typ) ^ "]] disagrees with existing " ^
      "type [[" ^ (fmt_type exp_t) ^ "]]"
    )
  else
    match (exp, typ) with
    | (
        (
          ValNil
          | ValU64 (_) | ValU32 (_) | ValU16 (_) | ValU8  (_)
          | ValI64 (_) | ValI32 (_) | ValI16 (_) | ValI8  (_)
          | ValF128(_) | ValF64 (_) | ValF32 (_)
          | ValBool(_)
          | ValStr (_)
        ),
        _
      ) -> exp

    | (ValVar(_, var_name),            _) -> ValVar        (typ, var_name)

    | (ValCastTrunc  (_, exp_trunc),   _) -> ValCastTrunc  (typ, exp_trunc)
    | (ValCastBitwise(_, exp_bitwise), _) -> ValCastBitwise(typ, exp_bitwise)

    (* The return type of a function does not influence its parameters. *)
    | (FuncCall(_, f_name, exp_lst), _) -> FuncCall(typ, f_name, exp_lst)

    | (BlockExpr(_, stmts, exp_res), _) ->
        (* We're not smart enough yet to influence the types of any expressions
        within the statements within the block. So, just make sure the trailing
        expression is type-injected. *)
        let exp_res_injected = inject_type_into_expr typ exp_res in
        BlockExpr(typ, stmts, exp_res_injected)

    | (IndexExpr(_, idx_exp, arr_exp), _) ->
        (* We can't use our injection type info to assist with typechecking the
        index expression, but we _can_ use it to assist in typechecking the
        indexed array itself, by assuming the array expression type is expected
        to be an "array of" the target type. *)
        let arr_t = expr_type arr_exp in
        let arr_injection_type = begin match arr_t with
          | Array(_, sz) -> Array(typ, sz)
          | _ -> failwith ("Unexpected non-array type: " ^ (fmt_type arr_t))
        end in
        let arr_exp_injected =
          inject_type_into_expr arr_injection_type arr_exp
        in
        IndexExpr(typ, idx_exp, arr_exp_injected)

    | (StaticIndexExpr(_, idx, arr_exp), _) ->
        (* We can't use our injection type info to assist with typechecking the
        index expression, but we _can_ use it to assist in typechecking the
        indexed array itself, by assuming the array expression type is expected
        to be an "array of" the target type. *)
        let arr_t = expr_type arr_exp in
        let arr_injection_type = begin match arr_t with
          | Array(_, sz) -> Array(typ, sz)
          | _ -> failwith ("Unexpected non-array type: " ^ (fmt_type arr_t))
        end in
        let arr_exp_injected =
          inject_type_into_expr arr_injection_type arr_exp
        in
        StaticIndexExpr(typ, idx, arr_exp_injected)

    | (ArrayExpr(_, elem_lst), Array(elem_t, sz)) ->
        let elem_t_lst = List.init sz (fun _ -> elem_t) in
        let elem_exp_injected_lst =
          List.map2 inject_type_into_expr elem_t_lst elem_lst
        in
        ArrayExpr(typ, elem_exp_injected_lst)

    | (ArrayExpr(_, _), _) ->
        failwith (
          "Cannot inject non-array type into array expr: " ^ (fmt_type typ)
        )

    | (TupleExpr(_, exp_lst), Tuple(exp_t_lst)) ->
        let exp_injected_lst =
          List.map2 inject_type_into_expr exp_t_lst exp_lst
        in
        TupleExpr(typ, exp_injected_lst)

    | (TupleExpr(_, _), _) ->
        failwith (
          "Cannot inject non-tuple type into tuple expr: " ^ (fmt_type typ)
        )

    | (BinOp(_, bin_op, lhs, rhs), _) ->
        let lhs_injected = inject_type_into_expr typ lhs in
        let rhs_injected = inject_type_into_expr typ rhs in
        BinOp(typ, bin_op, lhs_injected, rhs_injected)

    | (IfThenElseExpr(_, cond_exp, then_exp, else_exp), _) ->
        let then_exp_injected = inject_type_into_expr typ then_exp in
        let else_exp_injected = inject_type_into_expr typ else_exp in
        IfThenElseExpr (typ, cond_exp, then_exp_injected, else_exp_injected)

    | (WhileExpr(_, cond_expr, stmts, exp_res), _) ->
        let exp_res_injected = inject_type_into_expr typ exp_res in
        WhileExpr(typ, cond_expr, stmts, exp_res_injected)

    | (VariantCtorExpr(_, ctor_name, ctor_exp), Variant(_, ctors)) ->
        let (_, ctor_exp_t) = List.find (
            fun (name, _) -> name = ctor_name
          ) ctors
        in
        let ctor_exp_injected = inject_type_into_expr ctor_exp_t ctor_exp in
        VariantCtorExpr(typ, ctor_name, ctor_exp_injected)

    | (VariantCtorExpr(_, _, _), _) ->
        failwith (
          "Unexpectedly encountered non-variant type for variant " ^
          "constructor expr: [[ " ^ (fmt_type typ) ^ " ]]"
        )
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
