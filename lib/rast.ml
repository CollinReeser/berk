open Ast
open Typing
open Ir
open Utility

(*
Reduced-complexity AST.

Various elements of the full AST, generated by parse and used for typechecking,
can be rewritten in a more explicit but simpler form. This allows for easier
further analysis once the input is deemed well-formed, and easier generation
of MIR.

This reduced form of the AST deliberately loses certain information, like:

  - Limited scoping of variables.
  - Modifiers on variables, like mutability.

as it is assumed that the input AST was already verified as being well-formed.
*)

type rexpr =
  | RValNil
  | RValF128 of string
  | RValF64 of float
  | RValF32 of float
  | RValBool of bool
  | RValStr of string
  | RValInt of berk_t * int

  | RValVar of berk_t * string
  | RValFunc of berk_t * string

  | RValRawArray of berk_t

  | RValCast of berk_t * cast_op * rexpr
  | RUnOp of berk_t * un_op * rexpr
  | RBinOp of berk_t * bin_op * rexpr * rexpr

  | RBlockExpr of berk_t * rstmt * rexpr

  | RExprInvoke of berk_t * rexpr * rexpr list

  | RArrayExpr of berk_t * rexpr list
  | RIndexExpr of berk_t * rexpr * rexpr

  | RTupleIndexExpr of berk_t * int * rexpr
  | RTupleExpr of berk_t * rexpr list

  | RVariantCtorExpr of berk_t * string * rexpr list

  | RMatchExpr of berk_t * rexpr * (rpattern * rexpr) list

  | RWhileExpr of berk_t * rstmt list * rexpr * rstmt list

and rpattern =
  | RWild of berk_t
  | RVarBind of berk_t * string
  | RPNil
  | RPBool of bool
  | RPTuple of berk_t * rpattern list
  | RCtor of berk_t * string * rpattern list
  | RPatternAs of berk_t * rpattern * string

and rassign_idx_lval =
  (* An index into a tuple. *)
  | RALStaticIndex of int
  (* An index into a static or dynamic array. *)
  | RALIndex of rexpr

and rstmt =
  | RDeclStmt of string * berk_t * rexpr

  | RDeclDefStmt of (string * berk_t) list

  | RAssignStmt of string * rassign_idx_lval list * rexpr

  | RExprStmt of rexpr
  | RReturnStmt of rexpr

  (* A convenience container for when a stmt needs to be rewritten using
  multiple rstmt. *)
  | RStmts of rstmt list
;;

let rexpr_type exp =
  begin match exp with
  | RValNil -> Nil
  | RValF128(_) -> F128
  | RValF64(_)  -> F64
  | RValF32(_)  -> F32
  | RValBool(_) -> Bool
  | RValStr(_) -> String
  | RValInt(typ, _) -> typ
  | RValVar(typ, _) -> typ
  | RValFunc(typ, _) -> typ
  | RValRawArray(typ) -> typ
  | RValCast(typ, _, _) -> typ
  | RUnOp(typ, _, _) -> typ
  | RBinOp(typ, _, _, _) -> typ
  | RBlockExpr(typ, _, _) -> typ
  | RWhileExpr(typ, _, _, _) -> typ
  | RExprInvoke(typ, _, _) -> typ
  | RArrayExpr(typ, _) -> typ
  | RIndexExpr(typ, _, _) -> typ
  | RTupleIndexExpr(typ, _, _) -> typ
  | RTupleExpr(typ, _) -> typ
  | RVariantCtorExpr(typ, _, _) -> typ
  | RMatchExpr(typ, _, _) -> typ
  end
;;

let rec expr_to_rexpr expr : rexpr =
  begin match expr with
  | ValName(_, name) ->
      failwith (
        Printf.sprintf
          "Error: Cannot convert ValName(%s) to rexpr: must be pre-resolved"
          name
      )

  | ValNil -> RValNil
  | ValF128(s) -> RValF128(s)
  | ValF64(f) -> RValF64(f)
  | ValF32(f) -> RValF32(f)
  | ValBool(b) -> RValBool(b)
  | ValStr(s) -> RValStr(s)
  | ValInt(t, i) -> RValInt(t, i)

  | ValVar(t, name) -> RValVar(t, name)
  | ValFunc(t, name) -> RValFunc(t, name)

  | ValRawArray(t) -> RValRawArray(t)

  | ValCast(t, op, e) ->
      let re = expr_to_rexpr e in
      RValCast(t, op, re)

  | UnOp(t, op, e) ->
      let re = expr_to_rexpr e in
      RUnOp(t, op, re)

  | BinOp(t, op, e_lhs, e_rhs) ->
      let re_lhs = expr_to_rexpr e_lhs in
      let re_rhs = expr_to_rexpr e_rhs in
      RBinOp(t, op, re_lhs, re_rhs)

  | BlockExpr(t, stmts, e) ->
      let re = expr_to_rexpr e in
      let rstmts = List.map stmt_to_rstmt stmts in
      let wrapped_rstmts = RStmts(rstmts) in
      RBlockExpr(t, wrapped_rstmts, re)

  | ExprInvoke(t, e_func, e_args) ->
      let re_func = expr_to_rexpr e_func in
      let re_args = List.map expr_to_rexpr e_args in
      RExprInvoke(t, re_func, re_args)

  | FuncCall(t, name, e_args) ->
      let args_ts = List.map expr_type e_args in
      let func_t = Function(t, args_ts) in
      let re_func = RValFunc(func_t, name) in

      let re_args = List.map expr_to_rexpr e_args in

      RExprInvoke(t, re_func, re_args)

  | UfcsCall(t, e_arg_first, name, e_args_rest) ->
      let e_args_all = e_arg_first :: e_args_rest in

      let args_ts = List.map expr_type e_args_all in
      let func_t = Function(t, args_ts) in
      let re_func = RValFunc(func_t, name) in

      let re_args = List.map expr_to_rexpr e_args_all in

      RExprInvoke(t, re_func, re_args)

  | ArrayExpr(t, e_elems) ->
      let re_elems = List.map expr_to_rexpr e_elems in
      RArrayExpr(t, re_elems)

  | IndexExpr(t, e_idx, e_arr) ->
      let re_idx = expr_to_rexpr e_idx in
      let re_arr = expr_to_rexpr e_arr in
      RIndexExpr(t, re_idx, re_arr)

  | TupleIndexExpr(t, i, e_tuple) ->
      let re_tuple = expr_to_rexpr e_tuple in
      RTupleIndexExpr(t, i, re_tuple)

  | TupleExpr(t, e_elems) ->
      let re_elems = List.map expr_to_rexpr e_elems in
      RTupleExpr(t, re_elems)

  (* TODO: Could we turn this into an explicit struct of certain elements to
  make reasoning about RAST -> MIR generation and MIR -> LLVM generation easier?
  *)
  | VariantCtorExpr(t, name_ctor, e_fields) ->
      let re_fields = List.map expr_to_rexpr e_fields in
      RVariantCtorExpr(t, name_ctor, re_fields)

  | IfThenElseExpr(t, e_cond, e_then, e_else) ->
      let re_cond = expr_to_rexpr e_cond in
      let re_then = expr_to_rexpr e_then in
      let re_else = expr_to_rexpr e_else in
      RMatchExpr(t, re_cond, [(RPBool(true), re_then); (RWild(Bool), re_else)])

  | WhileExpr(t, stmts_init, e_cond, stmts_block) ->
      let rstmts_init = List.map stmt_to_rstmt stmts_init in
      let rstmts_block = List.map stmt_to_rstmt stmts_block in
      let re_cond = expr_to_rexpr e_cond in
      RWhileExpr(t, rstmts_init, re_cond, rstmts_block)

  | MatchExpr(t, e_cond, patts_to_exprs) ->
      let re_cond = expr_to_rexpr e_cond in
      let rpatts_to_rexprs =
        List.map (
          fun (patt, expr) ->
            let rpatt = pattern_to_rpattern patt in
            let rexpr = expr_to_rexpr expr in
            (rpatt, rexpr)
        ) patts_to_exprs
      in
      RMatchExpr(t, re_cond, rpatts_to_rexprs)
  end

and pattern_to_rpattern patt : rpattern =
  begin match patt with
  | PNil -> RPNil

  | Wild(t) -> RWild(t)

  | VarBind(t, name) -> RVarBind(t, name)

  | PBool(b) -> RPBool(b)

  | PTuple(t, patts) ->
      let rpatts = List.map pattern_to_rpattern patts in
      RPTuple(t, rpatts)

  | Ctor(t, name_ctor, patts) ->
      let rpatts = List.map pattern_to_rpattern patts in
      RCtor(t, name_ctor, rpatts)

  | PatternAs(t, patt, name) ->
      let rpatt = pattern_to_rpattern patt in
      RPatternAs(t, rpatt, name)
  end

and assign_idx_lval_to_rassign_idx_lval idx : rassign_idx_lval =
  begin match idx with
  | ALStaticIndex(i) ->
      RALStaticIndex(i)

  | ALIndex(e) ->
      let re = expr_to_rexpr e in
      RALIndex(re)
  end

and stmt_to_rstmt stmt : rstmt =
  begin match stmt with
  | ExprStmt(_, e) ->
      let re = expr_to_rexpr e in
      RExprStmt(re)

  | ReturnStmt(e) ->
      let re = expr_to_rexpr e in
      RReturnStmt(re)

  | DeclStmt(name, _, t, e) ->
      let re = expr_to_rexpr e in
      RDeclStmt(name, t, re)

  | DeclDefStmt(names_quals_ts) ->
      let names_ts = List.map (fun (name, _, t) -> (name, t)) names_quals_ts in
      RDeclDefStmt(names_ts)

  | AssignStmt(name, idxs, e) ->
      let ridxs = List.map assign_idx_lval_to_rassign_idx_lval idxs in
      let re = expr_to_rexpr e in
      RAssignStmt(name, ridxs, re)

  (* Deconstructing `let` stmts can be described as first assigning the
  result of the expr-to-be-deconstructed to a placeholder named variable, and
  then performing a series of indexes onto that variable into the target
  "real" deconstructed variable names. *)
  | DeclDeconStmt(names_quals, t, e) ->
      let names = List.map (fun (name, _) -> name) names_quals in
      let re = expr_to_rexpr e in

      let placeholder_name = Printf.sprintf "__%s" (fmt_join_strs "_" names) in

      let init_rstmt = RDeclStmt(placeholder_name, t, re) in
      let decon_rstmts =
        begin match t with
        | Tuple(ts) ->
            map2i (
              fun i name t_elem ->
                RDeclStmt(
                  name, t_elem,
                  RTupleIndexExpr(t_elem, i, RValVar(t, placeholder_name))
                )
            ) names ts

        | _ ->
            failwith "Cannot rewrite deconstruction of non-tuple decl."
        end
      in
      RStmts(init_rstmt :: decon_rstmts)
  end
