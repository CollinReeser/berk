open Typing
open Ast

module StrMap = Map.Make(String)

type typecheck_ctxt = {
  vars: (berk_t * var_qual) StrMap.t;
  ret_t: berk_t;
}

let default_tc_ctxt typ = {vars = StrMap.empty; ret_t = typ}

let get_resolve_type stmts =
  let resolve_expr_types =
    List.filter_map (
        fun stmt ->
          match stmt with
          | ResolveStmt(exp) -> Some(expr_type exp)
          | _ -> None
      ) stmts
  in
  match resolve_expr_types with
  | [] -> Nil
  | [x] -> x
  | x::xs -> List.fold_left (fun x y -> common_type_of_lr x y) x xs
;;

let populate_ctxt_with_params f_params base_vars =
  let add_param vars (id, qual, typ) = begin
    StrMap.add id (typ, qual) vars
  end in
  let added_vars = List.fold_left add_param base_vars f_params in
  added_vars


let rec type_check_func func_def =
  let {f_stmts; f_params; f_ret_t; _} = func_def in
  let tc_ctxt_base = default_tc_ctxt f_ret_t in
  let vars_base = tc_ctxt_base.vars in
  let vars_init = populate_ctxt_with_params f_params vars_base in
  let tc_ctxt_init = {tc_ctxt_base with vars = vars_init} in

  let (_, f_stmts_typechecked) = type_check_stmts tc_ctxt_init f_stmts in

  {func_def with f_stmts = f_stmts_typechecked}

and type_check_stmt (tc_ctxt) (stmt) : (typecheck_ctxt * stmt) =
  match stmt with
  | DeclStmt(id, qual, decl_t, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in
      let resolved_t = match decl_t with
      | Undecided -> exp_t
      | _ ->
        if type_convertible_to exp_t decl_t
        then decl_t
        else failwith "Explicitly declared type disagrees with expr"
      in
      let vars_up = StrMap.add id (resolved_t, qual) tc_ctxt.vars in
      let tc_ctxt_up = {tc_ctxt with vars = vars_up} in
      (tc_ctxt_up, DeclStmt(id, qual, resolved_t, exp_typechecked))
  | AssignStmt(id, exp) ->
      let (var_t, {mut}) = StrMap.find id tc_ctxt.vars in
      let _ = if mut then () else failwith "Cannot assign to immutable var" in
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in

      if type_convertible_to exp_t var_t
        then (tc_ctxt, AssignStmt(id, exp_typechecked))
        else failwith "Expr for assignment does not typecheck"

  | ExprStmt(exp) -> (tc_ctxt, ExprStmt(type_check_expr tc_ctxt exp))
  | ResolveStmt(exp) -> (tc_ctxt, ResolveStmt(type_check_expr tc_ctxt exp))
  | ReturnStmt(exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in
      if type_convertible_to exp_t tc_ctxt.ret_t
        then (tc_ctxt, ReturnStmt(exp_typechecked))
        else failwith "Expr for return does not typecheck with func ret_t"

and type_check_stmts tc_ctxt stmts =
  match stmts with
  | [] -> (tc_ctxt, [])
  | x::xs ->
      let (tc_ctxt_updated, stmt_tced) = type_check_stmt tc_ctxt x in
      let (tc_ctxt_final, stmts_tced) = type_check_stmts tc_ctxt_updated xs in
      (tc_ctxt_final, stmt_tced :: stmts_tced)

and type_check_expr (tc_ctxt : typecheck_ctxt) exp : expr =
  match exp with
  | ValU64(i) -> ValU64(i)
  | ValU32(i) -> ValU32(i)
  | ValU16(i) -> ValU16(i)
  | ValU8 (i) -> ValU8 (i)

  | ValI64(i) -> ValI64(i)
  | ValI32(i) -> ValI32(i)
  | ValI16(i) -> ValI16(i)
  | ValI8 (i) -> ValI8 (i)

  | ValF128(str) -> ValF128(str)
  | ValF64(f)    -> ValF64(f)
  | ValF32(f)    -> ValF32(f)

  | ValBool(b) -> ValBool(b)

  | ValVar(_, id) ->
      let (var_t, _) = StrMap.find id tc_ctxt.vars in
      ValVar(var_t, id)

  | ValCastTrunc(target_t, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in
      if type_truncatable_to exp_t target_t
        then ValCastTrunc(target_t, exp_typechecked)
        else failwith "Cannot truncate-cast incompatible types"

  | ValCastBitwise(target_t, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in
      if type_bitwise_to exp_t target_t
        then ValCastBitwise(target_t, exp_typechecked)
        else failwith "Cannot bitwise-cast incompatible types"

  | BinOp(_, op, lhs, rhs) ->
      begin match op with
      | Add | Sub | Mul | Div | Mod ->
          let lhs_typechecked = type_check_expr tc_ctxt lhs in
          let rhs_typechecked = type_check_expr tc_ctxt rhs in
          let lhs_t = expr_type lhs_typechecked in
          let rhs_t = expr_type rhs_typechecked in
          let common_t = common_type_of_lr lhs_t rhs_t in
          BinOp(common_t, op, lhs_typechecked, rhs_typechecked)

      | Eq | NotEq | Less | LessEq | Greater | GreaterEq ->
          let lhs_typechecked = type_check_expr tc_ctxt lhs in
          let rhs_typechecked = type_check_expr tc_ctxt rhs in
          BinOp(Bool, op, lhs_typechecked, rhs_typechecked)
      end

  | BlockExpr(_, stmts) ->
      let (_, stmts_typechecked) = type_check_stmts tc_ctxt stmts in
      let stmts_resolve_t = get_resolve_type stmts_typechecked in
      BlockExpr(stmts_resolve_t, stmts_typechecked)

  | IfThenElseExpr(_, if_cond, then_expr, else_expr) ->
      let if_cond_typechecked = type_check_expr tc_ctxt if_cond in
      let if_cond_t = expr_type if_cond_typechecked in

      let then_expr_typechecked = type_check_expr tc_ctxt then_expr in
      let then_expr_t = expr_type then_expr_typechecked in

      let else_expr_typechecked = type_check_expr tc_ctxt else_expr in
      let else_expr_t = expr_type else_expr_typechecked in

      let _ = match if_cond_t with
      | Bool -> ()
      | _ -> failwith "if-expr condition must resolve to Bool"
      in

      let then_else_agreement_t = common_type_of_lr then_expr_t else_expr_t in

      IfThenElseExpr(
        then_else_agreement_t,
        if_cond_typechecked,
        then_expr_typechecked,
        else_expr_typechecked
      )
;;
