open Typing
open Ast


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


let rec type_check_stmt stmt =
  match stmt with
  | DeclDef(id, decl_t, exp) ->
      let exp_typechecked = type_check_expr exp in
      let exp_t = expr_type exp_typechecked in
      let resolved_t = match decl_t with
      | Undecided -> exp_t
      | _ ->
        if type_convertible_to exp_t decl_t
        then decl_t
        else failwith "Explicitly declared type disagrees with expr"
      in
      DeclDef(id, resolved_t, exp_typechecked)
  | ExprStmt(exp) -> ExprStmt(type_check_expr exp)
  | ResolveStmt(exp) -> ResolveStmt(type_check_expr exp)

and type_check_stmts stmts =
  List.map (fun stmt -> type_check_stmt stmt) stmts

and type_check_expr exp =
  match exp with
  | ValI64(i)  -> ValI64(i)
  | ValI32(i)  -> ValI32(i)
  | ValF32(i)  -> ValF32(i)
  | ValBool(b) -> ValBool(b)
  | BinOp(_, op, lhs, rhs) ->
      let lhs_typechecked = type_check_expr lhs in
      let rhs_typechecked = type_check_expr rhs in
      let lhs_t = expr_type lhs_typechecked in
      let rhs_t = expr_type rhs_typechecked in
      let common_t = common_type_of_lr lhs_t rhs_t in
      BinOp(common_t, op, lhs_typechecked, rhs_typechecked)
  | BlockExpr(_, stmts) ->
      let stmts_typechecked = type_check_stmts stmts in
      let stmts_resolve_t = get_resolve_type stmts_typechecked in
      BlockExpr(stmts_resolve_t, stmts_typechecked)
  | IfThenElseExpr(_, if_cond, then_expr, else_expr) ->
      let if_cond_typechecked = type_check_expr if_cond in
      let if_cond_t = expr_type if_cond_typechecked in

      let then_expr_typechecked = type_check_expr then_expr in
      let then_expr_t = expr_type then_expr_typechecked in

      let else_expr_typechecked = type_check_expr else_expr in
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
