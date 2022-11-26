open Typing
open Ast


let rec type_check_if_expr_stmts stmts =
  let resolve_stmt_types =
    List.filter_map (
      fun st ->
        match st with
        | ResolveStmt ex -> Some(type_check_expr ex)
        | _ -> None
    ) stmts
  in
  match resolve_stmt_types with
  | [] -> None
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs

and type_check_expr exp =
  match exp with
  | ValI64(_) -> Some(I64)
  | ValI32(_) -> Some(I32)
  | ValBool(_) -> Some(Bool)
  | Add(lhs, rhs) ->
      let lhs_type = type_check_expr lhs in
      let rhs_type = type_check_expr rhs in
      common_type_of_lr lhs_type rhs_type
  | Sub(lhs, rhs) ->
      let lhs_type = type_check_expr lhs in
      let rhs_type = type_check_expr rhs in
      common_type_of_lr lhs_type rhs_type
  | Mul(lhs, rhs) ->
      let lhs_type = type_check_expr lhs in
      let rhs_type = type_check_expr rhs in
      common_type_of_lr lhs_type rhs_type
  | IfExpr({
      if_block = {cond = if_cond; stmts = if_stmts};
      else_if_blocks;
      else_block;
    }) ->
      let if_cond_type = type_check_expr if_cond in
      let if_stmts_type = type_check_if_expr_stmts if_stmts in
      let else_if_cond_type = (
        List.fold_left (
          fun lhs rhs ->
            match (lhs, rhs) with
            | (Some(Bool), Some(Bool)) -> Some(Bool)
            | _ -> None
        )
        (Some(Bool))
        (
          List.map (
            fun {cond; stmts = _} ->
              type_check_expr cond
          ) else_if_blocks
        )
      ) in
      let else_if_stmts_type =
        let else_if_stmts_types =
          List.map
            type_check_if_expr_stmts (
              List.map
                (fun {cond = _; stmts} -> stmts)
                else_if_blocks
            )
        in
        match else_if_stmts_types with
        | [] -> None
        | [x] -> x
        | x::xs -> List.fold_left common_type_of_lr x xs
      in
      let else_stmts_type =
        match else_block with
        | None -> None
        | Some(stmts) -> type_check_if_expr_stmts stmts
      in
      match (if_cond_type, else_if_cond_type) with
      | (Some(Bool), Some(Bool)) ->
          common_type_of_lst [
            if_stmts_type; else_if_stmts_type; else_stmts_type
          ]
      | _ -> None
;;
