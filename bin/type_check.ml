open Typing
open Ast

module StrMap = Map.Make(String)

type module_context = {
  func_sigs: (berk_t * (ident_t * var_qual * berk_t) list) StrMap.t;
}

let default_mod_ctxt = {func_sigs = StrMap.empty}

type typecheck_context = {
  vars: (berk_t * var_qual) StrMap.t;
  ret_t: berk_t;
  mod_ctxt: module_context;
}

let default_tc_ctxt typ = {
  vars = StrMap.empty;
  ret_t = typ;
  mod_ctxt = default_mod_ctxt;
}

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

let rec type_check_mod_decls mod_decls =
  let mod_ctxt = default_mod_ctxt in

  let rec _type_check_mod_decls ctxt decls =
    match decls with
    | [] -> (ctxt, [])
    | x::xs ->
      let (mod_ctxt_up, decl_tced) = type_check_mod_decl ctxt x in
      let (mod_ctxt_fin, decls_tced) = _type_check_mod_decls mod_ctxt_up xs in
      (mod_ctxt_fin, decl_tced :: decls_tced)
  in
  let (_, mod_decls_typechecked) = _type_check_mod_decls mod_ctxt mod_decls in

  mod_decls_typechecked

and type_check_mod_decl mod_ctxt mod_decl =
  match mod_decl with
  | FuncExternDecl(f_decl_ast) ->
      let {f_name; f_params; f_ret_t;} = f_decl_ast in
      let func_sigs_up = begin
        StrMap.add f_name (f_ret_t, f_params) mod_ctxt.func_sigs
      end in
      let mod_ctxt_up = {func_sigs = func_sigs_up} in

      (mod_ctxt_up, FuncExternDecl(f_decl_ast))

  | FuncDef(f_ast) ->
      let {f_decl = {f_name; f_params; f_ret_t;}; _} = f_ast in
      let func_sigs_up = begin
        StrMap.add f_name (f_ret_t, f_params) mod_ctxt.func_sigs
      end in
      let mod_ctxt_up = {func_sigs = func_sigs_up} in
      let func_ast_typechecked = type_check_func mod_ctxt_up f_ast in

      (mod_ctxt_up, FuncDef(func_ast_typechecked))

and type_check_func mod_ctxt func_def =
  let {f_decl = {f_params; f_ret_t; _;}; f_stmts;} = func_def in
  let tc_ctxt_base = default_tc_ctxt f_ret_t in
  let vars_base = tc_ctxt_base.vars in
  let vars_init = populate_ctxt_with_params f_params vars_base in
  let tc_ctxt_init = {
    tc_ctxt_base with
      vars = vars_init;
      mod_ctxt = mod_ctxt
  } in

  let (_, f_stmts_typechecked) = type_check_stmts tc_ctxt_init f_stmts in

  {func_def with f_stmts = f_stmts_typechecked}

and update_vars_with_idents_quals vars_init idents_quals types =
  let idents_quals_types = List.combine idents_quals types in
  List.fold_left (
    fun vars ((id, qual), typ) ->
      StrMap.add id (typ, qual) vars
  ) vars_init idents_quals_types

and type_check_stmt (tc_ctxt) (stmt) : (typecheck_context * stmt) =
  match stmt with
  | DeclStmt(ident, qual, decl_t, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in
      let resolved_t = match decl_t with
      | Undecided -> exp_t
      | _ ->
        if type_convertible_to exp_t decl_t
        then decl_t
        else failwith "Explicitly declared type disagrees with expr"
      in

      let vars_up = StrMap.add ident (resolved_t, qual) tc_ctxt.vars in
      let tc_ctxt_up = {tc_ctxt with vars = vars_up} in

      (tc_ctxt_up, DeclStmt(ident, qual, resolved_t, exp_typechecked))

  | DeclDeconStmt(idents_quals, decl_t, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in
      let resolved_t = match decl_t with
      | Undecided -> exp_t
      | _ ->
        if type_convertible_to exp_t decl_t
        then decl_t
        else failwith "Explicitly declared type disagrees with expr"
      in

      let vars_up = begin match resolved_t with
        | Array(typ, sz) ->
            if sz == List.length idents_quals
            then
              begin
                let types = List.init sz (fun _ -> typ) in
                update_vars_with_idents_quals tc_ctxt.vars idents_quals types
              end
            else failwith "Mismatch in number of idents vs array expr in decl"
        | Tuple(types) ->
            if List.length types == List.length idents_quals
            then
              begin
                update_vars_with_idents_quals tc_ctxt.vars idents_quals types
              end
            else failwith "Mismatch in number of idents vs tuple expr in decl"
        | _ -> failwith "Cannot deconstruct non-aggregate type in decl"
        end
      in
      let tc_ctxt_up = {tc_ctxt with vars = vars_up} in

      (tc_ctxt_up, DeclDeconStmt(idents_quals, resolved_t, exp_typechecked))

  | AssignStmt(ident, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in

      let (var_t, {mut}) = StrMap.find ident tc_ctxt.vars in

      let _ =
        if mut
          then ()
          else failwith "Cannot assign to immutable var"
      in

      if type_convertible_to exp_t var_t
        then (tc_ctxt, AssignStmt(ident, exp_typechecked))
        else failwith "Expr for assignment does not typecheck"

  | AssignDeconStmt(idents, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt exp in
      let exp_t = expr_type exp_typechecked in

      let typecheck_id_typ_pairs idents types =
        List.iter2 (
          fun id typ ->
            let (var_t, {mut}) = StrMap.find id tc_ctxt.vars in
            let _ = if mut
              then ()
              else failwith "Cannot assign to immutable var"
            in
            if type_convertible_to typ var_t
              then ()
              else failwith "Cannot assign type to var"
        ) idents types
      in

      begin match exp_t with
        | Array(typ, sz) ->
          let _ =
            if List.length idents == sz
              then
                let types = List.init sz (fun _ -> typ) in
                typecheck_id_typ_pairs idents types
              else failwith "Mismatch in number of idents vs array expr in assi"
          in

          (tc_ctxt, AssignDeconStmt(idents, exp_typechecked))

        | Tuple(types) ->
          let _ =
            if List.length idents == List.length types
              then typecheck_id_typ_pairs idents types
              else failwith "Mismatch in number of idents vs tuple expr in assi"
          in

          (tc_ctxt, AssignDeconStmt(idents, exp_typechecked))

        | _ -> failwith "Cannot deconstruct non-aggregate type into ids"
      end

  | ExprStmt(exp) -> (tc_ctxt, ExprStmt(type_check_expr tc_ctxt exp))
  | BlockStmt (stmts) ->
      let (tc_ctxt_up, stmts_typechecked) = type_check_stmts tc_ctxt stmts in
      (tc_ctxt_up, BlockStmt(stmts_typechecked))

  | IfThenElseStmt (if_cond, then_stmt, else_stmt) ->
      let if_cond_typechecked = type_check_expr tc_ctxt if_cond in
      let (_, then_stmt_typechecked) = type_check_stmt tc_ctxt then_stmt in
      let (_, else_stmt_typechecked) = type_check_stmt tc_ctxt else_stmt in
      (
        tc_ctxt,
        IfThenElseStmt(
          if_cond_typechecked,
          then_stmt_typechecked,
          else_stmt_typechecked
        )
      )

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

and type_check_expr (tc_ctxt : typecheck_context) (exp : expr) =
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

    | FuncCall(_, f_name, exprs) ->
        let (ret_t, params) = StrMap.find f_name tc_ctxt.mod_ctxt.func_sigs in
        let exprs_typechecked = List.map (type_check_expr tc_ctxt) exprs in
        let exprs_t = List.map expr_type exprs_typechecked in
        let params_t = List.map (fun (_, _, param_t) -> param_t) params in
        let _ = List.iter2 (
          fun expr_t param_t ->
            if type_convertible_to expr_t param_t
            then ()
            else failwith "Could not convert expr type to arg type"
        ) exprs_t params_t in

        FuncCall(ret_t, f_name, exprs_typechecked)

    | ArrayExpr(_, exprs) ->
        let exprs_typechecked = List.map (type_check_expr tc_ctxt) exprs in
        let expr_t_lst = List.map expr_type exprs_typechecked in
        let common_t = common_type_of_lst expr_t_lst in
        let arr_t = Array(common_t, List.length exprs) in

        ArrayExpr(arr_t, exprs_typechecked)

    | IndexExpr(_, idx, arr) ->
        let idx_typechecked = type_check_expr tc_ctxt idx in
        let arr_typechecked = type_check_expr tc_ctxt arr in
        let idx_t = expr_type idx_typechecked in
        let arr_t = expr_type arr_typechecked in
        if is_index_type idx_t && is_indexable_type arr_t
          then
            begin match arr_t with
            | Array(elem_typ, sz) ->
                begin match idx_typechecked with
                  | ValU64(i)
                  | ValU32(i)
                  | ValU16(i)
                  | ValU8(i) ->
                      if i < sz
                        then
                          IndexExpr(
                            elem_typ, idx_typechecked, arr_typechecked
                          )
                        else failwith "Static out-of-bounds index into array"
                  | _ ->
                      IndexExpr(
                        elem_typ, idx_typechecked, arr_typechecked
                      )
                end
            | _ -> failwith "Unexpected index target in index expr"
            end
          else failwith "Unexpected components of index operation"

    | StaticIndexExpr(_, idx, arr) ->
        let arr_typechecked = type_check_expr tc_ctxt arr in
        let arr_t = expr_type arr_typechecked in
        let static_idx_typechecked = begin
          match arr_t with
          | Array(elem_typ, sz) ->
            begin
              if idx < 0 || idx >= sz
              then failwith "out-of-bounds idx for array"
              else StaticIndexExpr(elem_typ, idx, arr_typechecked)
            end
          | _ -> failwith "Unexpectedly indexing into non-array"
        end in

        static_idx_typechecked

    | TupleExpr(_, exprs) ->
        let exprs_typechecked = List.map (type_check_expr tc_ctxt) exprs in
        let exprs_t_lst = List.map expr_type exprs_typechecked in
        let tuple_t = Tuple(exprs_t_lst) in

        TupleExpr(tuple_t, exprs_typechecked)

;;
