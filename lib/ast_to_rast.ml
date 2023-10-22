open Ast
open Ir
open Rast
open Rast_typing
open Utility

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
  | ValInt(t, i) ->
      let rt = berk_t_to_rast_t t in
      RValInt(rt, i)

  | ValVar(t, name) ->
      let rt = berk_t_to_rast_t t in
      RValVar(rt, name)
  | ValFunc(t, name) ->
      let rt = berk_t_to_rast_t t in
      RValFunc(rt, name)

  | ValRawArray(t) ->
      let rt = berk_t_to_rast_t t in
      RValRawArray(rt)

  | ValCast(t, op, e) ->
      let rt = berk_t_to_rast_t t in
      let re = expr_to_rexpr e in
      RValCast(rt, op, re)

  | RefOf(t, e) ->
      let rt = berk_t_to_rast_t t in
      let re = expr_to_rexpr e in
      RAddressOf(rt, re)

  | DerefOf(t, e) ->
      let rt = berk_t_to_rast_t t in
      let re = expr_to_rexpr e in
      RDerefAddr(rt, re)

  | UnOp(t, LNot, e) ->
      let rt = berk_t_to_rast_t t in
      let re = expr_to_rexpr e in
      RUnOp(rt, LNot, re)

  | BinOp(t, LOr, e_lhs, e_rhs) ->
      let rt = berk_t_to_rast_t t in
      let re_lhs = expr_to_rexpr e_lhs in
      let re_rhs = expr_to_rexpr e_rhs in
      RMatchExpr(
        rt, re_lhs, [
          (RPBool(true), RValBool(true));
          (RWild(RBool), re_rhs);
        ]
      )

  | BinOp(t, LAnd, e_lhs, e_rhs) ->
      let rt = berk_t_to_rast_t t in
      let re_lhs = expr_to_rexpr e_lhs in
      let re_rhs = expr_to_rexpr e_rhs in
      RMatchExpr(
        rt, re_lhs, [
          (RPBool(false), RValBool(false));
          (RWild(RBool), re_rhs);
        ]
      )

  | BinOp(t, op, e_lhs, e_rhs) ->
      let rt = berk_t_to_rast_t t in
      let rop = op_to_rop op in
      let re_lhs = expr_to_rexpr e_lhs in
      let re_rhs = expr_to_rexpr e_rhs in
      RBinOp(rt, rop, re_lhs, re_rhs)

  | BlockExpr(t, stmts, e) ->
      let rt = berk_t_to_rast_t t in
      let re = expr_to_rexpr e in
      let rstmts = List.map stmt_to_rstmt stmts in
      let wrapped_rstmts = RStmts(rstmts) in
      RBlockExpr(rt, wrapped_rstmts, re)

  | ExprInvoke(t, e_func, e_args) ->
      let rt = berk_t_to_rast_t t in
      let re_func = expr_to_rexpr e_func in
      let re_args = List.map expr_to_rexpr e_args in
      RExprInvoke(rt, re_func, re_args)

  | FuncCall(t, name, e_args) ->
      let rt = berk_t_to_rast_t t in
      let args_rts =
        List.map (
          fun e_arg ->
            let expr_t = expr_type e_arg in
            berk_t_to_rast_t expr_t
        ) e_args
      in
      let func_rt : rast_t = RFunction(rt, args_rts) in
      let re_func = RValFunc(func_rt, name) in

      let re_args = List.map expr_to_rexpr e_args in

      RExprInvoke(rt, re_func, re_args)

  | UfcsCall(t, e_arg_first, name, underscore_pos, e_args_rest) ->
      (* Inject the e_arg_first into the correct spot in e_args_all depending on
      its position as indicated by the (possibly implicit) underscore. *)
      let e_args_all = insert e_args_rest underscore_pos e_arg_first in

      let rewritten_as_func_call = FuncCall(t, name, e_args_all) in

      expr_to_rexpr rewritten_as_func_call

  | ArrayExpr(t, e_elems) ->
      let rt = berk_t_to_rast_t t in
      let re_elems = List.map expr_to_rexpr e_elems in
      RArrayExpr(rt, re_elems)

  | IndexExpr(t, e_idx, e_arr) ->
      let rt = berk_t_to_rast_t t in
      let re_idx = expr_to_rexpr e_idx in
      let re_arr = expr_to_rexpr e_arr in
      RIndexExpr(rt, re_idx, re_arr)

  | TupleIndexExpr(t, i, e_tuple) ->
      let rt = berk_t_to_rast_t t in
      let re_tuple = expr_to_rexpr e_tuple in
      RTupleIndexExpr(rt, i, re_tuple)

  | TupleExpr(t, e_elems) ->
      let rt = berk_t_to_rast_t t in
      let re_elems = List.map expr_to_rexpr e_elems in
      RTupleExpr(rt, re_elems)

  | VariantCtorExpr(t, ctor_name, e_fields) ->
      (* "Type-erase" the value of the variant constructor into (what's expected
      to be) a union type. *)
      let rt = berk_t_to_rast_t t in

      let ctor_tuple = begin
        let open Typing in

        let ctor_idx = get_tag_index_by_variant_ctor t ctor_name in
        let ctor_idx_rexpr = RValInt(variant_tag_rt, ctor_idx) in

        let ctor_accessible_fields = List.map expr_to_rexpr e_fields in
        let ctor_all_fields = ctor_idx_rexpr :: ctor_accessible_fields in

        let tuple_ts = List.map rexpr_type ctor_all_fields in
        let tuple_t : rast_t = RTuple(tuple_ts) in

        RTupleExpr(tuple_t, ctor_all_fields)
      end in

      RValCast(rt, Bitwise, ctor_tuple)

  | IfThenElseExpr(t, e_cond, e_then, e_else) ->
      let rt = berk_t_to_rast_t t in
      let re_cond = expr_to_rexpr e_cond in
      let re_then = expr_to_rexpr e_then in
      let re_else = expr_to_rexpr e_else in
      RMatchExpr(
        rt,
        re_cond, [
          (RPBool(true), re_then);
          (RWild(RBool), re_else)
        ]
      )

  | IfIsThenElseExpr(t, e_conds, e_then, e_else) ->
      let rt = berk_t_to_rast_t t in
      let re_then = expr_to_rexpr e_then in
      let re_else = expr_to_rexpr e_else in

      let rec _if_is_conds_to_rexpr conds =
        begin match conds with
        | [] ->
            re_then

        | IfIsGeneral(e_cond_part) :: rest ->
            let re_cond_part = expr_to_rexpr e_cond_part in
            let re_cond_rest = _if_is_conds_to_rexpr rest in

            RMatchExpr(
              rt,
              re_cond_part, [
                (RPBool(true), re_cond_rest);
                (RWild(RBool), re_else)
              ]
            )

        | IfIsPattern(exp, patt) :: rest ->
            let re_cond_part = expr_to_rexpr exp in
            let re_patt = pattern_to_rpattern patt in
            let re_rt = rexpr_type re_cond_part in
            let re_cond_rest = _if_is_conds_to_rexpr rest in

            RMatchExpr(
              rt,
              re_cond_part, [
                (re_patt, re_cond_rest);
                (RWild(re_rt), re_else)
              ]
            )

        end
      in
      _if_is_conds_to_rexpr e_conds

  | WhileExpr(t, stmts_init, e_cond, stmts_block) ->
      let rt = berk_t_to_rast_t t in
      let rstmts_init = List.map stmt_to_rstmt stmts_init in
      let rstmts_block = List.map stmt_to_rstmt stmts_block in
      let re_cond = expr_to_rexpr e_cond in
      RWhileExpr(rt, rstmts_init, re_cond, rstmts_block)

  | MatchExpr(t, e_cond, patts_to_exprs) ->
      let rt = berk_t_to_rast_t t in
      let re_cond = expr_to_rexpr e_cond in
      let rpatts_to_rexprs =
        List.map (
          fun (patt, expr) ->
            let rpatt = pattern_to_rpattern patt in
            let rexpr = expr_to_rexpr expr in
            (rpatt, rexpr)
        ) patts_to_exprs
      in
      RMatchExpr(rt, re_cond, rpatts_to_rexprs)
  end

and pattern_to_rpattern patt : rpattern =
  begin match patt with
  | PNil -> RPNil

  | Wild(t) ->
      let rt = berk_t_to_rast_t t in
      RWild(rt)

  | VarBind(t, name) ->
      let rt = berk_t_to_rast_t t in
      RVarBind(rt, name)

  | PBool(b) -> RPBool(b)

  | PInt(t, IRangeLiteral(i)) ->
      let rt = berk_t_to_rast_t t in
      RPIntLit(rt, i)

  | PInt(t, IRangeAllFrom(i)) ->
      let rt = berk_t_to_rast_t t in
      RPIntFrom(rt, i)

  | PInt(t, IRangeAllUntil(i)) ->
      let rt = berk_t_to_rast_t t in
      RPIntUntil(rt, i)

  | PInt(t, IRangeFromUntil(i, j)) ->
      let rt = berk_t_to_rast_t t in
      RPIntRange(rt, i, j)

  | PInt(_, IRangeAll) -> failwith "IRangeAll should not survive typecheck"

  | PTuple(t, patts) ->
      let rt = berk_t_to_rast_t t in
      let rpatts = List.map pattern_to_rpattern patts in
      RPTuple(rt, rpatts)

  | Ctor(t, ctor_name, patts) ->
      (* The variant value will come to us as a "type-erased" union type, that
      we'll need to (attempt to) bitwise-cast into a specific constructor tuple
      pattern. *)

      let ctor_tuple_t : rast_t = begin
        let open Typing in

        let v_ctor = get_v_ctor t ctor_name in
        let ctor_tuple_ts = v_ctor_as_tagged_type_list v_ctor in
        RTuple(ctor_tuple_ts)
      end in

      let tuple_patt = begin
        let open Typing in

        let idx = get_tag_index_by_variant_ctor t ctor_name in
        let rpatts = List.map pattern_to_rpattern patts in
        let tuple_rpatts = RPIntLit(variant_tag_rt, idx) :: rpatts in

        RPTuple(ctor_tuple_t, tuple_rpatts)
      end in

      let rt = berk_t_to_rast_t t in
      RPCastThen(rt, ctor_tuple_t, Bitwise, tuple_patt)

  | PatternAs(t, patt, name) ->
      let rt = berk_t_to_rast_t t in
      let rpatt = pattern_to_rpattern patt in
      RPatternAs(rt, rpatt, name)
  end

(* Translate lval-assignment-specific indexing into the generic "evaluate
to a ptr" logic that both RHS and LHS indexing can share. *)
and assign_idx_lval_to_rexpr_index rexpr (idxs : assign_idx_lval list) : rexpr =
  let index_expr =
    List.fold_left (
      fun cur_exp (idx : assign_idx_lval) ->
        begin match idx with
        | ALStaticIndex(indexed_t, i) ->
            let indexed_rt = berk_t_to_rast_t indexed_t in
            RTupleIndexExpr(indexed_rt, i, cur_exp)

        | ALIndex(indexed_t, e) ->
            let indexed_rt = berk_t_to_rast_t indexed_t in
            let re = expr_to_rexpr e in
            RIndexExpr(indexed_rt, re, cur_exp)

        | ALDeref(derefed_t) ->
            let derefed_rt = berk_t_to_rast_t derefed_t in
            RDerefAddr(derefed_rt, cur_exp)
        end
    ) rexpr idxs
  in
  index_expr

and stmt_to_rstmt stmt : rstmt =
  begin match stmt with
  | ExprStmt(_, e) ->
      let re = expr_to_rexpr e in
      RExprStmt(re)

  | ReturnStmt(e) ->
      let re = expr_to_rexpr e in
      RReturnStmt(re)

  | DeclStmt(name, _, t, e) ->
      let rt = berk_t_to_rast_t t in
      let re = expr_to_rexpr e in
      RDeclStmt(name, rt, re)

  | DeclDefaultStmt(names_quals_ts) ->
      let names_rts =
        List.map (
          fun (name, _, t) ->
            let rt = berk_t_to_rast_t t in
            (name, rt)
        ) names_quals_ts
      in
      RDeclDefaultStmt(names_rts)

  | AssignStmt(name, named_t, idxs, e) ->
      let named_rt = berk_t_to_rast_t named_t in
      let start_rexpr = RValVar(named_rt, name) in
      let ridx = assign_idx_lval_to_rexpr_index start_rexpr idxs in
      let named_rt = berk_t_to_rast_t named_t in
      let re = expr_to_rexpr e in
      RAssignStmt(name, named_rt, ridx, re)

  (* Deconstructing `let` stmts can be described as first assigning the
  result of the expr-to-be-deconstructed to a placeholder named variable, and
  then performing a series of indexes onto that variable into the target
  "real" deconstructed variable names. *)
  | DeclDeconStmt(names_quals, t, e) ->
      let names = List.map (fun (name, _) -> name) names_quals in
      let rt = berk_t_to_rast_t t in
      let re = expr_to_rexpr e in

      let placeholder_name = Printf.sprintf "__%s" (fmt_join_strs "_" names) in

      let init_rstmt = RDeclStmt(placeholder_name, rt, re) in
      let decon_rstmts =
        begin match t with
        | Tuple(ts) ->
            map2i (
              fun i name elem_t ->
                let elem_rt = berk_t_to_rast_t elem_t in
                RDeclStmt(
                  name, elem_rt,
                  RTupleIndexExpr(elem_rt, i, RValVar(rt, placeholder_name))
                )
            ) names ts

        | _ ->
            failwith "Cannot rewrite deconstruction of non-tuple decl."
        end
      in
      RStmts(init_rstmt :: decon_rstmts)
  end

and f_param_to_rf_param (name, _, t) =
  let rt = berk_t_to_rast_t t in
  (name, rt)

and func_decl_t_to_rfunc_decl_t {f_name; f_params; f_ret_t} =
  let rf_params = List.map f_param_to_rf_param f_params in
  let rf_ret_rt = berk_t_to_rast_t f_ret_t in
  {rf_name=f_name; rf_params=rf_params; rf_ret_t=rf_ret_rt}

and func_def_t_to_rfunc_def_t
  {f_decl=({f_name; f_ret_t; _} as f_decl); f_stmts}
=
  (* Ensure there is a trailing return stmt if there isn't one already. *)
  let f_stmts =
    begin match (List.rev f_stmts) with
    | ReturnStmt(_) :: _ -> f_stmts
    | []
    | _ :: _ ->
        if f_ret_t = Nil then
          f_stmts @ [ReturnStmt(ValNil)]
        else
          failwith (
            Printf.sprintf "No trailing return-stmt but non-nil function [%s]"
              f_name
          )
    end
  in

  (* Generate RAST function declaration from source AST. *)
  let rf_decl = func_decl_t_to_rfunc_decl_t f_decl in

  (* Generate RAST function definition from the source AST. *)
  let rf_stmts = List.map stmt_to_rstmt f_stmts in

  {rf_decl=rf_decl; rf_stmts=rf_stmts}
;;
