open Hir
open Ir
open Rast
open Rast_typing


type hir_ctxt = {
  func_vars: (rast_t * int) StrMap.t;
  seen_vars: hir_variable StrMap.t;
  tmp_counter: int;
}

let default_hir_ctxt : hir_ctxt = {
  func_vars = StrMap.empty;
  seen_vars = StrMap.empty;
  tmp_counter = 0;
}


let get_tmp_name hir_ctxt : (hir_ctxt * string) =
  (
    {hir_ctxt with tmp_counter = hir_ctxt.tmp_counter + 1},
    "__hir_tmp_" ^ (Printf.sprintf "%d" hir_ctxt.tmp_counter)
  )
;;


let rec rexpr_to_hir hctxt hscope rexpr
  : (hir_ctxt * hir_scope * hir_variable)
=
  begin match rexpr with
  | RValVar(t, name) ->
      (* Check whether the given name represents a function argument. *)
      begin match (StrMap.find_opt name hctxt.func_vars) with
      | Some((t, i)) ->
          (* This name refers to a function argument. *)
          let (hctxt, tmp) = get_tmp_name hctxt in
          let decl = (t, tmp) in
          let decls = decl :: hscope.declarations in
          let instr = Instr(HArgToVar(decl, name, i)) in
          let instrs = instr :: hscope.instructions in
          let hscope = {declarations = decls; instructions = instrs} in
          (hctxt, hscope, decl)

      | None ->
          (* This was not a function argument. *)
          let decl = (t, name) in
          (hctxt, hscope, decl)
      end

  | RValFunc(func_t, func_name) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (func_t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValFunc(func_name))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValNil ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RNil, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValNil)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValBool(b) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValBool(b))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValStr(s) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RString, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValStr(s))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF32(f) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RF32, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValF32(f))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF64(f) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RF64, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValF64(f))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF128(s) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RF128, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValF128(s))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValInt(t, x) ->
      let hval =
        begin match t with
        | RU8 ->  HValU8 (x)
        | RU16 -> HValU16(x)
        | RU32 -> HValU32(x)
        | RU64 -> HValU64(x)
        | RI8 ->  HValI8 (x)
        | RI16 -> HValI16(x)
        | RI32 -> HValI32(x)
        | RI64 -> HValI64(x)
        | _ ->
            failwith (
              Printf.sprintf "Nonsense type [%s] for int [%d] convert to HIR."
                (fmt_rtype t) x
            )
        end
      in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, hval)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RUnOp(t, op, exp) ->
      let (hctxt, hscope, rhs_var) = rexpr_to_hir hctxt hscope exp in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HUnOp(decl, op, rhs_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValCast(t, op, exp) ->
      let (hctxt, hscope, rhs_var) = rexpr_to_hir hctxt hscope exp in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValCast(decl, op, rhs_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RBinOp(t, op, lhs, rhs) ->
      let (hctxt, hscope, lhs_var) = rexpr_to_hir hctxt hscope lhs in
      let (hctxt, hscope, rhs_var) = rexpr_to_hir hctxt hscope rhs in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HBinOp(decl, op, lhs_var, rhs_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  (* Declare an outer variable, create an inner scope, evaluate an initial
  statement within that inner scope, evaluate an expr within that inner scope
  and assign the result to the declared outer variable. *)
  | RBlockExpr(t, rstmt, rexpr) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in

      let inner_scope = empty_scope in
      let (hctxt, inner_scope) = rstmt_to_hir hctxt inner_scope rstmt in
      let (hctxt, inner_scope, hvar) = rexpr_to_hir hctxt inner_scope rexpr in

      let inner_instr = Instr(HValueAssign(decl, HValVar(hvar))) in
      let inner_instrs = inner_instr :: inner_scope.instructions in
      let inner_scope = {inner_scope with instructions = inner_instrs} in

      let instr = Scope(inner_scope) in
      let instrs = instr :: hscope.instructions in

      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RTupleExpr(t, rexprs) ->
      let ((hctxt, hscope), hvars) =
        List.fold_left_map (
          fun (hctxt, hscope) rexpr ->
            let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in
            ((hctxt, hscope), hvar)
        ) (hctxt, hscope) rexprs
      in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HAggregate(decl, hvars)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RTupleIndexExpr(_, idx, tuple_exp) ->
      let tup_t = rexpr_type tuple_exp in
      let elem_t = unwrap_aggregate_indexable tup_t idx in

      let (hctxt, hscope, tup_var) = rexpr_to_hir hctxt hscope tuple_exp in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (elem_t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HAggregateIndex(decl, idx, tup_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RIndexExpr(_, idx_expr, idxable_expr) ->
      let (hctxt, hscope, idx) = rexpr_to_hir hctxt hscope idx_expr in
      let (hctxt, hscope, idxable) = rexpr_to_hir hctxt hscope idxable_expr in

      let (arr_t, _) = idxable in

      let elem_t = unwrap_ptr arr_t in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (elem_t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HDynamicIndex(decl, idx, idxable)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RWhileExpr (_, init_stmts, while_cond, then_stmts) ->
      (* Evaluate the initializing statements. *)
      let (hctxt, hscope) =
        List.fold_left (
          fun (hctxt, hscope) init_stmt ->
            let (hctxt, hscope) = rstmt_to_hir hctxt hscope init_stmt in

            (hctxt, hscope)
        ) (hctxt, hscope) init_stmts
      in

      (* Evaluate the condition into a single variable. *)
      let loop_cond_scope = empty_scope in
      let (hctxt, loop_cond_scope, cond_var) =
        rexpr_to_hir hctxt loop_cond_scope while_cond
      in

      (* Evaluate the body of the loop into an inner scope. *)
      let loop_body_scope = empty_scope in
      let (hctxt, loop_body_scope) =
        List.fold_left (
          fun (hctxt, loop_body_scope) then_stmt ->
            let (hctxt, loop_body_scope) =
              rstmt_to_hir hctxt loop_body_scope then_stmt
            in

            (hctxt, loop_body_scope)
        ) (hctxt, loop_body_scope) then_stmts
      in

      (* Inject the inner conditional loop scope into our scope/context. *)
      let instr = CondLoopScope(loop_cond_scope, cond_var, loop_body_scope) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (* NOTE: We're creating a dummy result value, as WhileExpr doesn't yet
      support yielding a result value. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RNil, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValNil)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RValRawArray(t) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let hscope = {hscope with declarations = decls} in

      (hctxt, hscope, decl)

  | RArrayExpr(t, rexprs) ->
      let ((hctxt, hscope), hvars) =
        List.fold_left_map (
          fun (hctxt, hscope) rexpr ->
            let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in
            ((hctxt, hscope), hvar)
        ) (hctxt, hscope) rexprs
      in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HAggregate(decl, hvars)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RExprInvoke(ret_t, func_rexpr, arg_rexprs) ->
      let (hctxt, hscope, hfunc) = rexpr_to_hir hctxt hscope func_rexpr in

      let ((hctxt, hscope), hargs) =
        List.fold_left_map (
          fun (hctxt, hscope) rexpr ->
            let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in
            ((hctxt, hscope), hvar)
        ) (hctxt, hscope) arg_rexprs
      in

      let get_invoke_instr t decl hfunc hargs =
        begin match t with
        | RNil -> HExprInvokeVoid(hfunc, hargs)
        | _ -> HExprInvoke(decl, hfunc, hargs)
        end
      in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (ret_t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(get_invoke_instr ret_t decl hfunc hargs) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RMatchExpr(t, matched_exp, patts_to_exprs) ->
      let (hctxt, hscope, hmatchee) = rexpr_to_hir hctxt hscope matched_exp in

      (* Create a variable which will be assigned to in each match arm with
      the match-arm result value. This will be used as the overall match-expr
      result value. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let hscope = {hscope with declarations = decls} in

      (* Create an inner scope within which we'll generate the match arms. *)
      let match_scope = empty_scope in

      let (hctxt, match_scope) =
        rmatch_arms_to_hir hctxt match_scope hmatchee decl patts_to_exprs
      in

      let instr = Scope(match_scope) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope, decl)
  end


(* Deconstruct a match pattern, returning a true/false boolean hvariable
indicating whether the match arm should be evaluated. *)
and rpattern_to_hir hctxt hscope hmatchee patt =
  begin match patt with
  | RPNil ->
      (* Create a temporary containing an unconditionally-true boolean,
      indicating this match pattern always succeeds. *)
      let (hctxt, hscope, htrue) = rexpr_to_hir hctxt hscope (RValBool(true)) in

      (hctxt, hscope, htrue)

  | RWild(_) ->
      (* Create a temporary containing an unconditionally-true boolean,
      indicating this match pattern always succeeds. *)
      let (hctxt, hscope, htrue) = rexpr_to_hir hctxt hscope (RValBool(true)) in

      (hctxt, hscope, htrue)

  | RVarBind(t, name) ->
      (* Create a temporary containing an unconditionally-true boolean,
      indicating this match pattern always succeeds. *)
      let (hctxt, hscope, htrue) = rexpr_to_hir hctxt hscope (RValBool(true)) in

      (* Declare a new variable that binds to the matchee.

      TODO: Later: this should be a transparent reference to the actual matched
      value. *)
      let decl = (t, name) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValVar(hmatchee))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, htrue)

  | RPatternAs(t, as_patt, name) ->
      (* Declare a new variable that binds to the matchee.

      TODO: Later: this should be a transparent reference to the actual matched
      value. *)
      let decl = (t, name) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValVar(hmatchee))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (* Evaluate the actual pattern. *)
      let (hctxt, hscope, hbool) =
        rpattern_to_hir hctxt hscope hmatchee as_patt
      in

      (hctxt, hscope, hbool)

  | RPBool(b) ->
      (* Create a temporary containing the boolean to match against. *)
      let (hctxt, hscope, hbool) = rexpr_to_hir hctxt hscope (RValBool(b)) in

      (* Create an instruction to compare the matchee against the boolean. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HBinOp(decl, Eq, hmatchee, hbool)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RPCastThen(target_t, op, casted_patt) ->
      (* Cast the matchee to the target type, then descend into the sub
      pattern. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (target_t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValCast(decl, op, hmatchee)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      rpattern_to_hir hctxt hscope decl casted_patt

  | RPIntLit(t, i) ->
      (* Create a temporary containing the int to match against. *)
      let (hctxt, hscope, hint) = rexpr_to_hir hctxt hscope (RValInt(t, i)) in

      (* Create an instruction to compare the matchee against the int. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HBinOp(decl, Eq, hmatchee, hint)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RPIntFrom(t, i) ->
      (* Create a temporary containing the int to compare against. *)
      let (hctxt, hscope, hint) = rexpr_to_hir hctxt hscope (RValInt(t, i)) in

      (* Create an instruction to compare the matchee against the int. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HBinOp(decl, Ge, hmatchee, hint)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RPIntUntil(t, i) ->
      (* Create a temporary containing the int to compare against. *)
      let (hctxt, hscope, hint) = rexpr_to_hir hctxt hscope (RValInt(t, i)) in

      (* Create an instruction to compare the matchee against the int. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HBinOp(decl, Lt, hmatchee, hint)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RPIntRange(t, i, j) ->
      (* Create a temporary containing the first to compare against. *)
      let (hctxt, hscope, hlhs) = rexpr_to_hir hctxt hscope (RValInt(t, i)) in
      (* Create a temporary containing the second to compare against. *)
      let (hctxt, hscope, hrhs) = rexpr_to_hir hctxt hscope (RValInt(t, j)) in

      (* Create an instruction to compare the matchee against the first int. *)
      let (hctxt, hscope, hlhs_cmp) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (RBool, tmp) in
        let decls = decl :: hscope.declarations in
        let instr = Instr(HBinOp(decl, Ge, hmatchee, hlhs)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (* Create an instruction to compare the matchee against the second int. *)
      let (hctxt, hscope, hrhs_cmp) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (RBool, tmp) in
        let decls = decl :: hscope.declarations in
        let instr = Instr(HBinOp(decl, Lt, hmatchee, hrhs)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (* Create an instruction to confirm the int was within the range . *)
      let (hctxt, hscope, hwithin_range) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (RBool, tmp) in
        let decls = decl :: hscope.declarations in
        let instr = Instr(HBinOp(decl, Eq, hlhs_cmp, hrhs_cmp)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (hctxt, hscope, hwithin_range)

  | RPTuple(tup_t, patts) ->
      (* Declare a boolean, defaulting to true but assignable to false in the
      case that any of the tuple elems don't match the pattern. *)
      let (hctxt, hscope, hoverall_bool) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (RBool, tmp) in
        let decls = decl :: hscope.declarations in
        let instr = Instr(HValueAssign(decl, HValBool(true))) in
        let instrs = instr :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (* Descend into the patterns for each of the elements of the tuple,
      short-circuiting if any pattern in turn doesn't match. *)

      let rec _rptuple_patt_deconstruct hctxt cur_scope idx patts =
        begin match patts with
        | [] ->
            let dead_scope = empty_scope in

            (hctxt, dead_scope)

        | patt :: patts_rest ->
            let (hctxt, cur_scope, helem) = begin
              let elem_t = unwrap_aggregate_indexable tup_t idx in

              let (hctxt, tmp) = get_tmp_name hctxt in
              let decl = (elem_t, tmp) in
              let decls = decl :: cur_scope.declarations in
              let instr = Instr(HAggregateIndex(decl, idx, hmatchee)) in
              let instrs = instr :: cur_scope.instructions in
              let cur_scope = {declarations = decls; instructions = instrs} in
              (hctxt, cur_scope, decl)
            end in

            (* Evaluate the tuple-element sub-pattern, yielding a match/no-match
            boolean value. *)
            let (hctxt, cur_scope, elem_res) =
              rpattern_to_hir hctxt cur_scope helem patt
            in

            (* Recursively evaluate the remainder of the sub-patterns in the
            tuple pattern, building a hierarchy of conditional inner scopes,
            accomplishing a short-circuiting tuple pattern match. *)
            let (hctxt, rest_scope) =
              _rptuple_patt_deconstruct hctxt empty_scope (idx + 1) patts_rest
            in

            (* In the event the sub-pattern did not match, assign "no-match"
            to our top-level whole-tuple match/no-match boolean. *)
            let else_scope = begin
              let else_scope = empty_scope in
              let instr =
                Instr(HValueAssign(hoverall_bool, HValBool(false)))
              in
              let instrs = instr :: else_scope.instructions in
              let else_scope = {else_scope with instructions = instrs} in
              else_scope
            end in

            let instr = CondScope(elem_res, rest_scope, else_scope) in
            let instrs = instr :: cur_scope.instructions in
            let cur_scope = {cur_scope with instructions = instrs} in

            (hctxt, cur_scope)
        end
      in

      (* Build a short-circuiting tuple match tree, where the value of
      hoverall_bool determines if the match was successful. *)
      let (hctxt, tuple_match_scope) =
        _rptuple_patt_deconstruct hctxt empty_scope 0 patts
      in

      let instr = Scope(tuple_match_scope) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, hoverall_bool)
  end


(* Given a complete, ordered set of pattern-to-match-arms, generate HIR that
represents this match expression. *)
and rmatch_arms_to_hir hctxt hscope hmatchee hresult patts_to_exprs
  : (hir_ctxt * hir_scope)
=
  let rec _rmatch_arms_to_hir hctxt hscope patts_to_exprs =
    begin match patts_to_exprs with
    (* We have exhausted the match arms. *)
    | [] ->
        (* TODO: This scope should be impossible to reach, as that implies
        that no match arms in a match expr matched the matchee, which should
        be statically impossible and verified during typecheck. We should add
        some sort of an assert/crash/halt here. *)
        let dead_scope = empty_scope in

        (hctxt, dead_scope)

    | (patt, expr) :: patts_to_exprs_rest ->
        (* Evaluate a boolean variable indicating whether we should enter this
        match arm. *)
        let (hctxt, hscope, hmatched) =
          rpattern_to_hir hctxt hscope hmatchee patt
        in

        (* Evaluate the arm expression, assigning the arm result to the
        overall match-expr result. *)
        let (hctxt, arm_exp_scope) =
          begin
            let arm_exp_scope = empty_scope in

            let (hctxt, arm_exp_scope, arm_result) =
              rexpr_to_hir hctxt arm_exp_scope expr
            in

            let instr = Instr(HValueAssign(hresult, HValVar(arm_result))) in
            let instrs = instr :: arm_exp_scope.instructions in
            let arm_exp_scope = {arm_exp_scope with instructions = instrs} in

            (hctxt, arm_exp_scope)
          end
        in

        (* Evaluate the next arm, in a fresh scope. *)
        let (hctxt, next_arm_scope) =
          let next_arm_scope = empty_scope in

          let (hctxt, next_arm_scope) =
            _rmatch_arms_to_hir hctxt next_arm_scope patts_to_exprs_rest
          in

          (hctxt, next_arm_scope)
        in

        (* Incorporate the potentially arbitrarily-nested conditional-scope
        hierarchy, representing the N match arms of this arm and all
        following arms, into the current scope. *)
        let instr = CondScope(hmatched, arm_exp_scope, next_arm_scope) in
        let instrs = instr :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in

        (hctxt, hscope)
    end
  in

  let (hctxt, hscope) = _rmatch_arms_to_hir hctxt hscope patts_to_exprs in

  (hctxt, hscope)


and rstmt_to_hir hctxt hscope rstmt : (hir_ctxt * hir_scope) =
  begin match rstmt with
  (* "Expand" a list of rstmts into hir instructions. *)
  | RStmts(rstmts) ->
      List.fold_left (
        fun (hctxt, hscope) rstmt -> rstmt_to_hir hctxt hscope rstmt
      ) (hctxt, hscope) rstmts

  (* Evaluate an expression. The result is abandoned. *)
  | RExprStmt(rexpr) ->
      let (hctxt, hscope, _) = rexpr_to_hir hctxt hscope rexpr in
      (hctxt, hscope)

  (* Declare, evaluate the expr for, and assign, a new named variable. *)
  | RDeclStmt(name, _, rexpr) ->
      (* NOTE: The declared type is not used. We might be doing some sort of an
      internal representational transformation and want to use the resultant
      transformation type, not the high-level original type. *)

      let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in
      let hvar_t = hir_variable_type hvar in

      let decl = (hvar_t, name) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValVar(hvar))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope)

  (* Declare a list of new named variables. *)
  | RDeclDefStmt(name_t_pairs) ->
      (* NOTE: This depends on an earlier pass having ensured that the only
      variables declared this way are those with types that have deterministic
      default values, which coincidentally is also the set of types which we
      would lower any higher-level types into. *)
      List.fold_left (
        fun (hctxt, hscope) (name, t) ->
          let decl = (t, name) in
          let decls = decl :: hscope.declarations in
          let hscope = {hscope with declarations = decls} in
          (hctxt, hscope)
      ) (hctxt, hscope) name_t_pairs

  | RReturnStmt(rexpr) ->
      let (hctxt, hscope, ((t, _) as hvar)) = rexpr_to_hir hctxt hscope rexpr in

      let ret_instr =
        begin match t with
        | RNil -> HRetVoid
        | _ -> HReturn(hvar)
      end in

      let instr = Instr(ret_instr) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope)

  (* Assign the RHS rexpr to the result of possibly-zero indexes into the LHS
  lvalue. *)
  | RAssignStmt(name, named_t, rassign_idx_lvals, rexpr) ->
      let (hctxt, hscope, rhs_hvar) = rexpr_to_hir hctxt hscope rexpr in

      let named_hvar = (named_t, name) in

      (* Possibly-zero indexing operations, yielding a resultant lvalue. *)
      let (hctxt, hscope, indexed_hvar) =
        List.fold_left (
          fun (hctxt, hscope, hvar) rassign_idx_lval ->
            begin match rassign_idx_lval with
            | RALStaticIndex(t, i) ->
                let (hctxt, tmp) = get_tmp_name hctxt in
                let decl = (t, tmp) in
                let decls = decl :: hscope.declarations in
                let instr = Instr(HAggregateIndex(decl, i, hvar)) in
                let instrs = instr :: hscope.instructions in
                let hscope = {declarations = decls; instructions = instrs} in
                (hctxt, hscope, decl)

            | RALIndex(t, e) ->
                let (hctxt, hscope, i_hvar) = rexpr_to_hir hctxt hscope e in

                let (hctxt, tmp) = get_tmp_name hctxt in
                let decl = (t, tmp) in
                let decls = decl :: hscope.declarations in
                let instr = Instr(HDynamicIndex(decl, i_hvar, hvar)) in
                let instrs = instr :: hscope.instructions in
                let hscope = {declarations = decls; instructions = instrs} in
                (hctxt, hscope, decl)
            end
        ) (hctxt, hscope, named_hvar) rassign_idx_lvals
      in

      let instr = Instr(HValueAssign(indexed_hvar, HValVar(rhs_hvar))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope)
  end
;;


let rfunc_decl_t_to_hfunc_decl_t {rf_name; rf_params; rf_ret_t} : hfunc_decl_t =
  {
    hf_name = rf_name;
    hf_params = rf_params;
    hf_ret_t = rf_ret_t;
  }
;;


let populate_hctxt_with_func_args hctxt {hf_params; _} : hir_ctxt =
  let (hctxt, _) =
    List.fold_left (
      fun (hctxt, i) (name, t) ->
        let func_vars' = StrMap.add name (t, i) hctxt.func_vars in
        let hctxt = {hctxt with func_vars = func_vars'} in

        (hctxt, (i + 1))
    ) (hctxt, 0) hf_params
  in

  hctxt
;;


let rfunc_def_t_to_hfunc_def_t {rf_decl; rf_stmts} : hfunc_def_t =
  let hf_decl = rfunc_decl_t_to_hfunc_decl_t rf_decl in

  (* Initialize a ctxt with the function arguments. *)
  let hctxt = populate_hctxt_with_func_args default_hir_ctxt hf_decl in

  let (_, hf_scope) =
    List.fold_left (
      fun (hctxt, hf_scope) rstmt ->
        let (hctxt, hf_scope) = rstmt_to_hir hctxt hf_scope rstmt in
        (hctxt, hf_scope)
    ) (hctxt, empty_scope) rf_stmts
  in

  {
    hf_decl = hf_decl;
    hf_scope = hf_scope;
  }
;;
