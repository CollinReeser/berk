open Hir
open Mir
open Rast_typing

(* type hir_variable = rast_t * string
declarations = hir_variable list *)

(* Given a list of variable declarations, generate MIR for allocating stack
space for those variables in the given basic block.

Allocas are sorted to minimize stack usage/minimize padding bytes between
variables, while still respecting alignment.
*)
let hscope_decls_to_mir mir_ctxt bb decls =
  let decls_sorted =
    List.stable_sort (
      fun (lhs_ptr_t, _) (rhs_ptr_t, _) ->
        let lhs_t = unwrap_ptr lhs_ptr_t in
        let rhs_t = unwrap_ptr rhs_ptr_t in
        compare (sizeof_rtype rhs_t) (sizeof_rtype lhs_t)
    ) decls
  in

  let alloca_instrs_rev =
    List.fold_left (
      fun alloca_instrs_rev (t, name) ->
        let ptr_t = t in
        let elem_t = unwrap_ptr ptr_t in

        (* Do not generate allocas for zero-size types. *)
        begin match elem_t with
        | RNil ->
            alloca_instrs_rev

        | _ ->
            let alloca_lval = {t=ptr_t; kind=Tmp; lname=name} in
            let alloca_instr = Alloca(alloca_lval, elem_t) in
            (alloca_instr :: alloca_instrs_rev)
        end
    ) [] decls_sorted
  in

  (* Try to ensure the MIR allocas the variables in roughly their order of
  use. *)
  let alloca_instrs = List.rev alloca_instrs_rev in

  let bb = {bb with instrs = bb.instrs @ alloca_instrs} in
  let mir_ctxt = update_bb mir_ctxt bb in

  (mir_ctxt, bb)
;;

let lval_from_hvar kind (t, lname) =
  {t; kind; lname}
;;

let rval_from_hval hval : rval =
  begin match hval with
  | HValNil     -> Constant(ValNil)
  | HValU8(i)   -> Constant(ValU8(i))
  | HValU16(i)  -> Constant(ValU16(i))
  | HValU32(i)  -> Constant(ValU32(i))
  | HValU64(i)  -> Constant(ValU64(i))
  | HValI8(i)   -> Constant(ValI8(i))
  | HValI16(i)  -> Constant(ValI16(i))
  | HValI32(i)  -> Constant(ValI32(i))
  | HValI64(i)  -> Constant(ValI64(i))
  | HValF32(f)  -> Constant(ValF32(f))
  | HValF64(f)  -> Constant(ValF64(f))
  | HValF128(s) -> Constant(ValF128(s))
  | HValBool(b) -> Constant(ValBool(b))
  | HValStr(s)  -> Constant(ValStr(s))
  | HValFunc(s) -> Constant(ValFunc(s))

  | HValVar(hvar) ->
      let lval = lval_from_hvar Var hvar in
      RVar(lval)
  end
;;

let hir_instr_to_mir mir_ctxt bb instr : (mir_ctxt * bb) =
  begin match instr with
  | HRetVoid ->
      let bb = {bb with instrs = bb.instrs @ [RetVoid]} in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HReturn(ret_var) ->
      let ret_lval = lval_from_hvar Tmp ret_var in

      let bb = {bb with instrs = bb.instrs @ [Ret(ret_lval)]} in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HValueStore(target_var, source_var) ->
      let target_lval = lval_from_hvar Tmp target_var in
      let {t=source_t; _} as source_lval = lval_from_hvar Tmp source_var in

      (* Do not generate a store into a pointer to a zero-size type. *)
      let bb =
        begin match source_t with
        | RNil ->
            bb

        | _ ->
            {bb with instrs = bb.instrs @ [Store(target_lval, source_lval)]}
        end
      in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HValueLoad(result_var, source_var) ->
      let {t=result_t; _} as result_lval = lval_from_hvar Tmp result_var in
      let source_lval = lval_from_hvar Tmp source_var in

      (* Don't generate a load from a pointer to a zero-size type, instead just
      grabbing a placeholder instance of that type. *)
      let bb =
        begin match result_t with
        | RNil ->
            let nil_rval = Constant(ValNil) in
            {bb with instrs = bb.instrs @ [Assign(result_lval, nil_rval)]}

        | _ ->
            {bb with instrs = bb.instrs @ [Load(result_lval, source_lval)]}
        end
      in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HAggregate(result_var, elem_vars) ->
      let result_lval = lval_from_hvar Tmp result_var in

      let elem_lvals = List.map (lval_from_hvar Tmp) elem_vars in

      let bb = {
        bb with instrs = bb.instrs @ [
          ConstructAggregate(result_lval, elem_lvals)
        ]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HAggregateIndex(result_var, idx, aggregate_var) ->
      let result_lval = lval_from_hvar Tmp result_var in
      let aggregate_lval = lval_from_hvar Tmp aggregate_var in

      let bb = {
        bb with instrs = bb.instrs @ [
          FromAggregate(result_lval, idx, aggregate_lval)
        ]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HArgToVar(result_var, _, arg_idx) ->
      let result_lval = lval_from_hvar Tmp result_var in

      let bb = {
        bb with instrs = bb.instrs @ [GetArg(result_lval, arg_idx)]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HValueAssign(result_var, rhs_val) ->
      let result_lval = lval_from_hvar Tmp result_var in
      let rhs_rval = rval_from_hval rhs_val in

      let bb = {
        bb with instrs = bb.instrs @ [Assign(result_lval, rhs_rval)]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HValCast(result_var, op, source_var) ->
      let result_lval = lval_from_hvar Tmp result_var in
      let source_lval = lval_from_hvar Tmp source_var in

      let bb = {
        bb with instrs = bb.instrs @ [Cast(result_lval, op, source_lval)]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HUnOp(result_var, op, rhs_var) ->
      let result_lval = lval_from_hvar Tmp result_var in
      let rhs_lval = lval_from_hvar Tmp rhs_var in

      let bb = {
        bb with instrs = bb.instrs @ [UnOp(result_lval, op, rhs_lval)]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HBinOp(result_var, op, lhs_var, rhs_var) ->
      let result_lval = lval_from_hvar Tmp result_var in
      let lhs_lval = lval_from_hvar Tmp lhs_var in
      let rhs_lval = lval_from_hvar Tmp rhs_var in

      let bb = {
        bb with instrs = bb.instrs @ [
          BinOp(result_lval, op, lhs_lval, rhs_lval)
        ]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HExprInvokeVoid(func_var, arg_vars) ->
      let func_lval = lval_from_hvar Tmp func_var in
      let arg_lvals = List.map (lval_from_hvar Tmp) arg_vars in

      let bb = {
        bb with instrs = bb.instrs @ [CallVoid(func_lval, arg_lvals)]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HExprInvoke(result_var, func_var, arg_vars) ->
      let result_lval = lval_from_hvar Tmp result_var in
      let func_lval = lval_from_hvar Tmp func_var in
      let arg_lvals = List.map (lval_from_hvar Tmp) arg_vars in

      let bb = {
        bb with instrs = bb.instrs @ [Call(result_lval, func_lval, arg_lvals)]
      } in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)

  | HDynamicIndex(result_var, idx_var, ptr_to_arr_var) ->
      let result_lval = lval_from_hvar Tmp result_var in
      let idx_lval = lval_from_hvar Tmp idx_var in
      let ptr_to_arr_lval = lval_from_hvar Tmp ptr_to_arr_var in

      let ptrto_instr =
        PtrTo(
          result_lval, [
            (* Start at "index 0" of this "one-elem array of arrays". *)
            Static(0);
            (* Second index is into the arr-index of the pointed-to array. *)
            Dynamic(idx_lval)
          ],
          ptr_to_arr_lval
        )
      in

      let bb = {bb with instrs = bb.instrs @ [ptrto_instr]} in

      let mir_ctxt = update_bb mir_ctxt bb in
      (mir_ctxt, bb)
  end
;;

let rec hscope_instr_to_mir mir_ctxt bb scope_instr =
  begin match scope_instr with
  | Instr(instr) ->
      hir_instr_to_mir mir_ctxt bb instr

  | Scope({instructions; _}) ->
      let (mir_ctxt, bb) = hscope_instrs_to_mir mir_ctxt bb instructions in

      let mir_ctxt = update_bb mir_ctxt bb in

      (mir_ctxt, bb)

  | CondScope(
      cond_var, {instructions=then_instrs; _}, {instructions=else_instrs; _}
    ) ->
      let cond_lval = lval_from_hvar Tmp cond_var in

      let (mir_ctxt, then_bb_name) = get_bbname mir_ctxt in
      let (mir_ctxt, else_bb_name) = get_bbname mir_ctxt in
      let (mir_ctxt, end_bb_name) = get_bbname mir_ctxt in
      let then_bb = {name=then_bb_name; instrs=[]} in
      let else_bb = {name=else_bb_name; instrs=[]} in
      let end_bb = {name=end_bb_name; instrs=[]} in

      let bb = {
        bb with instrs = bb.instrs @ [CondBr(cond_lval, then_bb, else_bb)]
      } in

      let (mir_ctxt, then_bb) = begin
        let (mir_ctxt, then_bb) =
          hscope_instrs_to_mir mir_ctxt then_bb then_instrs
        in

        (mir_ctxt, {then_bb with instrs = then_bb.instrs @ [Br(end_bb)]})
      end in

      let (mir_ctxt, else_bb) =
        let (mir_ctxt, else_bb) =
          hscope_instrs_to_mir mir_ctxt else_bb else_instrs
        in

        (mir_ctxt, {else_bb with instrs = else_bb.instrs @ [Br(end_bb)]})
      in

      let mir_ctxt = update_bb mir_ctxt bb in
      let mir_ctxt = update_bb mir_ctxt then_bb in
      let mir_ctxt = update_bb mir_ctxt else_bb in
      let mir_ctxt = update_bb mir_ctxt end_bb in

      (mir_ctxt, end_bb)

  | CondLoopScope(
      {instructions=cond_instrs; _}, cond_var, {instructions=then_instrs; _}
    ) ->
      let cond_lval = lval_from_hvar Tmp cond_var in

      let (mir_ctxt, cond_bb_name) = get_bbname mir_ctxt in
      let (mir_ctxt, then_bb_name) = get_bbname mir_ctxt in
      let (mir_ctxt, end_bb_name) = get_bbname mir_ctxt in
      let cond_bb = {name=cond_bb_name; instrs=[]} in
      let then_bb = {name=then_bb_name; instrs=[]} in
      let end_bb = {name=end_bb_name; instrs=[]} in

      let bb = {bb with instrs = bb.instrs @ [Br(cond_bb)]} in

      let (mir_ctxt, cond_bb) =
        let (mir_ctxt, cond_bb) =
          hscope_instrs_to_mir mir_ctxt cond_bb cond_instrs
        in

        (
          mir_ctxt,
          {
            cond_bb with
              instrs = cond_bb.instrs @ [CondBr(cond_lval, then_bb, end_bb)]
          }
        )
      in

      let (mir_ctxt, then_bb) = begin
        let (mir_ctxt, then_bb) =
          hscope_instrs_to_mir mir_ctxt then_bb then_instrs
        in

        (mir_ctxt, {then_bb with instrs = then_bb.instrs @ [Br(cond_bb)]})
      end in

      let mir_ctxt = update_bb mir_ctxt bb in
      let mir_ctxt = update_bb mir_ctxt cond_bb in
      let mir_ctxt = update_bb mir_ctxt then_bb in
      let mir_ctxt = update_bb mir_ctxt end_bb in

      (mir_ctxt, end_bb)
  end


and hscope_instrs_to_mir mir_ctxt bb scope_instrs =
  let (mir_ctxt, bb) =
    List.fold_left (
      fun (mir_ctxt, bb) scope_instr ->
        hscope_instr_to_mir mir_ctxt bb scope_instr
    ) (mir_ctxt, bb) scope_instrs
  in

  (mir_ctxt, bb)
;;

let hfunc_decl_to_mir {hf_name; hf_params; hf_ret_t} =
  let mir_ctxt = {
    f_name = hf_name;
    f_params = hf_params;
    f_ret_rt = hf_ret_t;
    name_gen = 0;
    lvars = StrMap.empty;
    bbs = StrMap.empty
  } in

  mir_ctxt
;;

let hfunc_def_to_mir {hf_decl; hf_scope} =
  (* Setup declaration for the function. *)
  let mir_ctxt = hfunc_decl_to_mir hf_decl in

  (* Collect all internal declarations and move them to the top-level scope. *)
  let toplevel_decl_hfscope = rewrite_hscope_to_only_toplevel_decls hf_scope in

  let bb_entry = {name="entry"; instrs=[]} in

  (* Generate MIR for all variable declarations. We do this because:

  - This simplifies handling of generating the instructions themselves. Simply
  assume any relevant variables already exist, and use them accordingly.

  - This ensures we don't end up with non-optimal codegen like stack allocas
  within loops that can exhaust the stack despite not actually needing a
  separate stack allocation for each run through the loop. *)
  let (mir_ctxt, bb) =
    hscope_decls_to_mir
      mir_ctxt
      bb_entry
      toplevel_decl_hfscope.declarations
  in

  (* Generate MIR for the tree of scoped instructions. *)
  let (mir_ctxt, _) =
    hscope_instrs_to_mir
      mir_ctxt
      bb
      toplevel_decl_hfscope.instructions
  in

  mir_ctxt
;;
