open Ir
open Rast
open Typing
open Utility

module StrMap = Map.Make(String)

type hir_variable = berk_t * string

type hir_value =
| HValNil
| HValU8 of int | HValU16 of int | HValU32 of int | HValU64 of int
| HValI8 of int | HValI16 of int | HValI32 of int | HValI64 of int
| HValF32 of float | HValF64 of float
| HValF128 of string
| HValBool of bool
| HValStr of string
| HValFunc of string
| HValVar of hir_variable

(* The left-most hir_variable is the assigned-to value that holds the result of
the instruction. The remaining hir_variables are the argument(s) to the
instruction. *)
type hir_instr =
  (* Return from the function using the given variable. *)
  | HReturn of hir_variable

  (* The LHS is a variable representing an aggregation of other variables
  provided by the RHS. *)
  | HAggregate of hir_variable * hir_variable list

  (* "Tuple-index" into the RHS variable with the given constant integer index,
  yielding the value in the resultant LHS variable. ie: `tmp = tup.3;` *)
  | HAggregateIndex of hir_variable * int * hir_variable

  (* LHS is resultant variable. Middle is indexing variable. RHS is indexed
  variable. *)
  | HDynamicIndex of hir_variable * hir_variable * hir_variable

  (* LHS is a new variable that represents the function argument indicated by
  the given name and func-arg-index. *)
  | HArgToVar of hir_variable * string * int

  (* Assign to a resultant variable a given "value". *)
  | HValueAssign of hir_variable * hir_value

  (* Create a raw array with the type of the given resultant variable. *)
  | HValRawArray of hir_variable

  (* Perform an operation on the target variable(s), producing the resultant
  variable. *)
  | HValCast of hir_variable * cast_op * hir_variable
  | HUnOp of hir_variable * un_op * hir_variable
  | HBinOp of hir_variable * bin_op * hir_variable * hir_variable

  (* The resultant variable is the result of invoking the function in the middle
  hir_variable on the argument list. *)
  | HExprInvoke of hir_variable * hir_variable * hir_variable list

  (* The resultant hir_variable is an array-expr composed of the hir_variable
  list. *)
  | HArrayExpr of hir_variable * hir_variable list

  (* ??? *)
  | HMatchExpr of hir_variable * (rpattern * hir_instr) list



(* ??? *)
and rpattern =
  | HWild of berk_t
  | HVarBind of berk_t * string
  | HPNil
  | HPBool of bool
  | HPIntLit of berk_t * int
  | HPIntFrom of berk_t * int
  | HPIntUntil of berk_t * int
  | HPIntRange of berk_t * int * int
  | HPTuple of berk_t * rpattern list
  | HCtor of berk_t * string * rpattern list
  | HPatternAs of berk_t * rpattern * string


type hir_scope = {
  declarations: hir_variable list;
  instructions: hir_scope_instr list;
}

and hir_scope_instr =
  (* Basic instruction *)
  | Instr of hir_instr
  (* Basic scope, unconditional evaluation and no looping. *)
  | Scope of hir_scope
  (* Conditional variable, then instruction list, else alternate scope *)
  | CondScope of hir_variable * hir_scope * hir_scope
  (* The first scope is the evaluation of the condition. The variable is the
  actual decision of whether to (re-)run the body of the loop. The second
  scope is the body of the loop itself. *)
  | CondLoopScope of hir_scope * hir_variable * hir_scope


(* ??? *)
and hf_param = (string * berk_t)


(* ??? *)
type hfunc_decl_t = {
  hf_name: string;
  hf_params: hf_param list;
  hf_ret_t: berk_t;
}


(* ??? *)
type hfunc_def_t = {
  hf_decl: hfunc_decl_t;
  hf_scope: hir_scope;
}


let hir_variable_type (t, _) = t ;;


let empty_scope : hir_scope = {
  declarations = [];
  instructions = [];
}


let fmt_hir_variable (t, name) : string =
  Printf.sprintf "%s: %s" name (fmt_type t)
;;

let fmt_hir_value hir_value : string =
  let open Printf in
  begin match hir_value with
  | HValNil ->
      sprintf "nil"
  | HValU8(i) | HValU16(i) | HValU32(i) | HValU64(i)
  | HValI8(i) | HValI16(i) | HValI32(i) | HValI64(i) ->
      sprintf "%d" i
  | HValF32(f) | HValF64(f) ->
      sprintf "%f" f
  | HValF128(f_str) ->
      sprintf "%s" f_str
  | HValBool(b) ->
      sprintf "%b" b
  | HValStr(str) ->
      sprintf "\"%s\"" (String.escaped str)
  | HValFunc(func_name) ->
      sprintf "fn<%s>" func_name
  | HValVar(hir_variable) ->
      fmt_hir_variable hir_variable
  end
;;

let fmt_hir_instr hir_instr : string =
  let open Printf in
  begin match hir_instr with
  | HReturn(h_var_res) ->
      sprintf "return %s" (fmt_hir_variable h_var_res)

  | HAggregate(h_var_res, h_var_elems) ->
      let elem_fmt_xs = List.map fmt_hir_variable h_var_elems in
      let elems_fmt = fmt_join_strs ", " elem_fmt_xs in
      sprintf "%s = (%s)"
        (fmt_hir_variable h_var_res)
        elems_fmt

  | HAggregateIndex(h_var_res, i, h_var_tup) ->
      sprintf "%s = (%s).%d"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_tup)
        i

  | HDynamicIndex(h_var_res, h_var_idx, h_var_arr) ->
      sprintf "%s = IDX (%s)[%s]"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_arr)
        (fmt_hir_variable h_var_idx)

  | HArgToVar(h_var_res, func_arg_name, func_arg_idx) ->
      sprintf "%s = arg(%d) # %s"
        (fmt_hir_variable h_var_res)
        func_arg_idx
        func_arg_name

  | HValueAssign(h_var_res, h_val) ->
      sprintf "%s = %s"
        (fmt_hir_variable h_var_res)
        (fmt_hir_value h_val)

  | HValRawArray(h_var_res) ->
      sprintf "ARRAY where %s"
        (fmt_hir_variable h_var_res)

  | HValCast(h_var_res, cast_op, h_var_orig) ->
      sprintf "%s = %s (%s)"
        (fmt_hir_variable h_var_res)
        (fmt_cast_op cast_op)
        (fmt_hir_variable h_var_orig)

  | HUnOp(h_var_res, un_op, h_var_orig) ->
      sprintf "%s = %s (%s)"
        (fmt_hir_variable h_var_res)
        (fmt_un_op un_op)
        (fmt_hir_variable h_var_orig)

  | HBinOp(h_var_res, bin_op, h_var_lhs, h_var_rhs) ->
      sprintf "%s = (%s) %s (%s)"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_lhs)
        (fmt_bin_op bin_op)
        (fmt_hir_variable h_var_rhs)

  | HExprInvoke(h_var_res, h_var_func, h_var_args) ->
      let arg_fmt_xs = List.map fmt_hir_variable h_var_args in
      let args_fmt = fmt_join_strs ", " arg_fmt_xs in

      sprintf "%s = (%s)(%s)"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_func)
        args_fmt

  | HArrayExpr(h_var_res, h_var_elems) ->
      let elem_fmt_xs = List.map fmt_hir_variable h_var_elems in
      let elems_fmt = fmt_join_strs ", " elem_fmt_xs in
      sprintf "%s = [%s]"
        (fmt_hir_variable h_var_res)
        elems_fmt

  | _ -> failwith "fmt_hir_instr(): Unimplemented"
  end
;;


let rec fmt_hir_scope ?(ind = "") {declarations; instructions} : string =
  let declaration_fmt_xs = List.map fmt_hir_variable declarations in
  let declaration_fmt_prefix_xs =
    List.map (
      Printf.sprintf "%s%s" (ind ^ "    ")
    ) declaration_fmt_xs
  in
  let declaration_fmt_prefix_xs_rev = List.rev declaration_fmt_prefix_xs in
  let declarations_fmt = fmt_join_strs "\n" declaration_fmt_prefix_xs_rev in

  let instruction_fmt_xs =
    List.map (
      fmt_hir_scope_instr ~ind:(ind ^ "    ")
    ) instructions in
  let instruction_fmt_xs_rev = List.rev instruction_fmt_xs in
  let instructions_fmt = fmt_join_strs "\n" instruction_fmt_xs_rev in

  Printf.sprintf (
    "%sscope {\n" ^^
    "%s  declarations:\n" ^^
    "%s\n" ^^
    "%s  instructions:\n" ^^
    "%s\n" ^^
    "%s}"
  )
    ind
    ind
    declarations_fmt
    ind
    instructions_fmt
    ind


and fmt_hir_scope_instr ?(ind = "") hir_scope_instr : string =
  let open Printf in
  begin match hir_scope_instr with
  | Instr(h_instr) ->
      sprintf "%s%s"
        ind (fmt_hir_instr h_instr)

  | Scope(h_scope) ->
      fmt_hir_scope ~ind:ind h_scope

  | CondScope(h_var_cond, h_scope_then, h_scope_else) ->
      sprintf (
        "%sif (%s) {\n" ^^
        "%s\n" ^^
        "%s}\n" ^^
        "%selse {\n" ^^
        "%s\n" ^^
        "%s}"
      )
        ind (fmt_hir_variable h_var_cond)
        (fmt_hir_scope ~ind:(ind ^ "  ") h_scope_then)
        ind
        ind
        (fmt_hir_scope ~ind:(ind ^ "  ") h_scope_else)
        ind

  | CondLoopScope(h_scope_cond, h_var_cond, h_scope_body) ->
      sprintf (
        "%swhile (\n" ^^
        "%s\n" ^^
        "%s%s\n" ^^
        "%s) {\n" ^^
        "%s\n" ^^
        "%s}"
      )
        ind
        (fmt_hir_scope ~ind:(ind ^ "  ") h_scope_cond)
        (ind ^ "    ") (fmt_hir_variable h_var_cond)
        ind
        (fmt_hir_scope ~ind:(ind ^ "  ") h_scope_body)
        ind
  end
;;


let fmt_hf_param (name, t) : string =
  Printf.sprintf "%s: %s" name (fmt_type t)
;;


let fmt_hfunc_decl_t {hf_name; hf_params; hf_ret_t} : string =
  let hf_param_fmt_xs = List.map fmt_hf_param hf_params in
  let hf_params_fmt = fmt_join_strs ", " hf_param_fmt_xs in

  Printf.sprintf "fn %s(%s): %s"
    hf_name
    hf_params_fmt
    (fmt_type hf_ret_t)
;;


let fmt_hfunc_def_t {hf_decl; hf_scope} =
  Printf.sprintf (
    "%s {\n" ^^
    "%s\n" ^^
    "}\n"
  )
    (fmt_hfunc_decl_t hf_decl)
    (fmt_hir_scope ~ind:"    " hf_scope)
;;


type hir_ctxt = {
  func_vars: (berk_t * int) StrMap.t;
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
      let decl = (Nil, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValNil)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValBool(b) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (Bool, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValBool(b))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValStr(s) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (String, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValStr(s))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF32(f) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (F32, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValF32(f))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF64(f) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (F64, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValF64(f))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF128(s) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (F128, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValF128(s))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValInt(t, x) ->
      let hval =
        begin match t with
        | U8 ->  HValU8 (x)
        | U16 -> HValU16(x)
        | U32 -> HValU32(x)
        | U64 -> HValU64(x)
        | I8 ->  HValI8 (x)
        | I16 -> HValI16(x)
        | I32 -> HValI32(x)
        | I64 -> HValI64(x)
        | _ ->
            failwith (
              Printf.sprintf "Nonsense type [%s] for int [%d] convert to HIR."
                (fmt_type t) x
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

  | RVariantCtorExpr(variant_t, ctor_name, ctor_rexprs) ->
      (* Generate the variant value as though it were a tuple of the constructor
      field args prefixed with the constructor index. *)

      (* Variant index, a static integer. *)
      let ctor_idx_t = U8 in
      let ctor_idx = get_tag_index_by_variant_ctor variant_t ctor_name in
      let ctor_idx_rexpr = RValInt(ctor_idx_t, ctor_idx) in

      let ctor_field_ts = List.map rexpr_type ctor_rexprs in
      let tuple_analogue_t = Tuple(ctor_idx_t :: ctor_field_ts) in

      let tuple_analogue_rexprs = ctor_idx_rexpr :: ctor_rexprs in

      let variant_tuple_analogue_rexpr =
        RTupleExpr(tuple_analogue_t, tuple_analogue_rexprs)
      in

      (* The variant has been equivalently described as a tuple expression, so
      generate HIR for that equivalent form instead.

      TODO: Depending on where else it might make sense to want to know that
      a value is a variant in the HIR, we may just choose to rewrite variant
      expressions (and variant match-patterns, etc) as tuple expressions in
      the RAST instead, simplifying the HIR (and consequently the MIR, etc). *)
      rexpr_to_hir hctxt hscope variant_tuple_analogue_rexpr

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
      let decl = (Nil, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValNil)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RValRawArray(t) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValRawArray(decl)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

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

  | RExprInvoke(t, func_rexpr, arg_rexprs) ->
      let (hctxt, hscope, hfunc) = rexpr_to_hir hctxt hscope func_rexpr in

      let ((hctxt, hscope), hargs) =
        List.fold_left_map (
          fun (hctxt, hscope) rexpr ->
            let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in
            ((hctxt, hscope), hvar)
        ) (hctxt, hscope) arg_rexprs
      in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HExprInvoke(decl, hfunc, hargs)) in
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
      let decl = (Bool, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HBinOp(decl, Eq, hmatchee, hbool)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, decl)

  | RPTuple(tup_t, patts) ->
      (* Declare a boolean, defaulting to true but assignable to false in the
      case that any of the tuple elems don't match the pattern. *)
      let (hctxt, hscope, hoverall_bool) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (Bool, tmp) in
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

  | _ ->
    failwith (
      Printf.sprintf
        "rpattern_to_hir, patt unimplemented: %s"
        (fmt_rpattern patt)
    )
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
      (* NOTE: The declared type is not used. We might be doing some sort of a
      representational transformation (like a variant becoming a bare tuple)
      and want to use the resultant transformation type, not the high-level
      original type. *)

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
      let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in

      let instr = Instr(HReturn(hvar)) in
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
