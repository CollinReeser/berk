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
  | HTupleIndex of hir_variable * int * hir_variable

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

  (* The resultant hir_variable is indexing using the middle hir_variable into
  the array in the third hir_variable. *)
  | HIndexExpr of hir_variable * hir_variable * hir_variable

  (* The resultant hir_variable is the variant value construction of the given
  name and the given possibly-zero list of constructor fields. *)
  | HVariantCtorExpr of hir_variable * string * hir_variable list

  (* ??? *)
  | HMatchExpr of hir_variable * (rpattern * hir_instr) list

  (* ??? *)
  (* | HWhileExpr of berk_t * hstmt list * hir_instr * hstmt list *)


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

(*
(* ??? *)
and hassign_idx_lval =
  (* An index into a tuple. *)
  | HALStaticIndex of int
  (* An index into a static or dynamic array. *)
  | HALIndex of hir_instr


(* ??? *)
and hstmt =
  | HDeclStmt of string * berk_t * hir_instr

  | HDeclDefStmt of (string * berk_t) list

  | HAssignStmt of string * hassign_idx_lval list * hir_instr

  | HExprStmt of hir_instr
  | HReturnStmt of hir_instr

  (* A convenience container for when a stmt needs to be rewritten using
  multiple rstmt. *)
  | HStmts of hstmt list
*)


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

  | HTupleIndex(h_var_res, i, h_var_tup) ->
      sprintf "%s = (%s).%d"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_tup)
        i

  | HDynamicIndex(h_var_res, h_var_idx, h_var_arr) ->
      sprintf "%s = DYN IDX (%s)[%s]"
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

  | HValRawArray(_) ->
      failwith "fmt_hir_instr(HValRawArray): Unimplemented"

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

  | HIndexExpr(h_var_res, h_var_idx, h_var_arr) ->
      sprintf "%s = IDX (%s)[%s]"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_arr)
        (fmt_hir_variable h_var_idx)

  | HVariantCtorExpr(h_var_res, ctor_name, h_var_elems) ->
      let elem_fmt_xs = List.map fmt_hir_variable h_var_elems in
      let elems_fmt = fmt_join_strs ", " elem_fmt_xs in
      sprintf "%s = %s(%s)"
        (fmt_hir_variable h_var_res)
        ctor_name
        elems_fmt

  | _ -> failwith "fmt_hir_instr(): Unimplemented"
  end
;;


(*
let fmt_hassign_idx_lval hassign_idx_lval : string =
  let open Printf in
  begin match hassign_idx_lval with
  | HALStaticIndex(i) -> sprintf ".%d" i
  | HALIndex(_) -> failwith "Unimplemented"
  end
;;
*)



(*
let fmt_hstmt hstmt : string =
  let open Printf in
  begin match hstmt with
  | HDeclStmt(name, t, * hir_instr
  | HDeclDefStmt of (string * berk_t) list
  | HAssignStmt of string * hassign_idx_lval list * hir_instr
  | HExprStmt of hir_instr
  | HReturnStmt of hir_instr
  | HStmts of hstmt list
  end
;;
*)


let rec fmt_hir_scope ?(ind = "") {declarations; instructions} : string =
  let declaration_fmt_xs = List.map fmt_hir_variable declarations in
  let declaration_fmt_prefix_xs =
    List.map (
      Printf.sprintf "%s%s" (ind ^ "   ")
    ) declaration_fmt_xs
  in
  let declaration_fmt_prefix_xs_rev = List.rev declaration_fmt_prefix_xs in
  let declarations_fmt = fmt_join_strs "\n" declaration_fmt_prefix_xs_rev in

  let instruction_fmt_xs =
    List.map (
      fmt_hir_scope_instr ~ind:(ind ^ "   ")
    ) instructions in
  let instruction_fmt_xs_rev = List.rev instruction_fmt_xs in
  let instructions_fmt = fmt_join_strs "\n" instruction_fmt_xs_rev in

  Printf.sprintf (
    "%sscope {\n" ^^
    "%s declarations:\n" ^^
    "%s\n" ^^
    "%s instructions:\n" ^^
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
        (fmt_hir_scope ~ind:(ind ^ "   ") h_scope_then)
        ind
        ind
        (fmt_hir_scope ~ind:(ind ^ "   ") h_scope_else)
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
        (fmt_hir_scope ~ind:(ind ^ "   ") h_scope_cond)
        (ind ^ "   ") (fmt_hir_variable h_var_cond)
        ind
        (fmt_hir_scope ~ind:(ind ^ "   ") h_scope_body)
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
    (fmt_hir_scope ~ind:"   " hf_scope)
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

  | RValCast(_, _, _) -> failwith "rexpr_to_hir(RValCast): Unimplemented"
  | RUnOp(_, _, _) -> failwith "rexpr_to_hir(RUnOp): Unimplemented"

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
      let instr = Instr(HTupleIndex(decl, idx, tup_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RVariantCtorExpr(variant_t, ctor_name, ctor_args) ->
      (* Variant index, a static integer. *)
      let ctor_idx = get_tag_index_by_variant_ctor variant_t ctor_name in

      let idx_t = U8 in

      (* Generate HIR for the variant constructor index. *)
      let (hctxt, hscope, ctor_idx_var) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (idx_t, tmp) in
        let decls = decl :: hscope.declarations in
        let instr = Instr(HValueAssign(decl, HValU8(ctor_idx))) in
        let instrs = instr :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (* The (reversed) list of types that make up this aggregate, starting with
      the variant constructor index. If there are no fields for this
      constructor, then this is also the entirety of the aggregate type. *)
      let agg_ts_rev = [idx_t] in

      (* Generate HIR for the variant constructor fields, if any. *)
      let ((hctxt, hscope, agg_ts_rev), ctor_arg_vars) =
        List.fold_left_map (
          fun (hctxt, hscope, agg_ts_rev) ctor_arg ->
            let elem_t = rexpr_type ctor_arg in
            let agg_ts_rev = elem_t :: agg_ts_rev in

            let (hctxt, hscope, ctor_arg_var) =
              rexpr_to_hir hctxt hscope ctor_arg
            in
            ((hctxt, hscope, agg_ts_rev), ctor_arg_var)
        ) (hctxt, hscope, agg_ts_rev) ctor_args
      in

      (* Our list of aggregate element types was generated in reverse order. *)
      let agg_ts = List.rev agg_ts_rev in

      (* The variant is represented internally as a tuple of the ctor index
      and its fields. *)
      let agg_t = Tuple(agg_ts) in

      (* The elements of the variant aggregate are the ctor idx and any fields
      it may have had. *)
      let agg_elems = ctor_idx_var :: ctor_arg_vars in

      (* Generate HIR for the final aggregate representation of the variant. *)
      let (hctxt, hscope, variant_var) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (agg_t, tmp) in
        let decls = decl :: hscope.declarations in
        let instr = Instr(HAggregate(decl, agg_elems)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (hctxt, hscope, variant_var)

  (* | RWhileExpr of berk_t * rstmt list * rexpr * rstmt list *)
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

  | RIndexExpr(_, _, _) ->
      failwith "rexpr_to_hir(RIndexExpr): Unimplemented"
  | RArrayExpr(_, _) ->
      failwith "rexpr_to_hir(RArrayExpr): Unimplemented"
  | RValRawArray(_) ->
      failwith "rexpr_to_hir(RValRawArray): Unimplemented"
  | RExprInvoke(_, _, _) ->
      failwith "rexpr_to_hir(RExprInvoke): Unimplemented"
  | RMatchExpr(_, _, _) ->
      failwith "rexpr_to_hir(RMatchExpr): Unimplemented"
  end


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
  | RDeclStmt(name, t, rexpr) ->
      (* The declared type is not used. We might be doing some sort of a
      representational transformation (like a variant becoming a bare tuple)
      and want to use the resultant transformation type, not the high-level
      original type. *)
      t |> ignore ;

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
                let instr = Instr(HTupleIndex(decl, i, hvar)) in
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
