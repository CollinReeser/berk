open Ir
open Rast_typing
open Utility

module StrMap = Map.Make(String)

type hir_variable = rast_t * string

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


and rpattern =
  | HWild of rast_t
  | HVarBind of rast_t * string
  | HPNil
  | HPBool of bool
  | HPIntLit of rast_t * int
  | HPIntFrom of rast_t * int
  | HPIntUntil of rast_t * int
  | HPIntRange of rast_t * int * int
  | HPTuple of rast_t * rpattern list
  (* Reinterpret the matchee as the given type, and then apply the given
  pattern. *)
  | HPCastThen of rast_t * cast_op * rpattern
  (* Match the matchee against the given pattern, but also bind a variable of
  the given name to the matchee. *)
  | HPatternAs of rast_t * rpattern * string


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


type hf_param = (string * rast_t)


type hfunc_decl_t = {
  hf_name: string;
  hf_params: hf_param list;
  hf_ret_t: rast_t;
}


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
  Printf.sprintf "%s: %s" name (fmt_rtype t)
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
  Printf.sprintf "%s: %s" name (fmt_rtype t)
;;


let fmt_hfunc_decl_t {hf_name; hf_params; hf_ret_t} : string =
  let hf_param_fmt_xs = List.map fmt_hf_param hf_params in
  let hf_params_fmt = fmt_join_strs ", " hf_param_fmt_xs in

  Printf.sprintf "fn %s(%s): %s"
    hf_name
    hf_params_fmt
    (fmt_rtype hf_ret_t)
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
