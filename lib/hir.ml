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
  (* Return void. *)
  | HRetVoid

  (* Return from the function using the given variable. *)
  | HReturn of hir_variable

  (* Store a value onto the stack at the given variable location. *)
  | HValueStore of hir_variable * hir_variable

  (* Load a value from the stack at the given variable location. *)
  | HValueLoad of hir_variable * hir_variable

  (* The LHS is a variable representing an aggregation of other variables
  provided by the RHS. *)
  | HAggregate of hir_variable * hir_variable list

  (* LHS is resultant variable, that is a _pointer to_ the indexed element (that
  would then still need to be loaded). Middle is one or more indexing variables.
  RHS is a pointer to an indexable value. *)
  | HDynamicIndex of hir_variable * hir_variable list * hir_variable

  (* LHS is a new variable that represents the function argument indicated by
  the given name and func-arg-index. *)
  | HArgToVar of hir_variable * string * int

  (* Assign to a resultant variable a given "value". *)
  | HValueAssign of hir_variable * hir_value

  (* Perform an operation on the target variable(s), producing the resultant
  variable. *)
  | HValCast of hir_variable * cast_op * hir_variable
  | HUnOp of hir_variable * un_op * hir_variable
  | HBinOp of hir_variable * rbin_op * hir_variable * hir_variable

  (* The resultant variable is the result of invoking the function in the middle
  hir_variable on the argument list. *)
  | HExprInvoke of hir_variable * hir_variable * hir_variable list

  (* As HExprInvoke but there is no resultant hvar. *)
  | HExprInvokeVoid of hir_variable * hir_variable list


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


type h_param = (string * rast_t)


type hfunc_decl_t = {
  hf_name: string;
  hf_params: h_param list;
  hf_ret_t: rast_t;
}

type hgenerator_decl_t = {
  hg_name: string;
  hg_params: h_param list;
  hg_yield_t: rast_t;
  hg_ret_t: rast_t;
}

type hfunc_def_t = {
  hf_decl: hfunc_decl_t;
  hf_scope: hir_scope;
}

type hgenerator_def_t = {
  hg_decl: hgenerator_decl_t;
  hg_scope: hir_scope;
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
  | HRetVoid ->
      sprintf "return (void)"

  | HReturn(h_var_res) ->
      sprintf "return %s" (fmt_hir_variable h_var_res)

  | HValueStore(h_var_target, h_var_source) ->
      sprintf "%s <-[store]<- %s"
        (fmt_hir_variable h_var_target)
        (fmt_hir_variable h_var_source)

  | HValueLoad(h_var_res, h_var_source) ->
      sprintf "%s <-[load.]<- %s"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_source)

  | HAggregate(h_var_res, h_var_elems) ->
      let elem_fmt_xs = List.map fmt_hir_variable h_var_elems in
      let elems_fmt = fmt_join_strs ", " elem_fmt_xs in
      sprintf "%s = (%s)"
        (fmt_hir_variable h_var_res)
        elems_fmt

  | HDynamicIndex(h_var_res, h_var_idxs, h_var_arr) ->
      sprintf "%s = IDX (%s)[%s]"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_arr)
        (fmt_join_strs ", " (List.map fmt_hir_variable h_var_idxs))

  | HArgToVar(h_var_res, func_arg_name, func_arg_idx) ->
      sprintf "%s = arg(%d) # %s"
        (fmt_hir_variable h_var_res)
        func_arg_idx
        func_arg_name

  | HValueAssign(h_var_res, h_val) ->
      sprintf "%s = %s"
        (fmt_hir_variable h_var_res)
        (fmt_hir_value h_val)

  | HValCast(h_var_res, cast_op, h_var_orig) ->
      let target_t = hir_variable_type h_var_res in
      sprintf "%s = %s (%s) -> %s"
        (fmt_hir_variable h_var_res)
        (fmt_cast_op cast_op)
        (fmt_hir_variable h_var_orig)
        (fmt_rtype target_t)

  | HUnOp(h_var_res, un_op, h_var_orig) ->
      sprintf "%s = %s (%s)"
        (fmt_hir_variable h_var_res)
        (fmt_un_op un_op)
        (fmt_hir_variable h_var_orig)

  | HBinOp(h_var_res, bin_op, h_var_lhs, h_var_rhs) ->
      sprintf "%s = (%s) %s (%s)"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_lhs)
        (fmt_rbin_op bin_op)
        (fmt_hir_variable h_var_rhs)

  | HExprInvoke(h_var_res, h_var_func, h_var_args) ->
      let arg_fmt_xs = List.map fmt_hir_variable h_var_args in
      let args_fmt = fmt_join_strs ", " arg_fmt_xs in

      sprintf "%s = (%s)(%s)"
        (fmt_hir_variable h_var_res)
        (fmt_hir_variable h_var_func)
        args_fmt

  | HExprInvokeVoid(h_var_func, h_var_args) ->
      let arg_fmt_xs = List.map fmt_hir_variable h_var_args in
      let args_fmt = fmt_join_strs ", " arg_fmt_xs in

      sprintf "(void) = (%s)(%s)"
        (fmt_hir_variable h_var_func)
        args_fmt
  end
;;


let rec fmt_hir_scope ?(ind = "") {declarations; instructions} : string =
  let declaration_fmt_xs = List.map fmt_hir_variable declarations in
  let declaration_fmt_prefix_xs =
    List.map (
      Printf.sprintf "%s%s" (ind ^ "    ")
    ) declaration_fmt_xs
  in
  let declarations_fmt = fmt_join_strs "\n" declaration_fmt_prefix_xs in

  let instruction_fmt_xs =
    List.map (
      fmt_hir_scope_instr ~ind:(ind ^ "    ")
    ) instructions in
  let instructions_fmt = fmt_join_strs "\n" instruction_fmt_xs in

  if (List.length declarations > 0) && (List.length instructions > 0) then
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
  else if (List.length declarations == 0) && (List.length instructions > 0) then
    Printf.sprintf (
      "%sscope {\n" ^^
      "%s  instructions:\n" ^^
      "%s\n" ^^
      "%s}"
    )
      ind
      ind
      instructions_fmt
      ind
  else if (List.length declarations > 0) && (List.length instructions == 0) then
    Printf.sprintf (
      "%sscope {\n" ^^
      "%s  declarations:\n" ^^
      "%s\n" ^^
      "%s}"
    )
      ind
      ind
      declarations_fmt
      ind
  else
    Printf.sprintf (
      "%sscope {}\n"
    )
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
        "%scond (%s)\n" ^^
        "%s) loop body {\n" ^^
        "%s\n" ^^
        "%s}"
      )
        ind
        (fmt_hir_scope ~ind:(ind ^ "  ") h_scope_cond)
        (ind ^ "  ") (fmt_hir_variable h_var_cond)
        ind
        (fmt_hir_scope ~ind:(ind ^ "  ") h_scope_body)
        ind
  end
;;


let fmt_hf_param (name, t) : string =
  Printf.sprintf "%s: %s" name (fmt_rtype t)
;;


let fmt_hf_params hf_params : string =
  let hf_param_fmt_xs = List.map fmt_hf_param hf_params in
  let hf_params_fmt = fmt_join_strs ", " hf_param_fmt_xs in
  hf_params_fmt
;;


let fmt_hfunc_decl_t {hf_name; hf_params; hf_ret_t} : string =
  Printf.sprintf "fn %s(%s): %s"
    hf_name
    (fmt_hf_params hf_params)
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


let fmt_hgenerator_decl_t {hg_name; hg_params; hg_yield_t; hg_ret_t} : string =
  Printf.sprintf "fn %s(%s) yield %s : %s"
    hg_name
    (fmt_hf_params hg_params)
    (fmt_rtype hg_yield_t)
    (fmt_rtype hg_ret_t)
;;


let fmt_hgenerator_def_t {hg_decl; hg_scope} =
  Printf.sprintf (
    "%s {\n" ^^
    "%s\n" ^^
    "}\n"
  )
    (fmt_hgenerator_decl_t hg_decl)
    (fmt_hir_scope ~ind:"    " hg_scope)
;;


(* The declarations and instructions in an HIR scope are populated in reverse.
This function recursively fixes the contents of the given scope so that they're
un-reversed. *)
let rec unreverse_hscope_decls_instrs hscope =
  let rec _reverse_hscope_instrs instrs instrs_rev =
    begin match instrs with
    | [] ->
        instrs_rev

    | (Instr(_) as instr) :: rest ->
        _reverse_hscope_instrs rest (instr :: instrs_rev)

    | Scope(inner_scope) :: rest ->
        let reversed_inner_scope = unreverse_hscope_decls_instrs inner_scope in
        let reversed_scope = Scope(reversed_inner_scope) in
        _reverse_hscope_instrs rest (reversed_scope :: instrs_rev)

    | CondScope(hvar, then_scope, else_scope) :: rest ->
        let reversed_then_scope = unreverse_hscope_decls_instrs then_scope in
        let reversed_else_scope = unreverse_hscope_decls_instrs else_scope in
        let reversed_scope =
          CondScope(hvar, reversed_then_scope, reversed_else_scope)
        in
        _reverse_hscope_instrs rest (reversed_scope :: instrs_rev)

    | CondLoopScope(cond_scope, hvar, body_scope) :: rest ->
        let reversed_cond_scope = unreverse_hscope_decls_instrs cond_scope in
        let reversed_body_scope = unreverse_hscope_decls_instrs body_scope in
        let reversed_scope =
          CondLoopScope(reversed_cond_scope, hvar, reversed_body_scope)
        in
        _reverse_hscope_instrs rest (reversed_scope :: instrs_rev)
    end
  in

  let decls_rev = List.rev hscope.declarations in
  let instrs_rev = _reverse_hscope_instrs hscope.instructions [] in

  {declarations=decls_rev; instructions=instrs_rev}
;;


(* Given an hir_scope that may have some arbitrary tree of internal subscopes,
rewrite the scope tree so that all declarations within the tree are moved to the
top-level scope, leaving all sub-scopes with zero declarations. *)
let rewrite_hscope_to_only_toplevel_decls hscope =
  (* Given an hir_scope_instr, yield the full list of all declarations made
  within any child scopes, and a version of that instruction with all of those
declarations stripped. *)
  let rec _strip_instruction
    scope_instr : (hir_variable list * hir_scope_instr)
  =
    begin match scope_instr with
    | Instr(instr) ->
        ([], Instr(instr))

    | Scope(inner_scope) ->
        let (inner_decls, inner_scope_stripped) = _strip_scope inner_scope in
        (
          inner_decls,
          Scope(inner_scope_stripped)
        )

    | CondScope(hvar, then_scope, else_scope) ->
        let (then_decls, then_scope_stripped) = _strip_scope then_scope in
        let (else_decls, else_scope_stripped) = _strip_scope else_scope in
        (
          then_decls @ else_decls,
          CondScope(hvar, then_scope_stripped, else_scope_stripped)
        )

    | CondLoopScope(eval_scope, hvar, body_scope) ->
        let (eval_decls, eval_scope_stripped) = _strip_scope eval_scope in
        let (body_decls, body_scope_stripped) = _strip_scope body_scope in
        (
          eval_decls @ body_decls,
          CondLoopScope(eval_scope_stripped, hvar, body_scope_stripped)
        )
    end

  (* Take an hir_scope, and return that scope with both its own declarations
  pulled out, and any declarations in child scopes also pulled out, returning
  the stripped declarations as a separate list, and the stripped version of the
  scope-tree itself. *)
  and _strip_scope
    ({declarations; instructions} : hir_scope) :
    (hir_variable list * hir_scope)
  =
    let (decls_inner, instrs_stripped) =
      List.fold_left (
        fun (decls_acc, instrs_stripped_acc) instr ->
          let (decls, instr_stripped) = _strip_instruction instr in
          (
            decls_acc @ decls,
            instrs_stripped_acc @ [instr_stripped]
          )
      ) ([], []) instructions
    in

    (
      declarations @ decls_inner,
      {
        declarations = [];
        instructions = instrs_stripped
      }
    )
  in

  let (all_decls, {instructions=instrs_stripped; _}) = _strip_scope hscope in

  {
    declarations = all_decls;
    instructions = instrs_stripped
  }
;;
