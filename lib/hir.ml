open Ir
open Rast
open Typing

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

type hir_ctxt = {
  seen_vars: hir_variable StrMap.t;
  tmp_counter: int;
}

(* The left-most hir_variable is the assigned-to value that holds the result of
the instruction. The remaining hir_variables are the argument(s) to the
instruction. *)
type hir_instr =
  | HReturn of hir_variable

  (* "Tuple-index" into the RHS variable with the given constant integer index,
  yielding the value in the resultant LHS variable. ie: `tmp = tup.3;` *)
  | HTupleIndex of hir_variable * int * hir_variable

  (* LHS is resultant variable. Middle is indexing variable. RHS is indexed
  variable. *)
  | HDynamicIndex of hir_variable * hir_variable * hir_variable

  | HValueAssign of hir_variable * hir_value

  (* Create a raw array with the type of the given resultant variable. *)
  | HValRawArray of hir_variable

  (* Perform an operation on the target variable(s), producting the resultant
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

  (* The resultant hir_variable is the static index into the target tuple expr
  hir_variable. *)
  | HTupleIndexExpr of hir_variable * int * hir_variable

  (* The resultant hir_variable is the tuple of the given hir_variables. *)
  | HTupleExpr of hir_variable * hir_variable list

  (* The resultant hir_variable is the variant value construction of the given
  name and the given possibly-zero list of constructor fields. *)
  | HVariantCtorExpr of hir_variable * string * hir_variable list

  (* ??? *)
  | HMatchExpr of hir_variable * (rpattern * hir_instr) list

  (* ??? *)
  | HWhileExpr of berk_t * hstmt list * hir_instr * hstmt list


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


(* ??? *)
and rassign_idx_lval =
  (* An index into a tuple. *)
  | HALStaticIndex of int
  (* An index into a static or dynamic array. *)
  | HALIndex of hir_instr


(* ??? *)
and hstmt =
  | HDeclStmt of string * berk_t * hir_instr

  | HDeclDefStmt of (string * berk_t) list

  | HAssignStmt of string * rassign_idx_lval list * hir_instr

  | HExprStmt of hir_instr
  | HReturnStmt of hir_instr

  (* A convenience container for when a stmt needs to be rewritten using
  multiple rstmt. *)
  | HStmts of hstmt list


(* ??? *)
and hf_param = (string * berk_t)


(* ??? *)
and hfunc_decl_t = {
  hf_name: string;
  hf_params: hf_param list;
  hf_ret_t: berk_t;
}


(* ??? *)
and hfunc_def_t = {
  hf_decl: hfunc_decl_t;
  hf_stmts: hstmt list;
}
;;


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
  (* Conditional  variable for whether to run the body *)
  | CondLoop of hir_variable * hir_scope


let empty_scope : hir_scope = {
  declarations = [];
  instructions = [];
}


let default_hir_ctxt : hir_ctxt = {
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
      let decl = (t, name) in
      (hctxt, hscope, decl)

  | RValFunc(_, _) -> failwith "Unimplemented"

  | RValNil ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (Nil, tmp) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValNil)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF128(_) -> failwith "Unimplemented"
  | RValF64(_) -> failwith "Unimplemented"
  | RValF32(_) -> failwith "Unimplemented"
  | RValBool(_) -> failwith "Unimplemented"
  | RValStr(_) -> failwith "Unimplemented"
  | RValInt(_, _) -> failwith "Unimplemented"

  | RValCast(_, _, _) -> failwith "Unimplemented"
  | RUnOp(_, _, _) -> failwith "Unimplemented"
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
      let instr = Instr(HTupleExpr(decl, hvars)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope, decl)


  | RIndexExpr(_, _, _) -> failwith "Unimplemented"
  | RTupleIndexExpr(_, _, _) -> failwith "Unimplemented"
  | RArrayExpr(_, _) -> failwith "Unimplemented"
  | RValRawArray(_) -> failwith "Unimplemented"
  | RVariantCtorExpr(_, _, _) -> failwith "Unimplemented"
  | RExprInvoke(_, _, _) -> failwith "Unimplemented"
  | RWhileExpr(_, _, _, _) -> failwith "Unimplemented"
  | RMatchExpr(_, _, _) -> failwith "Unimplemented"
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
      let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in

      let decl = (t, name) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueAssign(decl, HValVar(hvar))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope)

  (* Declare a list of new named variables. *)
  | RDeclDefStmt(name_t_pairs) ->
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
