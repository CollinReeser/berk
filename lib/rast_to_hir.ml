open Hir
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


(* Yield a pointer into some arbitrarily-complex datastructure, a series
of indexes to get to (a pointer to) the desired element within, and the
type of the element that will be yielded after loading from that pointer.
*)
let rec indexable_expr_to_hir hctxt hscope idxable =
  begin match idxable with
  (* A named variable is already an alloca'd value accessible via pointer
  on the stack. We want to merely yield that variable pointer. *)
  | RValVar(t, name) ->
      (* Yield the variable itself, ie, the _pointer to_ the variable
      value. *)

      let decl_t = RPtr(t) in
      let decl_ptr = (decl_t, name) in
      (hctxt, hscope, decl_ptr, [], decl_t)

  (* An inner indexing operation means we have another layer of the target
  type to unwrap. We also want to do all indexing in one shot, so we
  accumulate a list of indexes, so we can do index->index->load,
  rather than index->load->index->load. *)
  | RIndexExpr(_, inner_idx_expr, inner_idxable_expr) ->
      let (hctxt, hscope, inner_idx) =
        rexpr_to_hir hctxt hscope inner_idx_expr
      in
      let (hctxt, hscope, inner_idxable, idxs_rev, ptr_agg_t) =
        indexable_expr_to_hir hctxt hscope inner_idxable_expr
      in

      (* Since we're doing another index operation, the element type we
      got back from our recursive call is itself some
      dereferenceable/indexable type, so unwrap that type further to get
      the element type at this level of indexing. *)
      let elem_t = unwrap_indexable_pointer ptr_agg_t in

      (hctxt, hscope, inner_idxable, inner_idx :: idxs_rev, elem_t)

  | RTupleIndexExpr(_, i, inner_idxable_expr) ->
      let (hctxt, tmp_idx) = get_tmp_name hctxt in
      let inner_idx = (RI32, tmp_idx) in
      let instr_idx = Instr(HValueAssign(inner_idx, HValI32(i))) in
      let instrs = instr_idx :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      let (hctxt, hscope, inner_idxable, idxs_rev, aggregate_t) =
        indexable_expr_to_hir hctxt hscope inner_idxable_expr
      in

      (* Since we're doing another index operation, the element type we
      got back from our recursive call is itself some
      dereferenceable/indexable type, so unwrap that type further to get
      the element type at this level of indexing. *)
      let elem_t = unwrap_aggregate_indexable_pointer aggregate_t i in

      (hctxt, hscope, inner_idxable, inner_idx :: idxs_rev, elem_t)

  (* If we actually need to perform a dereference because we've hit a layer of
  indirection, then we need to collate the indices we've potentially collected
  so far, generate a dynamic index to load using those indices, load that
  pointer, and clear our indices-so-far collection since we just loaded them. *)
  | RDerefAddr(_, inner_derefable_expr) ->
      (* Recurse and acquire the resolved indexable expression up to this point,
      including any indices we need to navigate the indexable expression. *)
      let (hctxt, hscope, inner_idxable, idxs_rev, ptr_t) =
        indexable_expr_to_hir hctxt hscope inner_derefable_expr
      in

      (* Get our calculated pointer to the address we're going to dereference.

      If we haven't already collected any indices, then we don't need to
      calculate a dynamic index, because we're just going to dereference a
      pointer we already have in-hand (i.e., a reference variable). *)
      let (hctxt, hscope, decl_ptr) =
        let idxs = List.rev idxs_rev in

        if List.length idxs > 0 then
          let (hctxt, tmp) = get_tmp_name hctxt in
          let decl_ptr = (ptr_t, tmp) in
          let instr = Instr(HDynamicIndex(decl_ptr, idxs, inner_idxable)) in
          let instrs = instr :: hscope.instructions in
          let hscope = {hscope with instructions = instrs} in
          (hctxt, hscope, decl_ptr)

        else
          (hctxt, hscope, inner_idxable)
      in

      (* We expect that the type we got back from our recursion is itself some
      layer of indirection that we can unwrap, where that unwrap should itself
      yield a some other indexable (pointer, array, etc). *)
      let elem_t = unwrap_indexable_pointer ptr_t in

      (* Load that address, which should yield to us a pointer that can then
      be loaded from, assigned to, or indexed further. *)
      let (hctxt, hscope, decl_lval) =
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (elem_t, tmp) in
        let instr = Instr(HValueLoad(decl, decl_ptr)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope, decl)
      in

      (* Note again that we clear the indices calculated before this point,
      since we've already used them in a load. *)
      (hctxt, hscope, decl_lval, [], elem_t)

  | _ ->
      failwith (
        Printf.sprintf (
          "RAST->HIR: RIndexExpr: Idxing unimplemented " ^^
          "for [[ %s ]]"
        ) (fmt_rexpr idxable)
      )
  end


and rexpr_to_hir ?(autoload=true) hctxt hscope rexpr
  : (hir_ctxt * hir_scope * hir_variable)
=

  begin match rexpr with
  | RValVar(t, name) ->
      (* The real, internal type of a variable is actually a pointer to its
      apparent type, because variable values are stored on the stack and
      really variables themselves are the pointers to this stack location.
      *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let var = (RPtr(t), name) in
      let instr = Instr(HValueLoad(decl, var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValFunc(func_t, func_name) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (func_t, tmp) in
      let instr = Instr(HValueAssign(decl, HValFunc(func_name))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValNil ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RNil, tmp) in
      let instr = Instr(HValueAssign(decl, HValNil)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValBool(b) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let instr = Instr(HValueAssign(decl, HValBool(b))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValStr(s) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RString, tmp) in
      let instr = Instr(HValueAssign(decl, HValStr(s))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF32(f) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RF32, tmp) in
      let instr = Instr(HValueAssign(decl, HValF32(f))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF64(f) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RF64, tmp) in
      let instr = Instr(HValueAssign(decl, HValF64(f))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValF128(s) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RF128, tmp) in
      let instr = Instr(HValueAssign(decl, HValF128(s))) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
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
      let instr = Instr(HValueAssign(decl, hval)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  (* Taking the address of a named variable means merely acquiring the existing
  pointer to the variable. *)
  | RAddressOf(ptr_t, RValVar(_, name)) ->
      let (hctxt, tmp_address) = get_tmp_name hctxt in
      let decl_address = (ptr_t, tmp_address) in
      (* The variable is _really_ a pointer to that type.

      TODO: We should uniformly treat variables as pointers to a type instead of
      pretending they are their direct type. *)
      let var = HValVar(ptr_t, name) in
      let instr = Instr(HValueAssign(decl_address, var)) in

      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl_address)

  (* There are two paths this can take:

  (1) Taking the address of an expression that is not a named variable, but is
  still _accessible from_ a named variable, means evaluating the expression as
  far as possible, but without loading the evaluated pointer and instead just
  taking the pointer itself as our value. e.g., if we're taking the address of
  an inner array of a multidimensional array, or even the bottom value after
  fully indexing an array, and that array is ultimately owned by a named
  variable, then we just make sure we don't actually _load_ the indexed value,
  but rather use the pointer to it itself.

  (2) Taking the address of a true temporary, ie, a value that is not reached
  via dereferencing/indexing on a named variable. A raw value not already stored
  on the stack. In this case, since we want the address, we go out of our way to
  store the temporary to the stack, pretend it is a (inaccessible) named
  variable, and continue as if we were taking a reference to that variable.
  *)
  | RAddressOf(t, exp) ->
      (* Evaluate the expression, with autoload disabled. This will yield a
      pointer to the value back to us. *)
      let (hctxt, hscope, exp_var) =
        rexpr_to_hir ~autoload:false hctxt hscope exp
      in

      begin if is_true_temporary exp then
        (* The value we got from the evaluation of the expression is a true
        temporary, ie, a bare value not reachable from a named variable. In
        order to take its address, we must first store the temporary to the
        stack and _make_ an (inaccessible) named variable. *)
        let (hctxt, tmp_store) = get_tmp_name hctxt in
        let decl_store = (t, tmp_store) in
        let decls = decl_store :: hscope.declarations in
        let instr_store = Instr(HValueStore(decl_store, exp_var)) in
        let instrs = instr_store :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in

        (hctxt, hscope, decl_store)

      else
        (* The value we got from the evaluation of the expression is ultimately
        a pointer into some datastructure owned by a named variable, so simply
        pass that pointer along. *)

        (hctxt, hscope, exp_var)

      end

  (* Dereferencing an address means loading the pointer. *)
  | RDerefAddr(t, exp) ->
      let (hctxt, hscope, exp_var) = rexpr_to_hir hctxt hscope exp in

      if autoload then
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (t, tmp) in
        let instr = Instr(HValueLoad(decl, exp_var)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope, decl)
      else
        (hctxt, hscope, exp_var)


  | RUnOp(t, op, exp) ->
      let (hctxt, hscope, rhs_var) = rexpr_to_hir hctxt hscope exp in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let instr = Instr(HUnOp(decl, op, rhs_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RValCast(target_t, (Bitwise as op), exp) ->
      let exp_t = rexpr_type exp in

      let (hctxt, hscope, rhs_var) = rexpr_to_hir hctxt hscope exp in

      (* Only generate the cast if it's a non-no-op cast, as otherwise
      during codegen the code generator may elide the cast instruction
      entirely, which can mess up the expectation that MIR and codegen IR
      agree on names of temporaries.

      NOTE: We still treat the final decl as-if it were casted to the
      target type, even if we elide an explicit cast.
      *)

      let (hctxt, hscope, decl) = begin
        if (is_bitwise_same_type target_t exp_t) then
          (* In this case, the source type and target type have the same bitwise
          representation, so we must elide an instruction to perform an actual
          cast. Instead, we perform an "implicit" cast by storing the source
          value into a memory location, and loading it back in as-if it were the
          target type.

          NOTE: This kind of implicit cast is often required when casting
          variant temporaries, so that follow-on instructions are working in
          terms of the variant's "super tuple" type, rather than its "concrete
          tuple" type. *)
          let (hctxt, tmp_store) = get_tmp_name hctxt in
          let (hctxt, tmp_load) = get_tmp_name hctxt in
          let decl_store = (RPtr(exp_t), tmp_store) in
          let decl_load = (target_t, tmp_load) in
          let decls = decl_store :: hscope.declarations in
          let instr_store = Instr(HValueStore(decl_store, rhs_var)) in
          let instr_load = Instr(HValueLoad(decl_load, decl_store)) in
          let instrs = instr_load :: instr_store :: hscope.instructions in
          let hscope = {declarations = decls; instructions = instrs} in
          (hctxt, hscope, decl_load)

        else
          let (hctxt, tmp_store) = get_tmp_name hctxt in
          let (hctxt, tmp_cast) = get_tmp_name hctxt in
          let (hctxt, tmp_load) = get_tmp_name hctxt in
          let decl_store = (RPtr(exp_t), tmp_store) in
          let decl_cast = (RPtr(target_t), tmp_cast) in
          let decl_load = (target_t, tmp_load) in
          let decls = decl_store :: hscope.declarations in
          let instr_store = Instr(HValueStore(decl_store, rhs_var)) in
          let instr_cast = Instr(HValCast(decl_cast, op, decl_store)) in
          let instr_load = Instr(HValueLoad(decl_load, decl_cast)) in
          let instrs =
            instr_load :: instr_cast :: instr_store :: hscope.instructions
          in
          let hscope = {declarations = decls; instructions = instrs} in
          (hctxt, hscope, decl_load)
      end in

      (hctxt, hscope, decl)

  | RValCast(t, op, exp) ->
      let (hctxt, hscope, rhs_var) = rexpr_to_hir hctxt hscope exp in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let instr = Instr(HValCast(decl, op, rhs_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RBinOp(t, op, lhs, rhs) ->
      let (hctxt, hscope, lhs_var) = rexpr_to_hir hctxt hscope lhs in
      let (hctxt, hscope, rhs_var) = rexpr_to_hir hctxt hscope rhs in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (t, tmp) in
      let instr = Instr(HBinOp(decl, op, lhs_var, rhs_var)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  (* Declare an outer variable, create an inner scope, evaluate an initial
  statement within that inner scope, evaluate an expr within that inner scope
  and assign the result to the declared outer variable. *)
  | RBlockExpr(t, rstmt, rexpr) ->
      let (hctxt, hscope, decl_store, decl_load) = begin
        let (hctxt, tmp_store) = get_tmp_name hctxt in
        let decl_store = (RPtr(t), tmp_store) in
        let decls = decl_store :: hscope.declarations in
        let hscope = {hscope with declarations = decls} in

        let (hctxt, tmp_load) = get_tmp_name hctxt in
        let decl_load = (t, tmp_load) in

        (hctxt, hscope, decl_store, decl_load)
      end in

      let (hctxt, inner_scope) = begin
        let inner_scope = empty_scope in
        let (hctxt, inner_scope) = rstmt_to_hir hctxt inner_scope rstmt in
        let (hctxt, inner_scope, hvar) = rexpr_to_hir hctxt inner_scope rexpr in

        let inner_instr = Instr(HValueStore(decl_store, hvar)) in
        let inner_instrs = inner_instr :: inner_scope.instructions in
        let inner_scope = {inner_scope with instructions = inner_instrs} in

        (hctxt, inner_scope)
      end in

      let instr_scope = Scope(inner_scope) in
      let instr_load = Instr(HValueLoad(decl_load, decl_store)) in
      let instrs = instr_load :: instr_scope :: hscope.instructions in

      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl_load)

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
      let instr = Instr(HAggregate(decl, hvars)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl)

  | RTupleIndexExpr(index_result_t, idx, tuple_exp) ->
      (* Generate the first-level index value. *)
      let (hctxt, hscope, decl_idx) = begin
        let (hctxt, tmp_idx) = get_tmp_name hctxt in
        let decl_idx = (RI32, tmp_idx) in
        let instr_idx = Instr(HValueAssign(decl_idx, HValI32(idx))) in
        let instrs = instr_idx :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope, decl_idx)
      end in

      (* Evaluate the expression we'll ultimately index into, and any additional
      layers of indexing we need to do, and the resultant type we will get once
      the generated index pointer is loaded. *)
      let (hctxt, hscope, idxable, inner_idxs_rev, elem_t) =
        indexable_expr_to_hir hctxt hscope tuple_exp
      in

      let idxs_rev = decl_idx :: inner_idxs_rev in
      let idxs = List.rev idxs_rev in

      let elem_t = unwrap_aggregate_indexable_pointer elem_t idx in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl_ptr = (elem_t, tmp) in
      let instr = Instr(HDynamicIndex(decl_ptr, idxs, idxable)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      let (hctxt, hscope, decl_result) = begin
        let pointed_elem_t = unwrap_ptr elem_t in

        if is_same_type elem_t index_result_t then
          (* If the expected result of the top-level index operation is just the
          pointer to the indexed value, we're done. *)
          (hctxt, hscope, decl_ptr)

        else if
          (not autoload) &&
          is_same_type pointed_elem_t index_result_t
        then
          (* If the expected result of the top-level index operation is the
          value itself (and which must be a base type and not something that
          needs further indexing), _but_ we were instructed not to autoload
          the value, then return the pointer to the value. *)
          (hctxt, hscope, decl_ptr)

        else if is_same_type pointed_elem_t index_result_t then
          (* If the expected result of the top-level index operation is the
          value itself (and which must be a base type and not something that
          needs further indexing), then load that value. *)
          let (hctxt, tmp) = get_tmp_name hctxt in
          let decl_result = (pointed_elem_t, tmp) in
          let instr = Instr(HValueLoad(decl_result, decl_ptr)) in
          let instrs = instr :: hscope.instructions in
          let hscope = {hscope with instructions = instrs} in
          (hctxt, hscope, decl_result)

        else
          failwith (
            Printf.sprintf
              "Error: Tuple index is yielding unexpected type [ %s ] vs [ %s ]"
              (fmt_rtype elem_t)
              (fmt_rtype index_result_t)
          )
      end in

      (hctxt, hscope, decl_result)

  | RIndexExpr(index_result_t, idx_expr, idxable_expr) ->
      (* Generate the first-level dynamic index value. *)
      let (hctxt, hscope, idx) = rexpr_to_hir hctxt hscope idx_expr in

      (* Evaluate the expression we'll ultimately index into, and any additional
      layers of indexing we need to do, and the resultant type we will get once
      the generated index pointer is loaded. *)
      let (hctxt, hscope, idxable, inner_idxs_rev, elem_t) =
        indexable_expr_to_hir hctxt hscope idxable_expr
      in

      let idxs_rev = idx :: inner_idxs_rev in
      let idxs = List.rev idxs_rev in

      let elem_t = unwrap_indexable_pointer elem_t in

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl_ptr = (elem_t, tmp) in
      let instr = Instr(HDynamicIndex(decl_ptr, idxs, idxable)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      let (hctxt, hscope, decl_result) = begin
        let pointed_elem_t = unwrap_ptr elem_t in

        if is_same_type elem_t index_result_t then
          (* If the expected result of the top-level index operation is just the
          pointer to the indexed value, we're done. *)
          (hctxt, hscope, decl_ptr)

        else if
          (not autoload) &&
          is_same_type pointed_elem_t index_result_t
        then
          (* If the expected result of the top-level index operation is the
          value itself (and which must be a base type and not something that
          needs further indexing), _but_ we were instructed not to autoload
          the value, then return the pointer to the value. *)
          (hctxt, hscope, decl_ptr)

        else if is_same_type pointed_elem_t index_result_t then
          (* If the expected result of the top-level index operation is the
          value itself (and which must be a base type and not something that
          needs further indexing), then load that value. *)
          let (hctxt, tmp) = get_tmp_name hctxt in
          let decl_result = (pointed_elem_t, tmp) in
          let instr = Instr(HValueLoad(decl_result, decl_ptr)) in
          let instrs = instr :: hscope.instructions in
          let hscope = {hscope with instructions = instrs} in
          (hctxt, hscope, decl_result)

        else
          failwith (
            Printf.sprintf
              "Error: Array index is yielding unexpected type [ %s ] vs [ %s ]"
              (fmt_rtype elem_t)
              (fmt_rtype index_result_t)
          )
      end in

      (hctxt, hscope, decl_result)

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
      let instr = Instr(HValueAssign(decl, HValNil)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope, decl)

  | RValRawArray(t) ->
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RPtr(t), tmp) in
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
      let instr = Instr(HAggregate(decl, hvars)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

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
      let instr = Instr(get_invoke_instr ret_t decl hfunc hargs) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope, decl)

  | RMatchExpr(t, matched_exp, patts_to_exprs) ->
      let (hctxt, hscope, hmatchee) = rexpr_to_hir hctxt hscope matched_exp in

      (* Create a variable which will be assigned to in each match arm with
      the match-arm result value. This will be used as the overall match-expr
      result value. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl_store = (RPtr(t), tmp) in
      let decls = decl_store :: hscope.declarations in
      let hscope = {hscope with declarations = decls} in

      (* Create an inner scope within which we'll generate the match arms. *)
      let match_scope = empty_scope in

      let (hctxt, match_scope) =
        rmatch_arms_to_hir hctxt match_scope hmatchee decl_store patts_to_exprs
      in

      (* Load the result of the match expr after the end of the match scope. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl_load = (t, tmp) in
      let instr = Scope(match_scope) in
      let instr_load = Instr(HValueLoad(decl_load, decl_store)) in
      let instrs = instr_load :: instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope, decl_load)
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
      let decl = (RPtr(t), name) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueStore(decl, hmatchee)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in

      (hctxt, hscope, htrue)

  | RPatternAs(t, as_patt, name) ->
      (* Declare a new variable that binds to the matchee.

      TODO: Later: this should be a transparent reference to the actual matched
      value. *)
      let decl = (RPtr(t), name) in
      let decls = decl :: hscope.declarations in
      let instr = Instr(HValueStore(decl, hmatchee)) in
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
      let instr = Instr(HBinOp(decl, Eq, hmatchee, hbool)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope, decl)

  | RPCastThen(t, target_t, (Bitwise as op), casted_patt) ->
      let matchee_t = hir_variable_type hmatchee in

      let _ =
        if is_same_type t matchee_t then
          ()
        else
          failwith (
            Printf.sprintf
              "Error: Pattern type and expr type do not agree: [ %s ] vs [ %s ]"
              (fmt_rtype t)
              (fmt_rtype matchee_t)
          )
      in

      (* Only generate the cast if it's a non-no-op cast, as otherwise
      during codegen the code generator may elide the cast instruction
      entirely, which can mess up the expectation that MIR and codegen IR
      agree on names of temporaries. *)

      let (hctxt, hscope, decl) = begin
        if (is_bitwise_same_type target_t matchee_t) then
          (hctxt, hscope, hmatchee)

        else
          (* Cast the matchee to the target type, then descend into the sub
          pattern. *)
          let (hctxt, tmp_store) = get_tmp_name hctxt in
          let (hctxt, tmp_cast) = get_tmp_name hctxt in
          let (hctxt, tmp_load) = get_tmp_name hctxt in
          let decl_store = (RPtr(matchee_t), tmp_store) in
          let decl_cast = (RPtr(target_t), tmp_cast) in
          let decl_load = (target_t, tmp_load) in
          let decls = decl_store :: hscope.declarations in
          let instr_store = Instr(HValueStore(decl_store, hmatchee)) in
          let instr_cast = Instr(HValCast(decl_cast, op, decl_store)) in
          let instr_load = Instr(HValueLoad(decl_load, decl_cast)) in
          let instrs =
            instr_load :: instr_cast :: instr_store :: hscope.instructions
          in
          let hscope = {declarations = decls; instructions = instrs} in
          (hctxt, hscope, decl_load)
      end in

      rpattern_to_hir hctxt hscope decl casted_patt

  | RPCastThen(t, target_t, op, casted_patt) ->
      let matchee_t = hir_variable_type hmatchee in

      let _ =
        if is_same_type t matchee_t then
          ()
        else
          failwith (
            Printf.sprintf
              "Error: Pattern type and expr type do not agree: [ %s ] vs [ %s ]"
              (fmt_rtype t)
              (fmt_rtype matchee_t)
          )
      in

      (* Cast the matchee to the target type, then descend into the sub
      pattern. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (target_t, tmp) in
      let instr = Instr(HValCast(decl, op, hmatchee)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      rpattern_to_hir hctxt hscope decl casted_patt

  | RPIntLit(t, i) ->
      (* Create a temporary containing the int to match against. *)
      let (hctxt, hscope, hint) = rexpr_to_hir hctxt hscope (RValInt(t, i)) in

      (* Create an instruction to compare the matchee against the int. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let instr = Instr(HBinOp(decl, Eq, hmatchee, hint)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope, decl)

  | RPIntFrom(t, i) ->
      (* Create a temporary containing the int to compare against. *)
      let (hctxt, hscope, hint) = rexpr_to_hir hctxt hscope (RValInt(t, i)) in

      (* Create an instruction to compare the matchee against the int. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let instr = Instr(HBinOp(decl, Ge, hmatchee, hint)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

      (hctxt, hscope, decl)

  | RPIntUntil(t, i) ->
      (* Create a temporary containing the int to compare against. *)
      let (hctxt, hscope, hint) = rexpr_to_hir hctxt hscope (RValInt(t, i)) in

      (* Create an instruction to compare the matchee against the int. *)
      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl = (RBool, tmp) in
      let instr = Instr(HBinOp(decl, Lt, hmatchee, hint)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in

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
        let instr = Instr(HBinOp(decl, Ge, hmatchee, hlhs)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (* Create an instruction to compare the matchee against the second int. *)
      let (hctxt, hscope, hrhs_cmp) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (RBool, tmp) in
        let instr = Instr(HBinOp(decl, Lt, hmatchee, hrhs)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (* Create an instruction to confirm the int was within the range . *)
      let (hctxt, hscope, hwithin_range) = begin
        let (hctxt, tmp) = get_tmp_name hctxt in
        let decl = (RBool, tmp) in
        let instr = Instr(HBinOp(decl, Eq, hlhs_cmp, hrhs_cmp)) in
        let instrs = instr :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope, decl)
      end in

      (hctxt, hscope, hwithin_range)

  | RPTuple(tup_t, patts) ->
      (* Declare a boolean, defaulting to true but assignable to false in the
      case that any of the tuple elems don't match the pattern. *)
      let (hctxt, hscope, decl_store) = begin
        let (hctxt, tmp_assign) = get_tmp_name hctxt in
        let (hctxt, tmp_store) = get_tmp_name hctxt in
        let decl_assign = (RBool, tmp_assign) in
        let decl_store = (RPtr(RBool), tmp_store) in
        let decls = decl_store :: hscope.declarations in
        let instr_assign = Instr(HValueAssign(decl_assign, HValBool(true))) in
        let instr_store = Instr(HValueStore(decl_store, decl_assign)) in
        let instrs = instr_store :: instr_assign :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in
        (hctxt, hscope, decl_store)
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

              let (hctxt, tmp_idx) = get_tmp_name hctxt in
              let (hctxt, tmp_store) = get_tmp_name hctxt in
              let (hctxt, tmp_idx_val) = get_tmp_name hctxt in
              let (hctxt, tmp_load) = get_tmp_name hctxt in

              let decl_idx = (RI32, tmp_idx) in
              let decl_store = (RPtr(tup_t), tmp_store) in
              let decl_idx_val = (RPtr(elem_t), tmp_idx_val) in
              let decl_load = (elem_t, tmp_load) in

              let decls = decl_store :: cur_scope.declarations in

              let instr_idx = Instr(HValueAssign(decl_idx, HValI32(idx))) in
              let instr_store = Instr(HValueStore(decl_store, hmatchee)) in
              let instr_idx_val =
                Instr(HDynamicIndex(decl_idx_val, [decl_idx], decl_store))
              in
              let instr_load = Instr(HValueLoad(decl_load, decl_idx_val)) in

              let instrs =
                instr_load :: instr_idx_val :: instr_store :: instr_idx ::
                  cur_scope.instructions
              in
              let cur_scope = {declarations = decls; instructions = instrs} in
              (hctxt, cur_scope, decl_load)
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
            let (hctxt, else_scope) = begin
              let else_scope = empty_scope in
              let (hctxt, tmp) = get_tmp_name hctxt in
              let decl_as = (RBool, tmp) in
              let instr_as = Instr(HValueAssign(decl_as, HValBool(false))) in
              let instr_st = Instr(HValueStore(decl_store, decl_as)) in
              let instrs = instr_st :: instr_as :: else_scope.instructions in
              let else_scope = {else_scope with instructions = instrs} in
              (hctxt, else_scope)
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

      let (hctxt, tmp) = get_tmp_name hctxt in
      let decl_load = (RBool, tmp) in
      let instr_scope = Scope(tuple_match_scope) in
      let instr_load = Instr(HValueLoad(decl_load, decl_store)) in
      let instrs = instr_load :: instr_scope :: hscope.instructions in
      let hscope = {hscope with instructions = instrs} in
      (hctxt, hscope, decl_load)
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

            let instr = Instr(HValueStore(hresult, arm_result)) in
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


(* Given a decl (that's assumed to have already been added to the scope),
initialize the memory pointed to by that decl. *)
and initialize_decls hctxt hscope decls =
  let _decl_type_to_val t =
    begin match t with
    | RI64 -> HValI64(0)
    | RI32 -> HValI32(0)
    | RI16 -> HValI16(0)
    | RI8  -> HValI8(0)
    | RU64 -> HValU64(0)
    | RU32 -> HValU32(0)
    | RU16 -> HValU16(0)
    | RU8  -> HValU8(0)
    | RF128 -> HValF128("0.0")
    | RF64  -> HValF64(0.0)
    | RF32  -> HValF32(0.0)
    | RBool -> HValBool(false)
    | RString -> HValStr("")
    | RNil -> HValNil
    | _ ->
        failwith (
          Printf.sprintf
            "initialize_decls._decl_type_to_val for [ %s ] unimplemented."
            (fmt_rtype t)
        )
    end
  in

  let rec _initialize_decl (hctxt, hscope) ((ptr_t, _) as decl) =
    begin match ptr_t with
    | RPtr(
        (
          RI64 | RI32 | RI16 | RI8 |
          RU64 | RU32 | RU16 | RU8 |
          RF128 | RF64 | RF32 |
          RBool |
          RString |
          RNil
        ) as basic_t
      ) ->
        let init_val = _decl_type_to_val basic_t in

        let (hctxt, tmp_init) = get_tmp_name hctxt in
        let decl_init = (basic_t, tmp_init) in
        let instr_init = Instr(HValueAssign(decl_init, init_val)) in
        let instr_store = Instr(HValueStore(decl, decl_init)) in
        let instrs = instr_store :: instr_init :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope)

    | RPtr(RTuple(ts)) ->
        (* For each static index of the tuple, calculate a pointer to that
        index, and recurse. *)
        let (hctxt, hscope, _) =
          List.fold_left (
            fun (hctxt, hscope, idx) t ->
              let (hctxt, tmp_idx) = get_tmp_name hctxt in
              let (hctxt, tmp_ptr) = get_tmp_name hctxt in
              let decl_idx = (RI32, tmp_idx) in
              let decl_ptr = (RPtr(t), tmp_ptr) in
              let instr_idx = Instr(HValueAssign(decl_idx, HValI32(idx))) in
              let instr_ptr = Instr(HDynamicIndex(decl_ptr, [decl_idx], decl)) in
              let instrs = instr_ptr :: instr_idx :: hscope.instructions in
              let hscope = {hscope with instructions = instrs} in

              let (hctxt, hscope) = _initialize_decl (hctxt, hscope) decl_ptr in

              (hctxt, hscope, (idx + 1))
          ) (hctxt, hscope, 0) ts
        in

        (hctxt, hscope)

    | RPtr(RArray(t, sz)) ->
        (* Looping over each index in the array, calculate a pointer to that
        index and recurse. *)

        (* Declare and initialize an iteration variable. *)

        let (hctxt, hscope, decl_iter_store) =
          let (hctxt, tmp_iter) = get_tmp_name hctxt in
          let (hctxt, tmp_iter_store) = get_tmp_name hctxt in
          let decl_iter = (RI32, tmp_iter) in
          let decl_iter_store = (RPtr(RI32), tmp_iter_store) in
          let decls = decl_iter_store :: hscope.declarations in
          let instr_iter = Instr(HValueAssign(decl_iter, HValI32(0))) in
          let instr_iter_store = Instr(HValueStore(decl_iter_store, decl_iter)) in
          let instrs = instr_iter_store :: instr_iter :: hscope.instructions in
          let hscope = {declarations = decls; instructions = instrs} in

          (hctxt, hscope, decl_iter_store)
        in

        (* Populate the condition-evaluation scope, yielding that scope and the
        evaluated condition. *)
        let (hctxt, cond_scope, decl_cond) =
          let cond_scope = empty_scope in

          let (hctxt, tmp_iter) = get_tmp_name hctxt in
          let (hctxt, tmp_size) = get_tmp_name hctxt in
          let (hctxt, tmp_cond) = get_tmp_name hctxt in
          let decl_iter = (RI32, tmp_iter) in
          let decl_size = (RI32, tmp_size) in
          let decl_cond = (RBool, tmp_cond) in
          let instr_iter = Instr(HValueLoad(decl_iter, decl_iter_store)) in
          let instr_size = Instr(HValueAssign(decl_size, HValI32(sz))) in
          let instr_cond = Instr(HBinOp(decl_cond, Lt, decl_iter, decl_size)) in
          let instrs = (
            instr_cond ::
            instr_size ::
            instr_iter ::
            cond_scope.instructions
          ) in
          let cond_scope = {cond_scope with instructions = instrs} in

          (hctxt, cond_scope, decl_cond)
        in

        (* In the body of the loop, calculate a pointer to the "current" element
        in the array, based on our iterator variable, and then increment our
        iterator. *)
        let (hctxt, body_scope) =
          let body_scope = empty_scope in

          let (hctxt, tmp_iter) = get_tmp_name hctxt in
          let (hctxt, tmp_ptr) = get_tmp_name hctxt in
          let decl_iter = (RI32, tmp_iter) in
          let decl_ptr = (RPtr(t), tmp_ptr) in
          let instr_iter = Instr(HValueLoad(decl_iter, decl_iter_store)) in
          let instr_ptr = Instr(HDynamicIndex(decl_ptr, [decl_iter], decl)) in
          let instrs = instr_ptr :: instr_iter :: body_scope.instructions in
          let body_scope = {body_scope with instructions = instrs} in

          let (hctxt, body_scope) =
            _initialize_decl (hctxt, body_scope) decl_ptr
          in

          (* Inject incrementing the array iterator variable at the end of the
          loop body. *)
          let (hctxt, tmp_one) = get_tmp_name hctxt in
          let (hctxt, tmp_inc) = get_tmp_name hctxt in
          let decl_one = (RI32, tmp_one) in
          let decl_inc = (RI32, tmp_inc) in
          let instr_one = Instr(HValueAssign(decl_one, HValI32(1))) in
          let instr_inc = Instr(HBinOp(decl_inc, Add, decl_one, decl_iter)) in
          let instr_iter_store = Instr(HValueStore(decl_iter_store, decl_inc)) in

          let instrs = (
            instr_iter_store ::
            instr_inc ::
            instr_one ::
            body_scope.instructions
          ) in
          let body_scope = {body_scope with instructions = instrs} in

          (hctxt, body_scope)
        in

        let instr_loop = CondLoopScope(cond_scope, decl_cond, body_scope) in
        let instrs = instr_loop :: hscope.instructions in
        let hscope = {hscope with instructions = instrs} in
        (hctxt, hscope)

    | _ ->
        failwith (
          Printf.sprintf
            "initialize_decls._initialize_decl for [ %s ] is nonsense."
            (fmt_rtype ptr_t)
        )
    end
  in

  List.fold_left _initialize_decl (hctxt, hscope) decls


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
  | RDeclStmt(name, expected_t, rexpr) ->
      (* NOTE: The declared type is not used. We might be doing some sort of an
      internal representational transformation and want to use the resultant
      transformation type, not the high-level original type. *)

      let (hctxt, hscope, hvar) = rexpr_to_hir hctxt hscope rexpr in
      let hvar_t = hir_variable_type hvar in

      let _ =
        if is_same_type expected_t hvar_t then
          ()
        else
          failwith (
            Printf.sprintf
              "Got unexpected disagreement in RHS type: expected: [ %s ] vs got: [ %s ]"
              (fmt_rtype expected_t)
              (fmt_rtype hvar_t)
          )
      in

      let decl_store = (RPtr(hvar_t), name) in
      let decls = decl_store :: hscope.declarations in
      let instr = Instr(HValueStore(decl_store, hvar)) in
      let instrs = instr :: hscope.instructions in
      let hscope = {declarations = decls; instructions = instrs} in
      (hctxt, hscope)

  (* Declare a list of new named variables. *)
  | RDeclDefaultStmt(name_t_pairs) ->
      (* NOTE: This depends on an earlier pass having ensured that the only
      variables declared this way are those with types that have deterministic
      default values, which coincidentally is also the set of types which we
      would lower any higher-level types into. *)
      let default_decls =
        List.map (fun (name, t) -> (RPtr(t), name)) name_t_pairs
      in
      let decls = default_decls @ hscope.declarations in
      let hscope = {hscope with declarations = decls} in

      let (hctxt, hscope) = initialize_decls hctxt hscope default_decls in
      (hctxt, hscope)

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
  | RAssignStmt(_, _, lval_rexpr, rhs_rexpr) ->
      let (hctxt, hscope, rhs_hvar) = rexpr_to_hir hctxt hscope rhs_rexpr in

      (* Evaluate the expression we'll ultimately index into, and any additional
      layers of indexing we need to do, and the resultant type we will get once
      the generated index pointer is loaded. *)
      let (hctxt, hscope, decl_idxable, inner_idxs_rev, elem_t) =
        indexable_expr_to_hir hctxt hscope lval_rexpr
      in

      let (hctxt, hscope, decl_lval) =
        if List.length inner_idxs_rev > 0 then
          let idxs = List.rev inner_idxs_rev in

          let (hctxt, tmp) = get_tmp_name hctxt in
          let decl_ptr = (elem_t, tmp) in
          let instr = Instr(HDynamicIndex(decl_ptr, idxs, decl_idxable)) in
          let instrs = instr :: hscope.instructions in
          let hscope = {hscope with instructions = instrs} in
          (hctxt, hscope, decl_ptr)
        else
          (hctxt, hscope, decl_idxable)
      in

      let instr = Instr(HValueStore(decl_lval, rhs_hvar)) in
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


let rgenerator_decl_t_to_hgenerator_decl_t
  {rg_name; rg_params; rg_yield_t; rg_ret_t} : hgenerator_decl_t
=
  {
    hg_name = rg_name;
    hg_params = rg_params;
    hg_yield_t = rg_yield_t;
    hg_ret_t = rg_ret_t;
  }
;;


let populate_hscope_with_func_arg_vars
  hctxt hscope h_params : (hir_ctxt * hir_scope)
=
  let (hctxt, hscope, _) =
    List.fold_left (
      fun (hctxt, hscope, i) (name, t) ->
        let (hctxt, tmp_arg) = get_tmp_name hctxt in
        let decl_arg = (t, tmp_arg) in
        let decl_var = (RPtr(t), name) in
        let instr_argvar = Instr(HArgToVar(decl_arg, name, i)) in
        let instr_store = Instr(HValueStore(decl_var, decl_arg)) in
        let decls = decl_var :: hscope.declarations in
        let instrs = instr_store :: instr_argvar :: hscope.instructions in
        let hscope = {declarations = decls; instructions = instrs} in

        (hctxt, hscope, i + 1)

    ) (hctxt, hscope, 0) h_params
  in

  (hctxt, hscope)
;;


let rfunc_def_t_to_hfunc_def_t {rf_decl; rf_stmts} : hfunc_def_t =
  let {hf_params; _} as hf_decl = rfunc_decl_t_to_hfunc_decl_t rf_decl in

  let hf_scope = empty_scope in
  let hctxt = default_hir_ctxt in

  (* Initialize the scope with the function argument variables. *)
  let (hctxt, hf_scope) =
    populate_hscope_with_func_arg_vars hctxt hf_scope hf_params
  in

  let (_, hf_scope) =
    List.fold_left (
      fun (hctxt, hf_scope) rstmt ->
        let (hctxt, hf_scope) = rstmt_to_hir hctxt hf_scope rstmt in
        (hctxt, hf_scope)
    ) (hctxt, hf_scope) rf_stmts
  in

  (* The declarations and instructions in an HIR scope are populated in reverse.
  We now need to reverse them again, so that they're in the right order. *)
  let hf_scope = unreverse_hscope_decls_instrs hf_scope in

  {
    hf_decl = hf_decl;
    hf_scope = hf_scope;
  }
;;

let rgenerator_def_t_to_hgenerator_def_t
  {rg_decl; rg_stmts} : hgenerator_def_t
=
  let {hg_params; _} as hg_decl =
    rgenerator_decl_t_to_hgenerator_decl_t rg_decl
  in

  let hg_scope = empty_scope in
  let hctxt = default_hir_ctxt in

  (* Initialize the scope with the function argument variables. *)
  let (hctxt, hg_scope) =
    populate_hscope_with_func_arg_vars hctxt hg_scope hg_params
  in

  let (_, hg_scope) =
    List.fold_left (
      fun (hctxt, hg_scope) rstmt ->
        let (hctxt, hg_scope) = rstmt_to_hir hctxt hg_scope rstmt in
        (hctxt, hg_scope)
    ) (hctxt, hg_scope) rg_stmts
  in

  (* The declarations and instructions in an HIR scope are populated in reverse.
  We now need to reverse them again, so that they're in the right order. *)
  let hg_scope = unreverse_hscope_decls_instrs hg_scope in

  {hg_decl; hg_scope}
;;
