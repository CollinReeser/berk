open Ast
open Typing
open Utility

module StrMap = Map.Make(String)

type module_context = {
  func_sigs: func_decl_t StrMap.t;
  variants: variant_decl_t StrMap.t;
}

let default_mod_ctxt = {
  func_sigs = StrMap.empty;
  variants = StrMap.empty;
}

type typecheck_context = {
  vars: (berk_t * var_qual) StrMap.t;
  ret_t: berk_t;
  ret_t_candidates: berk_t list;
  mod_ctxt: module_context;
}

let default_tc_ctxt typ = {
  vars = StrMap.empty;
  ret_t = typ;
  ret_t_candidates = [];
  mod_ctxt = default_mod_ctxt;
}

let populate_ctxt_with_params f_params base_vars =
  let add_param vars (id, qual, typ) = begin
    StrMap.add id (typ, qual) vars
  end in
  let added_vars = List.fold_left add_param base_vars f_params in
  added_vars

let add_uniq_varname varname t_qual_pair vars =
  if StrMap.mem varname vars then
    failwith (Printf.sprintf "%s already in scope!" varname)
  else
    StrMap.add varname t_qual_pair vars

(* Given a variant declaration that may contain some arbitrary number of unbound
types, a variant constructor name that exists in the given variant declaration,
and the corresponding value type of the constructor, yield an
as-concrete-as-possible Variant type. *)
let variant_decl_to_variant_type {v_name; v_ctors; _} ctor_name typ =
  let (_, ctor_typ) = List.find (fun (name, _) -> name = ctor_name) v_ctors in

  let tvars_to_types = map_tvars_to_types ctor_typ typ in
  let init_variant_t = Variant(v_name, v_ctors) in

  let variant_t_concretified =
    concretify_unbound_types tvars_to_types init_variant_t
  in

  variant_t_concretified
;;


(* Given a statement/expression, return true if all involved types are
concretely bound/decided, false otherwise. *)

let rec is_concrete_stmt ?(verbose=false) stmt =
  let _is_concrete_expr expr = is_concrete_expr ~verbose:verbose expr in
  let _is_concrete_type typ  = is_concrete_type ~verbose:verbose typ in

  let res = begin match stmt with
  | ExprStmt(expr)
  | ReturnStmt(expr)
  | AssignStmt(_, expr)
  | AssignDeconStmt(_, expr) ->
      _is_concrete_expr expr

  | DeclStmt(_, _, typ, expr)
  | DeclDeconStmt(_, typ, expr) ->
      (_is_concrete_expr expr) && (_is_concrete_type typ)

  | DeclDefStmt(idents_quals_ts) ->
      List.fold_left (&&) true (
        List.map (fun (_, _, t) -> _is_concrete_type t) idents_quals_ts
      )

  end in

  let _ = if verbose then
    begin
      Printf.printf "is_concrete_stmt[[ %s ]] == %B\n%!"
        (fmt_stmt ~print_typ:true "" stmt)
        res
    end
  else
    ()
  in

  res

and is_concrete_expr ?(verbose=false) expr =
  let _is_concrete_expr expr = is_concrete_expr ~verbose:verbose expr in
  let _is_concrete_stmt stmt = is_concrete_stmt ~verbose:verbose stmt in
  let _is_concrete_type typ  = is_concrete_type ~verbose:verbose typ in
  let _is_concrete_patt patt = is_concrete_patt ~verbose:verbose patt in

  let res = begin match expr with
  | ValU64(_)  | ValU32(_) | ValU16(_) | ValU8(_)
  | ValI64(_)  | ValI32(_) | ValI16(_) | ValI8(_)
  | ValF128(_) | ValF64(_) | ValF32(_)
  | ValBool(_)
  | ValStr(_)
  | ValNil -> true

  | ValInt(typ, _) -> _is_concrete_type typ

  | ValVar(typ, _)
  | ValFunc(typ, _)
  | ValName(typ, _) -> _is_concrete_type typ

  | ValRawArray(typ) -> _is_concrete_type typ

  | ValCastTrunc(typ, expr)
  | ValCastBitwise(typ, expr)
  | ValCastExtend(typ, expr)
  | StaticIndexExpr(typ, _, expr)
  | VariantCtorExpr(typ, _, expr) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr expr)

  | BinOp(typ, _, expr_1, expr_2)
  | IndexExpr(typ, expr_1, expr_2) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr expr_1) &&
        (_is_concrete_expr expr_2)

  | IfThenElseExpr(typ, expr_1, expr_2, expr_3) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr expr_1) &&
        (_is_concrete_expr expr_2) &&
        (_is_concrete_expr expr_3)

  | BlockExpr(typ, stmts, expr) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr expr) &&
        (List.fold_left (&&) true (List.map _is_concrete_stmt stmts))

  | WhileExpr(typ, init_stmts, exp_cond, then_stmts) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr exp_cond) &&
        (List.fold_left (&&) true (List.map _is_concrete_stmt init_stmts)) &&
        (List.fold_left (&&) true (List.map _is_concrete_stmt then_stmts))

  | ArrayExpr(typ, exprs)
  | TupleExpr(typ, exprs)
  | FuncCall(typ, _, exprs) ->
      (_is_concrete_type typ) &&
        (List.fold_left (&&) true (List.map _is_concrete_expr exprs))

  | ExprInvoke(typ, func_exp, arg_exprs) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr func_exp) &&
        (List.fold_left (&&) true (List.map _is_concrete_expr arg_exprs))

  | MatchExpr(typ, matched_exp, pattern_exp_pairs) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr matched_exp) &&
        (
          List.fold_left (&&) true (
            List.map (
              fun (patt, exp) ->
                (_is_concrete_patt patt) && (_is_concrete_expr exp)
            ) pattern_exp_pairs
          )
        )
  end in

  let _ = if verbose then
    begin
      Printf.printf "is_concrete_stmt[[ %s ]] == %B\n%!"
        (fmt_expr ~print_typ:true "" expr)
        res
    end
  else
    ()
  in

  res

and is_concrete_patt ?(verbose=false) patt =
  let _is_concrete_patt patt = is_concrete_patt ~verbose:verbose patt in
  let _is_concrete_type typ  = is_concrete_type ~verbose:verbose typ  in

  begin match patt with
  | PNil -> true
  | PBool(_) -> true
  | Wild(t) -> (_is_concrete_type t)
  | VarBind(t, _) -> (_is_concrete_type t)
  | PTuple(t, _) -> (_is_concrete_type t)
  | Ctor(t, _, patt) -> (_is_concrete_type t) && (_is_concrete_patt patt)
  | PatternAs(t, patt, _) -> (_is_concrete_type t) && (_is_concrete_patt patt)
  end
;;


(* Try to yield the top-level variant type for the given constructor name and
associated list of types. If the constructor and its associated types
unambiguously match a particular variant, that variant type is returned. If
there are no matching variants, this function will fail. If no other mechanism
of disambiguation is provided and there are multiple matching variants, this
function will fail.

Optionally, a disambiguator string can be provided to assist in disambiguating
between multiple matching variants. If a disambiguator is provided, and the
constructor matches a particular variant, and the disambiguator eliminates that
variant as an option, then this function will fail.
*)
let variant_ctor_to_variant_type ?(disambiguator = "") mod_ctxt ctor_name typ =
  (* Given a variant declaration, return whether that variant contains the
  target constructor (via constructor name and associated type) *)
  let has_ctor {v_ctors; _} =
    let matching_ctor = List.find_opt (
        fun (candidate_name, candidate_typ) ->
          ctor_name = candidate_name &&
          type_convertible_to typ candidate_typ
      ) v_ctors
    in
    begin match matching_ctor with
      | None -> false
      | Some(_) -> true
    end
  in

  let variants = mod_ctxt.variants in

  let matching_variants =
    StrMap.filter (
      fun variant_name v_decl_t ->
        if disambiguator = ""
        then has_ctor v_decl_t
        else variant_name = disambiguator && has_ctor v_decl_t
    ) variants
  in

  let variant_typ = if StrMap.cardinal matching_variants = 1 then
    (* Take the one variant-name -> variant-decl binding there is. *)
    let (_, matching_variant_t) = StrMap.choose matching_variants in

    variant_decl_to_variant_type matching_variant_t ctor_name typ

  else if StrMap.cardinal matching_variants = 0 then
    failwith "No matching variants"
  else
    failwith (
      "Disambiguator " ^ disambiguator ^
      " yielded multiple matching variants"
    )
  in

  variant_typ
;;


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

(* Handle module-level declarations, ie, function decls/defs, type decls, etc *)
and type_check_mod_decl mod_ctxt mod_decl =
  (* Make sure that var-arg parameter declarations are only at the end of the
  function signature, if they exist at all. *)
  let rec confirm_at_most_trailing_var_arg f_params =
    begin match f_params with
    | [] -> true
    | (_, _, VarArgSentinel)::_::_ -> false
    | _::xs -> confirm_at_most_trailing_var_arg xs
    end
  in

  match mod_decl with
  | FuncExternDecl(f_decl_ast) ->
      let {f_name; f_params; f_ret_t;} = f_decl_ast in
      let _ = match (StrMap.find_opt f_name mod_ctxt.func_sigs) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of func " ^ f_name)
      in

      if not (confirm_at_most_trailing_var_arg f_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let func_sigs_up = begin
          StrMap.add f_name {f_name; f_params; f_ret_t} mod_ctxt.func_sigs
        end in
        let mod_ctxt_up = {mod_ctxt with func_sigs = func_sigs_up} in

        (mod_ctxt_up, FuncExternDecl(f_decl_ast))

  | FuncDef(f_ast) ->
      let {f_decl = {f_name; f_params; f_ret_t;}; _} = f_ast in
      let _ = match (StrMap.find_opt f_name mod_ctxt.func_sigs) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of func " ^ f_name)
      in

      if not (confirm_at_most_trailing_var_arg f_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let func_sigs_up = begin
          StrMap.add f_name {f_name; f_params; f_ret_t} mod_ctxt.func_sigs
        end in
        let mod_ctxt_up = {mod_ctxt with func_sigs = func_sigs_up} in
        let func_ast_typechecked = type_check_func mod_ctxt_up f_ast in

        (mod_ctxt_up, FuncDef(func_ast_typechecked))

  | VariantDecl({v_name; v_ctors; v_typ_vars} as v_decl_ast) ->
      let _ = match (StrMap.find_opt v_name mod_ctxt.variants) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of variant " ^ v_name)
      in

      let var_t = Variant(v_name, v_ctors) in
      let real_tvars = get_tvars var_t in
      let declared_tvars = List.sort compare v_typ_vars in
      let _ =
        if List.equal (=) real_tvars declared_tvars
        then ()
        else failwith (
            "Actual type vars don't match declared in variant " ^ v_name
          )
      in

      let variants_up = StrMap.add v_name v_decl_ast mod_ctxt.variants in
      let mod_ctxt_up = {mod_ctxt with variants = variants_up} in

      (mod_ctxt_up, VariantDecl(v_decl_ast))

(* Given a module-typechecking context and a function-definition AST, typecheck
the function definition and return its typechecked form. *)
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

  let (tc_ctxt_final, f_stmts_typechecked) =
    type_check_stmts tc_ctxt_init f_stmts
  in

  (* If the function declaration did not specify a return type, then we try to
  resolve that return type here. *)
  let resolved_ret_t = begin match f_ret_t with
    | Undecided -> common_type_of_lst tc_ctxt_final.ret_t_candidates
    | _ -> f_ret_t
  end in

  {
    f_stmts = f_stmts_typechecked;
    f_decl = {func_def.f_decl with f_ret_t = resolved_ret_t};
  }

and update_vars_with_idents_quals vars_init idents_quals types =
  let idents_quals_types = List.combine idents_quals types in
  List.fold_left (
    fun vars ((id, qual), typ) ->
      StrMap.add id (typ, qual) vars
  ) vars_init idents_quals_types

and type_check_stmt (tc_ctxt) (stmt) : (typecheck_context * stmt) =
  match stmt with
  | DeclStmt(ident, qual, decl_t, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt decl_t exp in
      let exp_t = expr_type exp_typechecked in
      let resolved_t = match decl_t with
      | Undecided -> exp_t
      | _ ->
        (* The expression's resolved type must be usable as the explicitly
        declared type. That said, the explicitly declared type may not have been
        fully resolved itself, but the expression's type ultimately should be
        (though it may have needed to use the explicitly-declared type's
        typevar info to fully resolve itself). *)
        if type_convertible_to exp_t decl_t then
           exp_t
        else
          begin
            let msg = Printf.sprintf (
                "Explicitly declared type [[ %s ]] " ^^
                "disagrees with deduced type [[ %s ]] " ^^
                "over expression [[ %s ]]\n%!"
              )
              (fmt_type decl_t)
              (fmt_type exp_t)
              (fmt_expr ~print_typ:true "" exp_typechecked)
            in

            failwith msg
          end
      in

      let vars_up = StrMap.add ident (resolved_t, qual) tc_ctxt.vars in
      let tc_ctxt_up = {tc_ctxt with vars = vars_up} in

      (tc_ctxt_up, DeclStmt(ident, qual, resolved_t, exp_typechecked))

  | DeclDefStmt((idents_quals_ts)) ->
      let tc_ctxt =
        List.fold_left (
          fun tc_ctxt (ident, qual, t) ->
            let vars_up = StrMap.add ident (t, qual) tc_ctxt.vars in
            {tc_ctxt with vars = vars_up}
        ) tc_ctxt idents_quals_ts
      in

      (tc_ctxt, stmt)

  | DeclDeconStmt(idents_quals, decl_t, exp) ->
      let exp_typechecked = type_check_expr tc_ctxt decl_t exp in
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

  | AssignStmt(lval, exp) ->
      let (lval_typechecked, lval_t, {mut}) =
        begin match lval with
        | ALVar(ident) ->
            let (var_t, var_qual) = StrMap.find ident tc_ctxt.vars in
            (lval, var_t, var_qual)

        | ALStaticIndex(ident, i) ->
            let (var_t, var_qual) = StrMap.find ident tc_ctxt.vars in
            let inner_t = unwrap_aggregate_indexable var_t i in

            (lval, inner_t, var_qual)

        | ALIndex(ident, idx_exps) ->
            let (var_t, var_qual) = StrMap.find ident tc_ctxt.vars in

            (* Typecheck the indexing expression. *)
            let idx_exps_typechecked =
              List.map (type_check_expr tc_ctxt Undecided) idx_exps
            in

            (* Get the type that will be produced after indexing into the given
            variable N times. *)
            let rec get_base_elem_t cur_t layers_remaining =
              begin if layers_remaining = 0 then
                cur_t
              else if is_indexable_type cur_t then
                get_base_elem_t (unwrap_indexable cur_t) (layers_remaining - 1)
              else
                failwith (
                  Printf.sprintf
                    (
                      "Indexable type exhausted before end of indexing: " ^^
                      "[%s] -> [%s] with [%d] remaining."
                    )
                    (fmt_type var_t) (fmt_type cur_t) (layers_remaining)
                )
              end
            in

            let base_elem_t = get_base_elem_t var_t (List.length idx_exps) in

            (ALIndex(ident, idx_exps_typechecked), base_elem_t, var_qual)
        end
      in

      let exp_typechecked = type_check_expr tc_ctxt lval_t exp in
      let exp_t = expr_type exp_typechecked in

      let _ =
        if mut
          then ()
          else failwith "Cannot assign to immutable var"
      in

      if type_convertible_to exp_t lval_t
        then (tc_ctxt, AssignStmt(lval_typechecked, exp_typechecked))
        else failwith "Expr for assignment does not typecheck"

  | AssignDeconStmt(lvals, exp) ->
      (* TODO: Add support for deconstructed assignment to indexed variables. *)
      let idents =
        List.map (
          fun lval -> match lval with
          | ALVar(ident) -> ident
          | _ -> failwith "Unimplemented: AssignDeconStmt for non-ALVar(_)"
        ) lvals
      in

      let assign_types = List.map (
          fun id ->
            let (var_t, _) = StrMap.find id tc_ctxt.vars in

            var_t
        ) idents
      in

      let expected_t = begin match exp with
        | TupleExpr(_, _) ->
            Tuple(assign_types)

        | ArrayExpr(_, _) ->
            let array_len = List.length idents in
            let elem_t = List.hd assign_types in
            Array(elem_t, array_len)

        | _ -> failwith "Cannot deconstruct non-tuple/array"
        end
      in

      let exp_typechecked = type_check_expr tc_ctxt expected_t exp in
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

          (* TODO: This is a hack to make it more clear we only support ALVar's
          in AssignDeconStmt for now. *)
          let idents = List.map (fun ident -> ALVar(ident)) idents in

          (tc_ctxt, AssignDeconStmt(idents, exp_typechecked))

        | Tuple(types) ->
          let _ =
            if List.length idents == List.length types
              then typecheck_id_typ_pairs idents types
              else failwith "Mismatch in number of idents vs tuple expr in assi"
          in

          (* TODO: This is a hack to make it more clear we only support ALVar's
          in AssignDeconStmt for now. *)
          let idents = List.map (fun ident -> ALVar(ident)) idents in

          (tc_ctxt, AssignDeconStmt(idents, exp_typechecked))

        | _ -> failwith "Cannot deconstruct non-aggregate type into ids"
      end

  | ExprStmt(exp) -> (tc_ctxt, ExprStmt(type_check_expr tc_ctxt Undecided exp))

  | ReturnStmt(exp) ->
      let exp_typechecked = type_check_expr tc_ctxt tc_ctxt.ret_t exp in
      let exp_t = expr_type exp_typechecked in
      let ret_tuple = begin match tc_ctxt.ret_t with
        | Undecided ->
            let ret_t_candidates_up = exp_t :: tc_ctxt.ret_t_candidates in
            let tc_ctxt_up = {
              tc_ctxt with ret_t_candidates = ret_t_candidates_up
            } in
            (tc_ctxt_up, ReturnStmt(exp_typechecked))
        | _ ->
            if type_convertible_to exp_t tc_ctxt.ret_t
              then (tc_ctxt, ReturnStmt(exp_typechecked))
              else failwith "Expr for return does not typecheck with func ret_t"
      end in

      ret_tuple

and type_check_stmts tc_ctxt stmts =
  match stmts with
  | [] -> (tc_ctxt, [])
  | x::xs ->
      let (tc_ctxt_updated, stmt_tced) = type_check_stmt tc_ctxt x in
      let (tc_ctxt_final, stmts_tced) = type_check_stmts tc_ctxt_updated xs in
      (tc_ctxt_final, stmt_tced :: stmts_tced)

(* Given a list of expressions, attempt to collapse/"unify" the types each
expression claims to have, with the expectation that they all ultimately agree
with each other, with respect to type variable mappings. *)
and collapse_expr_type_alternates_n tc_ctxt expr_lst =
  let expr_t_lst = List.map expr_type expr_lst in
  let expr_t_2_tuples = list_to_2_tuples expr_t_lst in
  let (tvars_to_types, _) =
    List.fold_left_map (
      fun map_so_far (lhs_t, rhs_t) ->
        let map_up = map_tvars_to_types ~init_map:map_so_far lhs_t rhs_t in
        (map_up, ())
    ) StrMap.empty expr_t_2_tuples
  in
  let expr_t_concretified_lst =
    List.map (concretify_unbound_types tvars_to_types) expr_t_lst
  in
  let agreement_candidate_t = common_type_of_lst expr_t_concretified_lst in

  let expr_resolved_injected_lst =
    List.map (inject_type_into_expr agreement_candidate_t) expr_lst
  in

  let expr_resolved_lst =
    List.map (type_check_expr tc_ctxt agreement_candidate_t) expr_resolved_injected_lst
  in

  let expr_t_resolved_lst = List.map expr_type expr_resolved_injected_lst in

  let agreement_t = common_type_of_lst expr_t_resolved_lst in

  (
    agreement_t,
    expr_resolved_lst
  )

and collapse_expr_type_alternates_2 tc_ctxt lhs_expr rhs_expr =
  let (agreement_t, collapsed) =
    collapse_expr_type_alternates_n tc_ctxt [lhs_expr; rhs_expr]
  in
  match collapsed with
  | [lhs_expr_collapsed; rhs_expr_collapsed] ->
    (
      agreement_t,
      lhs_expr_collapsed,
      rhs_expr_collapsed
    )
  | _ -> failwith "Collapse did not yield same-size list on output"


(* expected_t is what type the expression is expected to evaluate to. We
normally don't care about this, because the stmt-level typecheck will ensure the
expression is the right type. However, in cases of eg variants/structs that
might have type variables that the expression cannot infer, this information
can provide the needed type info. *)
and type_check_expr
  (tc_ctxt : typecheck_context) (expected_t : berk_t) (exp : expr)
=
  let rec _type_check_expr exp =
    begin match exp with
    | ValNil -> ValNil

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

    | ValStr(s) -> ValStr(s)

    (* If our generic int type is not yet _any_ inferred/default type, determine
    one now with the information we have. This may change later, if we have more
    specific information with which we can better infer a type.

    NOTE: We never wholesale replace ValInt with a more specific type; we
    want it to remain fluid in case we can make a better inference later. *)
    | ValInt(Undecided, i) ->
        begin match expected_t with
        (* Barring more specific information, default to reasonable int type. *)
        | Undecided -> ValInt(I32, i)

        | I64 | I32 | I16 | I8 -> ValInt(expected_t, i)
        | U64 | U32 | U16 | U8 ->
            if i >= 0 then
              ValInt(expected_t, i)
            else
              failwith (
                Printf.sprintf
                  "Unexpectedly expecting uint type [%s] for int [%d]."
                  (fmt_type expected_t)
                  i
              )

        | _ ->
            failwith (
              Printf.sprintf
                "Unexpectedly expecting non-integral type [%s] for int [%d]."
                (fmt_type expected_t)
                i
            )
        end

    (* We have _a_ type for our generic int, so keep it. This may be changed
    later if we get more information leading to a better inference. *)
    | ValInt(_, _) -> exp

    | ValVar(_, id) ->
        let (var_t, _) =
          try StrMap.find id tc_ctxt.vars
          with Not_found ->
            failwith (Printf.sprintf "No variable [%s] in scope" id)
        in
        ValVar(var_t, id)

    | ValFunc(_, func_name) ->
        let {f_params; f_ret_t; _} =
          StrMap.find func_name tc_ctxt.mod_ctxt.func_sigs
        in
        let f_param_t_lst = List.map (fun (_, _, t) -> t) f_params in
        let func_t = Function(f_ret_t, f_param_t_lst) in

        ValFunc(func_t, func_name)

    | ValName(_, name) ->
        (* "Generic variable" lookup first searches for actual in-scope named
        variables, and if that fails, searches for functions of the same name,
        yielding a function pointer. *)
        begin
          try
            let (var_t, _) = StrMap.find name tc_ctxt.vars in
            ValVar(var_t, name)
          with Not_found ->
          try
            begin
              let {f_params; f_ret_t; _} =
                StrMap.find name tc_ctxt.mod_ctxt.func_sigs
              in
              let f_param_t_lst = List.map (fun (_, _, t) -> t) f_params in
              let func_t = Function(f_ret_t, f_param_t_lst) in
              ValFunc(func_t, name)
            end
          with Not_found ->
            failwith
              (Printf.sprintf "No variable or function [%s] in scope" name)
        end

    | ValRawArray(t) -> ValRawArray(t)

    | ValCastTrunc(target_t, exp) ->
        let exp_typechecked = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in
        if type_truncatable_to exp_t target_t
          then ValCastTrunc(target_t, exp_typechecked)
          else failwith "Cannot truncate-cast incompatible types"

    | ValCastBitwise(target_t, exp) ->
        let exp_typechecked = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in
        if type_bitwise_to exp_t target_t
          then ValCastBitwise(target_t, exp_typechecked)
          else failwith "Cannot bitwise-cast incompatible types"

    | ValCastExtend(target_t, exp) ->
        let exp_typechecked = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in
        if type_extendable_to exp_t target_t
          then ValCastExtend(target_t, exp_typechecked)
          else failwith "Cannot extend incompatible types"

    | BinOp(_, op, lhs, rhs) ->
        let lhs_typechecked = _type_check_expr lhs in
        let rhs_typechecked = _type_check_expr rhs in

        (* In the event we have a concrete type for one side, but a generic type
        for the other (even one that we may have already assigned a tentative
        type for; these tentative types are permitted to be overridden if we
        have a better inference), we can fairly infer they should be the same
        type. *)
        let (lhs_typechecked, rhs_typechecked) =
          begin match (lhs_typechecked, rhs_typechecked) with
          (* We can't infer anything if they're both generic ints. *)
          | (ValInt(_, _), ValInt(_, _)) -> (lhs_typechecked, rhs_typechecked)

          | (ValInt(lhs_t, ln), rhs_typechecked) ->
              let rhs_t = expr_type rhs_typechecked in
              begin match (lhs_t, rhs_t) with
              (* Other side doesn't have concrete type yet, can't improve. *)
              | (_, Undecided) -> (lhs_typechecked, rhs_typechecked)
              (* Assume the other side concrete type is better inference. *)
              | (_, _) -> (ValInt(rhs_t, ln), rhs_typechecked)
              end

          | (lhs_typechecked, ValInt(rhs_t, rn)) ->
              let lhs_t = expr_type lhs_typechecked in
              begin match (lhs_t, rhs_t) with
              (* Other side doesn't have concrete type yet, can't improve. *)
              | (Undecided, _) -> (lhs_typechecked, rhs_typechecked)
              (* Assume the other side concrete type is better inference. *)
              | (_, _) -> (lhs_typechecked, ValInt(lhs_t, rn))
              end

          | _ -> (lhs_typechecked, rhs_typechecked)
          end
        in

        (* Double check that we didn't just break assumptions. *)
        let lhs_typechecked = _type_check_expr lhs_typechecked in
        let rhs_typechecked = _type_check_expr rhs_typechecked in

        begin match op with
        | Add | Sub | Mul | Div | Mod ->
            let lhs_t = expr_type lhs_typechecked in
            let rhs_t = expr_type rhs_typechecked in
            let common_t = common_type_of_lr lhs_t rhs_t in
            BinOp(common_t, op, lhs_typechecked, rhs_typechecked)

        | Eq | Ne | Lt | Le | Gt | Ge ->
            (* TODO: There should be an additional check that these are actually
            comparable, as relevant. *)
            BinOp(Bool, op, lhs_typechecked, rhs_typechecked)
        end

    | BlockExpr(_, stmts, exp) ->
        let (tc_ctxt_up, stmts_typechecked) = type_check_stmts tc_ctxt stmts in

        let expr_typechecked = type_check_expr tc_ctxt_up expected_t exp in
        let expr_t = expr_type expr_typechecked in

        BlockExpr(expr_t, stmts_typechecked, expr_typechecked)

    | IfThenElseExpr(_, if_cond, then_expr, else_expr) ->
        let if_cond_typechecked = _type_check_expr if_cond in
        let if_cond_t = expr_type if_cond_typechecked in

        let _ = match if_cond_t with
        | Bool -> ()
        | _ -> failwith "if-expr condition must resolve to Bool"
        in

        let then_expr_typechecked = _type_check_expr then_expr in
        let else_expr_typechecked = _type_check_expr else_expr in

        let then_expr_t = expr_type then_expr_typechecked in
        let else_expr_t = expr_type else_expr_typechecked in

        let then_else_agreement_t = common_type_of_lr then_expr_t else_expr_t in

        IfThenElseExpr(
          then_else_agreement_t,
          if_cond_typechecked,
          then_expr_typechecked,
          else_expr_typechecked
        )

    | WhileExpr(_, init_stmts, while_cond, then_stmts) ->
        (* NOTE: We keep the returned tc_ctxt for typechecking the init-stmts,
        as any declared variables in the init-stmts remain in scope for the
        while expr and body of the while. *)
        let (tc_ctxt, init_stmts_typechecked) =
          type_check_stmts tc_ctxt init_stmts
        in

        (* We call the top-level `type_check_expr`, and not `_type_check_expr`,
        because we want to use the tc_ctxt returned by typechecking the
        init-stmts, because we want visibility into any in-scope init-stmt vars.
        *)
        let while_cond_typechecked =
          type_check_expr tc_ctxt expected_t while_cond
        in
        let while_cond_t = expr_type while_cond_typechecked in

        let (_, then_stmts_typechecked) =
          type_check_stmts tc_ctxt then_stmts
        in

        let _ = match while_cond_t with
        | Bool -> ()
        | _ -> failwith "if-expr condition must resolve to Bool"
        in

        WhileExpr(
          Nil,
          init_stmts_typechecked,
          while_cond_typechecked,
          then_stmts_typechecked
        )

    | FuncCall(_, f_name, exprs) ->
        let {f_name; f_params; f_ret_t} =
          StrMap.find f_name tc_ctxt.mod_ctxt.func_sigs
        in
        let (params_non_variadic_t_lst, is_var_arg) =
          get_static_f_params f_params
        in

        let params_t_lst_padded = begin
            let len_diff =
              (List.length exprs) - (List.length params_non_variadic_t_lst)
            in
            if len_diff = 0 then
              params_non_variadic_t_lst
            else if len_diff > 0 then
              let padding = List.init len_diff (fun _ -> Undecided) in
              params_non_variadic_t_lst @ padding
            else
              failwith "Unexpected shorter expr list than non-variadic params"
          end
        in

        let exprs_typechecked =
          List.map2 (type_check_expr tc_ctxt) params_t_lst_padded exprs
        in
        let exprs_t = List.map expr_type exprs_typechecked in

        let cmp_non_variadic_params_to_exprs =
          List.compare_lengths params_non_variadic_t_lst exprs_t
        in
        let _ =
          if (
            is_var_arg && (cmp_non_variadic_params_to_exprs <= 0)
          ) || (
            cmp_non_variadic_params_to_exprs = 0
          )
          then ()
          else failwith
            "Func call args must not be less than num non-variadic func params"
        in

        let exprs_t_non_variadic =
          take exprs_t (List.length params_non_variadic_t_lst)
        in

        let _ = List.iter2 (
          fun expr_t param_t ->
            if type_convertible_to expr_t param_t
            then ()
            else failwith "Could not convert expr type to arg type"
        ) exprs_t_non_variadic params_non_variadic_t_lst in

        FuncCall(f_ret_t, f_name, exprs_typechecked)

    | ExprInvoke(_, func_exp, exprs) ->
        let func_exp_typechecked = _type_check_expr func_exp in
        let func_t = expr_type func_exp_typechecked in

        let (ret_t, f_fake_params) = begin match func_t with
          | Function(ret_t, args_t_lst) ->
              let f_fake_params =
                List.map (fun arg_t -> ((), (), arg_t)) args_t_lst
              in
              (ret_t, f_fake_params)
          | _ -> failwith "Invocable unexpectedly contains non-function type"
        end in

        let (params_non_variadic_t_lst, is_var_arg) =
          get_static_f_params f_fake_params
        in

        let params_t_lst_padded = begin
            let len_diff =
              (List.length exprs) - (List.length params_non_variadic_t_lst)
            in
            if len_diff = 0 then
              params_non_variadic_t_lst
            else if len_diff > 0 then
              let padding = List.init len_diff (fun _ -> Undecided) in
              params_non_variadic_t_lst @ padding
            else
              failwith "Unexpected shorter expr list than non-variadic params"
          end
        in

        let exprs_typechecked =
          List.map2 (type_check_expr tc_ctxt) params_t_lst_padded exprs
        in
        let exprs_t = List.map expr_type exprs_typechecked in

        let cmp_non_variadic_params_to_exprs =
          List.compare_lengths params_non_variadic_t_lst exprs_t
        in
        let _ =
          if (
            is_var_arg && (cmp_non_variadic_params_to_exprs <= 0)
          ) || (
            cmp_non_variadic_params_to_exprs = 0
          )
          then ()
          else failwith
            "Func call args must not be less than num non-variadic func params"
        in

        let exprs_t_non_variadic =
          take exprs_t (List.length params_non_variadic_t_lst)
        in

        let _ = List.iter2 (
          fun expr_t param_t ->
            if type_convertible_to expr_t param_t
            then ()
            else failwith "Could not convert expr type to arg type"
        ) exprs_t_non_variadic params_non_variadic_t_lst in

        ExprInvoke(ret_t, func_exp_typechecked, exprs_typechecked)

    | ArrayExpr(_, exprs) ->
        let elem_expected_t = begin match expected_t with
          | Array(elem_t, _) -> elem_t
          | Undecided -> Undecided
          | _ -> failwith "Unexpectedly expecting non-array type in array expr"
        end in

        let exprs_typechecked =
          List.map (type_check_expr tc_ctxt elem_expected_t) exprs
        in
        let expr_t_lst = List.map expr_type exprs_typechecked in
        let common_t = common_type_of_lst expr_t_lst in
        let arr_t = Array(common_t, List.length exprs) in

        ArrayExpr(arr_t, exprs_typechecked)

    | IndexExpr(_, idx, arr) ->
        let idx_typechecked = type_check_expr tc_ctxt Undecided idx in
        let arr_typechecked = _type_check_expr arr in
        let idx_t = expr_type idx_typechecked in
        let arr_t = expr_type arr_typechecked in
        if is_index_type idx_t && is_indexable_type arr_t
          then
            begin match arr_t with
            | Array(elem_typ, sz) ->
                begin match idx_typechecked with
                | ValI64(i) | ValI32(i) | ValI16(i) | ValI8(i)
                | ValU64(i) | ValU32(i) | ValU16(i) | ValU8(i) ->
                    if i < sz then
                      IndexExpr(
                        elem_typ, idx_typechecked, arr_typechecked
                      )
                    else
                      failwith "Static out-of-bounds index into array"
                | _ ->
                    IndexExpr(
                      elem_typ, idx_typechecked, arr_typechecked
                    )
                end

            | _ -> failwith "Unexpected index target in index expr"
            end
          else
            failwith (
              Printf.sprintf
                "Unexpected components of index operation: [%s] [%s]"
                (fmt_expr ~print_typ:true "" arr_typechecked)
                (fmt_expr ~print_typ:true "" idx_typechecked)
            )

    | StaticIndexExpr(_, idx, agg) ->
        let agg_typechecked = _type_check_expr agg in
        let agg_t = expr_type agg_typechecked in
        let static_idx_typechecked = begin
          match agg_t with
          | Tuple(ts) ->
            begin
              if idx < 0 || idx >= List.length ts
              then failwith "out-of-bounds idx for tuple"
              else
                let elem_typ = List.nth ts idx in
                StaticIndexExpr(elem_typ, idx, agg_typechecked)
            end
          | _ -> failwith "Unexpectedly indexing into non-aggregate"
        end in

        static_idx_typechecked

    | TupleExpr(_, exprs) ->
        let elem_expected_t_lst = begin match expected_t with
          | Tuple(typs) -> typs
          | Undecided ->
              let tuple_len = List.length exprs in
              List.init tuple_len (fun _ -> Undecided)
          | _ ->
              failwith (
                "Unexpectedly expecting non-tuple type in tuple expr: " ^
                (fmt_type expected_t)
              )
        end in

        let exprs_typechecked =
          List.map2 (type_check_expr tc_ctxt) elem_expected_t_lst exprs
        in
        let exprs_t_lst = List.map expr_type exprs_typechecked in
        let tuple_t = Tuple(exprs_t_lst) in

        TupleExpr(tuple_t, exprs_typechecked)

    | VariantCtorExpr(_, ctor_name, ctor_exp) ->
        let ctor_exp_expected_t = begin match expected_t with
          | Undecided -> Undecided
          | Variant(_, ctors) ->
              let (_, ctor_exp_t) = List.find (
                  fun (name, _) -> name = ctor_name
                ) ctors
              in
              ctor_exp_t
          | _ ->
              failwith (
                "Unexpectedly expecting non-variant type in " ^
                "variant expression: " ^ (fmt_type expected_t)
              )
        end in

        let ctor_exp_typechecked =
          type_check_expr tc_ctxt ctor_exp_expected_t ctor_exp
        in
        let ctor_exp_typ = expr_type ctor_exp_typechecked in
        let resolved_v_t : berk_t =
          variant_ctor_to_variant_type tc_ctxt.mod_ctxt ctor_name ctor_exp_typ
        in

        VariantCtorExpr(resolved_v_t, ctor_name, ctor_exp_typechecked)

    | MatchExpr(_, matched_expr, pattern_expr_pairs) ->
        let matched_expr_tc = _type_check_expr matched_expr in
        let matched_t = expr_type matched_expr_tc in

        let typecheck_pattern_expr_pair (patt, exp) =
          let (tc_ctxt, patt_tc) = type_check_pattern tc_ctxt matched_t patt in
          let exp_tc = type_check_expr tc_ctxt Undecided exp in

          (patt_tc, exp_tc)
        in

        let pattern_expr_pairs_tc =
          List.map typecheck_pattern_expr_pair pattern_expr_pairs
        in

        let patts = List.map (fun (patt, _) -> patt) pattern_expr_pairs_tc in

        let _ = check_patt_usefulness_exhaustion patts matched_t in

        let common_t = common_type_of_lst (
          List.map (fun (_, exp) -> expr_type exp) pattern_expr_pairs_tc
        ) in

        MatchExpr(common_t, matched_expr_tc, pattern_expr_pairs_tc)
    end
  in

  (* First, allow the typechecker to try to infer types as much as possible. *)
  let exp_typechecked = _type_check_expr exp in
  let exp_typechecked_t = expr_type exp_typechecked in

  (* If we were given an explicit type that the expression must match, then we
  inject that type back into the expression, which may implicitly promote
  relevant types. Since the explicit type may still not be complete (unspecified
  type vars, we try to roll in the information we have from the bottom-up
  typecheck as well.)

  If we were not given an explicit type, we inject the type the typechecker
  inferred, as this will normalize/promote various types as necessary in
  possibly-misaligned branches within the expression (eg, if-expr) *)
  let inject_t = begin match expected_t with
    | Undecided -> exp_typechecked_t
    | _ ->
        let inject_t = begin
          (* If the expected type is concrete, that should be all we need. If
          injecting this type doesn't typecheck, then the user needs to
          re-assess their explicit type declaration or what they expect the
          expression to evaluate to. *)
          if is_concrete_type expected_t then
            expected_t

          (* If the expected type is not concrete, then maybe the inferred type
          has enough information to create an overall-concrete, or
          more-concrete, type. *)
          else
            let tvars_to_t = map_tvars_to_types expected_t exp_typechecked_t in
            let concrete_t = concretify_unbound_types tvars_to_t expected_t in

            concrete_t
        end in
        inject_t
  end in

  (* Inject the evaluated type back into the expression, which can in particular
  be helpful to normalize types between alternate branches in expressions like
  if-expr. *)
  let exp_typechecked_injected =
    inject_type_into_expr inject_t exp_typechecked
  in

  exp_typechecked_injected

(* The infrastructure below to typecheck/exhaustion check/usefulness check match
patterns is inefficient and does not adhere to modern developments in
efficiently implementing these kinds of checks. This implementation should be
refactored to respect those developments. See also:

http://cambium.inria.fr/~maranget/papers/warn/index.html
*)

and type_check_pattern
  (tc_ctxt : typecheck_context) (matched_t : berk_t) (patt : pattern) :
  typecheck_context * pattern
=
  let (tc_ctxt, patt) = begin match patt with
  | PNil -> (tc_ctxt, PNil)

  | Wild(_) ->
      (tc_ctxt, Wild(matched_t))

  | VarBind(_, varname) ->
      let tc_ctxt = {
        tc_ctxt with
          vars = add_uniq_varname varname (matched_t, {mut=false}) tc_ctxt.vars
      } in

      (tc_ctxt, VarBind(matched_t, varname))

  | PBool(b) ->
      begin match matched_t with
      | Bool -> (tc_ctxt, PBool(b))
      | _ -> failwith "Match expression type does not match bool in pattern"
      end

  | PTuple(_, patts) ->
      begin match matched_t with
      | Tuple(ts) ->
          let (tc_ctxt, patts_tc_rev) =
            List.fold_left2 (
              fun (tc_ctxt, patts_tc_so_far_rev) t patt ->
                let (tc_ctxt, patt_tc) = type_check_pattern tc_ctxt t patt in

                (tc_ctxt, patt_tc :: patts_tc_so_far_rev)
            ) (tc_ctxt, []) ts patts
          in

          let patts_tc = List.rev patts_tc_rev in

          (tc_ctxt, PTuple(matched_t, patts_tc))

      | _ -> failwith "Match expression type does not match bool in pattern"
      end

  | Ctor(_, ctor_name, exp_patt) ->
      let ctor_exp_t = begin match matched_t with
      | Variant(_, ctors) ->
          (* TODO: This will just fail if the ctor_name does not match. We
            should have a nicer error message here (ie, "wrong variant") *)
          let (_, ctor_exp_t) = List.find (
              fun (name, _) -> ctor_name = name
            ) ctors
          in
          ctor_exp_t
      | _ ->
          failwith (
            "Unexpectedly expecting non-variant type in " ^
            "variant constructor match: " ^ (fmt_type matched_t)
          )
      end in

      let (tc_ctxt, exp_patt) =
        type_check_pattern tc_ctxt ctor_exp_t exp_patt
      in

      (tc_ctxt, Ctor(matched_t, ctor_name, exp_patt))

  | PatternAs(_, patt, varname) ->
      let (tc_ctxt, patt_typechecked) =
        type_check_pattern tc_ctxt matched_t patt
      in

      let tc_ctxt = {
        tc_ctxt with
          vars = add_uniq_varname varname (matched_t, {mut=false}) tc_ctxt.vars
      } in

      (tc_ctxt, PatternAs(matched_t, patt_typechecked, varname))
  end in

  (tc_ctxt, patt)

(* Does the LHS pattern dominate the RHS pattern? *)
and pattern_dominates lhs_patt rhs_patt =
  begin match (lhs_patt, rhs_patt) with
  | ((Wild(_) | VarBind(_, _)), _) -> true

  | (_, (Wild(_) | VarBind(_, _))) ->
      Printf.printf "No pattern dominates wildcards other than wildcards.\n" ;
      false

  | (PNil, PNil) -> true

  | (PBool(lhs_b), PBool(rhs_b)) ->
      if lhs_b = rhs_b then
        true
      else
        false

  | (PTuple(_, lhs_patts), PTuple(_, rhs_patts)) ->
      List.fold_left (&&) true (
        List.map2 pattern_dominates lhs_patts rhs_patts
      )

  | (Ctor(_, lhs_ctor_name, lhs_patt), Ctor(_, rhs_ctor_name, rhs_patt)) ->
      if lhs_ctor_name = rhs_ctor_name then
        pattern_dominates lhs_patt rhs_patt
      else
        false

  | (PatternAs(_, lhs_patt, _), PatternAs(_, rhs_patt, _)) ->
      pattern_dominates lhs_patt rhs_patt

  | (PatternAs(_, lhs_patt, _), rhs_patt) ->
      pattern_dominates lhs_patt rhs_patt

  | (PNil, _)
  | (PBool(_), _)
  | (PTuple(_, _), _)
  | (Ctor(_, _, _), _) -> failwith "Non-matching pattern types."

  end

and filter_dominated lhs_patt rhs_patts =
  List.filter (fun rhs -> not (pattern_dominates lhs_patt rhs)) rhs_patts

(* Returns a pair. The left list is the list of patterns that are useless
because the patterns before them are sufficient to match all pattern values, and
the right list is the list of pattern values not matched by any pattern (lacking
exhaustion). *)
and determine_pattern_completeness lhs_patts rhs_patts =
  let rec _determine_pattern_completeness lhs_patts_useless lhs_patts_rest rhs_patts_rest =
    begin match (lhs_patts_rest, rhs_patts_rest) with
    | ([], []) -> ((List.rev lhs_patts_useless), [])
    | (_, []) -> ((List.rev lhs_patts_useless) @ lhs_patts_rest, [])
    | ([], _) -> ((List.rev lhs_patts_useless), rhs_patts_rest)
    | (patt::lhs_patts_rest, _) ->
        (* Non-exhaustion of patterns is when there are remaining pattern values
        after exhausting all match pattern arms. *)
        let filtered_rhs_patts = filter_dominated patt rhs_patts_rest in
        (* Useless patterns are patterns that did not dominate any of the
        remaining pattern values. *)
        let lhs_patts_useless =
          if (List.length rhs_patts_rest) = (List.length filtered_rhs_patts)
          then patt :: lhs_patts_useless
          else lhs_patts_useless
        in
        _determine_pattern_completeness
          lhs_patts_useless lhs_patts_rest filtered_rhs_patts
    end
  in

  _determine_pattern_completeness [] lhs_patts rhs_patts

(* This function generates, essentially, the list of all possible permutations
of pattern values implied by the given type. *)
and generate_value_patts t : pattern list =
  match t with
  | Undecided -> failwith "Cannot generate values for undecided type"
  | Unbound(_) -> failwith "Cannot generate values for unbound typevar"
  | VarArgSentinel -> failwith "Cannot generate values for var-arg sentinel"

  | Nil -> [PNil]

  | U64 | U32 | U16 | U8
  | I64 | I32 | I16 | I8 -> failwith "Unimplemented"

  | F128 | F64 | F32 -> failwith "Unimplemented"

  | String -> failwith "Unimplemented"

  | Array(_, _) -> failwith "Unimplemented"

  | Tuple(ts) ->
      let ts_patts = List.map generate_value_patts ts in
      let ts_patts_cart_prod = cartesian_product ts_patts in
      List.map (fun ts_patt -> PTuple(t, ts_patt)) ts_patts_cart_prod

  | Ptr(_) -> failwith "Unimplemented"
  | ByteArray(_) -> failwith "Unimplemented"
  | Function(_, _) -> failwith "Unimplemented"

  | Bool -> [PBool(true); PBool(false)]

  | Variant(_, ctors) ->
      let ctor_patt_chunks : pattern list list =
        List.map (
          fun (ctor_name, ctor_t) ->
            let ctor_value_patts = generate_value_patts ctor_t in
            let ctor_patts =
              List.map (
                fun value_patt -> Ctor(t, ctor_name, value_patt)
              ) ctor_value_patts
            in
            ctor_patts
        ) ctors
      in
      List.flatten ctor_patt_chunks

and check_patt_usefulness_exhaustion lhs_patts t =
  let rhs_value_patts = generate_value_patts t in
  let (useless_lhs, unmatched_rhs) =
    determine_pattern_completeness lhs_patts rhs_value_patts
  in
  match (useless_lhs, unmatched_rhs) with
  | ([], []) -> ()
  | (useless, []) ->
      let useless_fmt =
        fmt_join_strs "\n" (
          List.map (fmt_pattern ~print_typ:false "") useless
        )
      in
      Printf.printf "Useless LHS pattern(s):\n%s\n%!" useless_fmt ;
      failwith "Match patterns must all be useful."

  | ([], unmatched) ->
      let unmatched_fmt =
        fmt_join_strs "\n" (
          List.map (fmt_pattern ~print_typ:false "") unmatched
        )
      in
      Printf.printf "Unmatched pattern value(s):\n%s\n%!" unmatched_fmt ;
      failwith "Match patterns must be exhaustive."

  | (_, _) ->
      failwith (
        "Unexpectedly both useless LHS pattern and unmatched RHS pattern value"
      )
