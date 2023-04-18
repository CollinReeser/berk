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

let fmt_variants_map variants =
  let variant_names_to_decls = StrMap.bindings variants in
  let variants_fmt =
    List.map (
      fun (_, v_decl) -> fmt_variant_decl v_decl
    ) variant_names_to_decls
  in
  fmt_join_strs ", " variants_fmt
;;

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


(* If the given type is an unbound type (some user-defined type), then try to
yield the more concrete type known by that name. *)
let rec bind_type mod_ctxt t =
  begin match t with
  | UnboundType(name, ts) ->
      let {v_name=v_name; v_ctors=v_ctors; v_typ_vars=v_typ_vars} as v_decl =
        begin match (StrMap.find_opt name mod_ctxt.variants) with
        | Some(t) -> t
        | None ->
            failwith (
              Printf.sprintf "No known type with name [%s]" name
            )
        end
      in

      Printf.printf "Variant decl: [%s]\n%!" (fmt_variant_decl v_decl);

      let bound_v_ctors = List.map (bind_v_ctor mod_ctxt) v_ctors in
      let variant_t = Variant(v_name, bound_v_ctors) in

      Printf.printf "Variant type: [%s]\n%!" (fmt_type variant_t);

      let tvars_to_ts =
        begin if List.length v_typ_vars = List.length ts then
          List.fold_left2 (
            fun tvars_to_ts v_typ_var t ->
              StrMap.add v_typ_var t tvars_to_ts
          ) StrMap.empty v_typ_vars ts
        else
          failwith (
            Printf.sprintf
              (
                "Type name [%s] matches [%s] but mismatch in instantiation " ^^
                "types <%s> vs expected typevars <%s>"
              )
              name
              (fmt_type variant_t)
              (fmt_join_types ~pretty_unbound:true ", " ts)
              (fmt_join_strs ", " v_typ_vars)
          )
        end
      in

      let concretified_variant_t =
        concretify_unbound_types tvars_to_ts variant_t
      in

      Printf.printf "Variant type (concrete): [%s]\n%!" (fmt_type concretified_variant_t);

      concretified_variant_t

  | _ -> t
  end

and bind_v_ctor mod_ctxt {name; fields} =
  let bound_fields =
    List.map (
      fun {t} ->
        let bind_t = bind_type mod_ctxt t in
        {t=bind_t}
    ) fields
  in
  {name; fields=bound_fields}
;;


(* Given a statement/expression, return true if all involved types are
concretely bound/decided, false otherwise. *)

let rec is_concrete_stmt ?(verbose=false) stmt =
  let _is_concrete_expr expr = is_concrete_expr ~verbose:verbose expr in
  let _is_concrete_type typ  = is_concrete_type ~verbose:verbose typ in

  let res = begin match stmt with
  | ExprStmt(expr)
  | ReturnStmt(expr)
  | AssignStmt(_, _, expr) ->
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
  | ValF128(_) | ValF64(_) | ValF32(_)
  | ValBool(_)
  | ValStr(_)
  | ValNil -> true

  | ValInt(typ, _) -> _is_concrete_type typ

  | ValVar(typ, _)
  | ValFunc(typ, _)
  | ValName(typ, _) -> _is_concrete_type typ

  | ValRawArray(typ) -> _is_concrete_type typ

  | ValCast(typ, _, expr)
  | UnOp(typ, _, expr)
  | TupleIndexExpr(typ, _, expr) ->
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
  | FuncCall(typ, _, exprs)
  | VariantCtorExpr(typ, _, exprs) ->
      (_is_concrete_type typ) &&
        (List.fold_left (&&) true (List.map _is_concrete_expr exprs))

  | UfcsCall(typ, exp, _, exprs) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr exp) &&
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
        (fmt_expr ~print_typ:true expr)
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
  | Ctor(t, _, patts) ->
      let is_concrete_t = _is_concrete_type t in
      let each_concrete_patt = List.map _is_concrete_patt patts in
      let all_concrete_patts = List.fold_left (&&) true each_concrete_patt in
      is_concrete_t && all_concrete_patts
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
let variant_ctor_to_variant_type ?(disambiguator = "") mod_ctxt ctor =
  (* Get all variant declarations that seem to match the given constructor. *)
  let matching_variants =
    StrMap.filter (
      fun variant_name v_decl_t ->
        if disambiguator = ""
        then v_decl_has_ctor v_decl_t ctor
        else variant_name = disambiguator && v_decl_has_ctor v_decl_t ctor
    ) mod_ctxt.variants
  in

  (* If there was exactly one matching variant declaration, then generate a
  variant _type_ that reflects that declaration. Else, fail. *)
  begin if StrMap.cardinal matching_variants = 1 then
    (* Take the one variant-name -> variant-decl binding there is. *)
    let (_, matching_variant_t) = StrMap.choose matching_variants in
    variant_decl_to_variant_type matching_variant_t ctor

  else if StrMap.cardinal matching_variants = 0 then
    failwith (
      Printf.sprintf "No matching variants for ctor [%s] among [%s]"
        (fmt_v_ctor ctor)
        (fmt_variants_map mod_ctxt.variants)
    )
  else
    failwith (
      "Disambiguator " ^ disambiguator ^
      " yielded multiple matching variants"
    )
  end
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
      let {f_name; f_params; f_ret_t} = f_decl_ast in
      let _ = match (StrMap.find_opt f_name mod_ctxt.func_sigs) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of func " ^ f_name)
      in

      (* If the return type is a user-defined type, bind it now. *)
      let f_ret_t = bind_type mod_ctxt f_ret_t in
      let f_decl_ast = {f_name; f_params; f_ret_t} in

      if not (confirm_at_most_trailing_var_arg f_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let func_sigs_up = begin
          StrMap.add f_name {f_name; f_params; f_ret_t} mod_ctxt.func_sigs
        end in
        let mod_ctxt_up = {mod_ctxt with func_sigs = func_sigs_up} in

        (mod_ctxt_up, FuncExternDecl(f_decl_ast))

  | FuncDef(f_ast) ->
      let {f_decl = {f_name; f_params; f_ret_t}; f_stmts} = f_ast in
      let _ = match (StrMap.find_opt f_name mod_ctxt.func_sigs) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of func " ^ f_name)
      in

      (* If the return type is a user-defined type, bind it now. *)
      let f_ret_t = bind_type mod_ctxt f_ret_t in
      let f_ast = {f_decl = {f_name; f_params; f_ret_t}; f_stmts} in

      if not (confirm_at_most_trailing_var_arg f_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let func_sigs_up = begin
          StrMap.add f_name {f_name; f_params; f_ret_t} mod_ctxt.func_sigs
        end in
        let mod_ctxt_up = {mod_ctxt with func_sigs = func_sigs_up} in
        let func_ast_typechecked = type_check_func mod_ctxt_up f_ast in

        (mod_ctxt_up, FuncDef(func_ast_typechecked))

  | VariantDecl({v_name; v_ctors; v_typ_vars}) ->
      let _ = match (StrMap.find_opt v_name mod_ctxt.variants) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of variant " ^ v_name)
      in

      (* If a variant declaration internally refers to other variants (ie,
      as a field of one of the constructors), then we want to resolve that
      field to a concrete type, and use that resolved declaration going
      forward. *)
      let bound_v_ctors = List.map (bind_v_ctor mod_ctxt) v_ctors in
      let bound_v_decl_ast = {v_name; v_ctors=bound_v_ctors; v_typ_vars} in

      let var_t = Variant(v_name, bound_v_ctors) in
      let real_tvars = get_tvars var_t in
      let declared_tvars = List.sort compare v_typ_vars in
      let _ =
        if List.equal (=) real_tvars declared_tvars
        then ()
        else failwith (
            "Actual type vars don't match declared in variant " ^ v_name
          )
      in

      let variants_up = StrMap.add v_name bound_v_decl_ast mod_ctxt.variants in
      let mod_ctxt_up = {mod_ctxt with variants = variants_up} in

      (mod_ctxt_up, VariantDecl(bound_v_decl_ast))

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
      (* If decl_t is an unbound type (some user-defined type we only have
      the name of), then bind it and shadow decl_t with our updated type. *)
      let decl_t = bind_type tc_ctxt.mod_ctxt decl_t in
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
              (fmt_expr ~print_typ:true exp_typechecked)
            in

            failwith msg
          end
      in

      let _ = if not (is_concrete_type resolved_t) then
        failwith (
          Printf.sprintf "Resolved type for `let %s` not concrete: [%s]"
            ident
            (fmt_type ~pretty_unbound:true resolved_t)
        )
      else ()
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

      (* If the declared type is fully concrete, assume we can use that. Else,
      attempt to merge the two types, where success implies they're compatible.
      *)
      let resolved_t =
        begin if is_concrete_type decl_t then
          decl_t
        else
          let merged_t = merge_types decl_t exp_t in
          begin if is_concrete_type merged_t then
            merged_t
          else
            failwith (
              Printf.sprintf
                "Could not reconcile declared vs inferred types: [%s] vs [%s]"
                (fmt_type decl_t) (fmt_type exp_t)
            )
          end
        end
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

  | AssignStmt(ident, lval_idxs, exp) ->
      (* Typecheck the chain of indexing against the named LHS variable, if
      there is any, and yield the type of the resultant target for the
      assignment (as well as the typechecked index expressions). *)
      let apply_index cur_t lval_idx =
        begin match lval_idx with
        | ALStaticIndex(i) ->
            let inner_t = unwrap_aggregate_indexable cur_t i in
            let lval_idx_tc = ALStaticIndex(i) in

            (inner_t, lval_idx_tc)

        | ALIndex(idx_exp) ->
            (* Typecheck the indexing expression itself. *)
            let idx_exp_tc =
              type_check_expr tc_ctxt Undecided idx_exp
            in

            let inner_t =
              if is_indexable_type cur_t then
                unwrap_indexable cur_t
              else
                failwith (
                  Printf.sprintf "Type cannot be indexed: [%s]" (fmt_type cur_t)
                )
            in

            let lval_idx_tc = ALIndex(idx_exp_tc) in

            (inner_t, lval_idx_tc)
        end
      in

      let (var_t, {mut}) = StrMap.find ident tc_ctxt.vars in

      let (lval_t, lval_idxs_typechecked) =
        List.fold_left_map apply_index var_t lval_idxs
      in

      let exp_typechecked = type_check_expr tc_ctxt lval_t exp in
      let exp_t = expr_type exp_typechecked in

      let _ =
        if mut then
          ()
        else
          failwith (
            Printf.sprintf "Cannot assign to immutable var [%s]" ident
          )
      in

      if type_convertible_to exp_t lval_t then
        (tc_ctxt, AssignStmt(ident, lval_idxs_typechecked, exp_typechecked))
      else
        failwith (
          Printf.sprintf "Expr for assignment to [%s] does not typecheck" ident
        )

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

    | ValCast(target_t, op, exp) ->
        let exp_typechecked = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in

        let op_func_check =
          begin match op with
          | Truncate -> type_truncatable_to
          | Bitwise -> type_bitwise_to
          | Extend -> type_extendable_to
          end
        in

        if op_func_check exp_t target_t then
          ValCast(target_t, op, exp_typechecked)
        else
          failwith (
            Printf.sprintf "Cannot [%s] incompatible types" (fmt_cast_op op)
          )

    | UnOp(_, op, exp) ->
        let exp_typechecked = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in

        begin match (op, exp_t) with
        | (LNot, Bool) -> UnOp(exp_t, op, exp_typechecked)
        | _ ->
            failwith (
              Printf.sprintf "Invalid combination of op/type for [%s]/[%s]"
              (fmt_un_op op)
              (fmt_type exp_t)
            )
        end

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

        let lhs_t = expr_type lhs_typechecked in
        let rhs_t = expr_type rhs_typechecked in

        begin match op with
        | Add | Sub | Mul | Div | Mod ->
            let common_t = common_type_of_lr lhs_t rhs_t in
            BinOp(common_t, op, lhs_typechecked, rhs_typechecked)

        | Eq | Ne | Lt | Le | Gt | Ge ->
            (* TODO: There should be an additional check that these are actually
            comparable, as relevant. *)
            BinOp(Bool, op, lhs_typechecked, rhs_typechecked)

        | LOr | LAnd ->
            begin match (lhs_t, rhs_t) with
            | (Bool, Bool) ->
                BinOp(Bool, op, lhs_typechecked, rhs_typechecked)

            | _ ->
                failwith (
                  Printf.sprintf
                    "Cannot logical-and/or on non-bool operands: [%s] vs [%s]"
                    (fmt_type lhs_t) (fmt_type rhs_t)
                )
            end
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

    | UfcsCall(_, exp, f_name, exprs) ->
        let {f_name; f_params; f_ret_t} =
          StrMap.find f_name tc_ctxt.mod_ctxt.func_sigs
        in

        (* For now, a UFCS call is simply a different syntax for a normal
        function call. Later, a UFCS call might also be a method call, where
        we may need to do some additional checking. Unclear yet. *)

        let exprs = exp :: exprs in

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

        (* Rewrite the UFCS call into a normal function call. *)
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
                | ValInt(_, i) ->
                    begin if i < sz && i >= 0 then
                      IndexExpr(
                        elem_typ, idx_typechecked, arr_typechecked
                      )
                    else
                      failwith "Static out-of-bounds index into array"
                    end
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
                (fmt_expr ~print_typ:true arr_typechecked)
                (fmt_expr ~print_typ:true idx_typechecked)
            )

    | TupleIndexExpr(_, idx, agg) ->
        let tuple_typechecked = _type_check_expr agg in
        let tuple_t = expr_type tuple_typechecked in
        let tuple_idx_typechecked = begin
          match tuple_t with
          | Tuple(ts) ->
            begin
              if idx < 0 || idx >= List.length ts
              then failwith "out-of-bounds idx for tuple"
              else
                let elem_typ = List.nth ts idx in
                TupleIndexExpr(elem_typ, idx, tuple_typechecked)
            end
          | _ ->
              failwith (
                Printf.sprintf "Unexpectedly indexing into non-tuple: [%s]"
                  (fmt_type tuple_t)
              )
        end in

        tuple_idx_typechecked

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

    | VariantCtorExpr(_, ctor_name, field_exprs) ->
        (* Get a symmetric list of expected types for each field in the variant
        ctor, based on the input expected type. *)
        let ctor_expected_ts = begin match expected_t with
          | Undecided ->
              List.init (List.length field_exprs) (fun _ -> Undecided)
          | Variant(_, _) ->
              get_v_ctor_fields_ts expected_t ctor_name

          | _ ->
              failwith (
                "Unexpectedly expecting non-variant type in " ^
                "variant expression: " ^ (fmt_type expected_t)
              )
        end in

        let field_exprs_typechecked =
          List.map2 (type_check_expr tc_ctxt) ctor_expected_ts field_exprs
        in
        let field_exprs_ts = List.map expr_type field_exprs_typechecked in

        (* This is a _placeholder_ constructor record, a common denominator
        ctor object, that we can use to try to determine the intended overall
        variant type this ctor-expr is referring to. *)
        let approximate_ctor = build_ctor_from_ts ctor_name field_exprs_ts in

        (* Assuming we were not given an input expected type, what variant type
        would we expect this variant ctor expression to be referring to? *)
        let inferred_v_t : berk_t =
          variant_ctor_to_variant_type tc_ctxt.mod_ctxt approximate_ctor
        in

        (* Ensure that our inferred variant type is at least convertible to
        the input expected type, if there was one, else just take what we
        inferred. *)
        let _ =
          begin match expected_t with
          | Variant(_, _) ->
              begin if type_convertible_to inferred_v_t expected_t then
                ()
              else
                failwith (
                  Printf.sprintf
                    "Expected type [%s] but inferred incompatible type [%s]"
                    (fmt_type expected_t)
                    (fmt_type inferred_v_t)
                )
              end
          | _ ->
              ()
          end
        in

        VariantCtorExpr(inferred_v_t, ctor_name, field_exprs_typechecked)

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
    | Undecided ->
        exp_typechecked_t
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
            (* First, collect the complete mutual set of typevars to concrete
            types, between the declared and inferred types. *)
            let tvars_to_t = map_tvars_to_types expected_t exp_typechecked_t in

            (* Concretify the declared and inferred types as far as possible.

            eg, if the declared type is
              Variant <`a=u32, `b> { | Some(`a=u32) | Other(`b)}
            and the inferred type is
              Variant <`a, `b=bool> { | Some(`a) | Other(`b=bool)}
            then this step will yield the following for both concretified types:
              Variant <`a=u32, `b=bool> { | Some(`a=u32) | Other(`b=bool)}
            *)
            let concrete_expected_t =
              concretify_unbound_types tvars_to_t expected_t
            in
            let concrete_exp_typechecked_t =
              concretify_unbound_types tvars_to_t exp_typechecked_t
            in

            (* Attempt to merge the two types. The concretification steps should
            have ideally eliminated all unbound typevars, but this step ensures
            that if one side is still undecided about a particular part of the
            type, then the other side is used as a reference.

            eg, if the declared type is the tuple `(undecided, bool)`, and the
            inferred type is (u32, bool), then we can merge the two into
            `(u32, bool)`, as opposed to claiming the inferred type is wrong
            because the declared type insists on a partial type. *)
            let merged_t =
              merge_types concrete_expected_t concrete_exp_typechecked_t
            in

            merged_t
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
          let (tc_ctxt, patts_tc) =
            fold_left_map2 type_check_pattern tc_ctxt ts patts
          in

          (tc_ctxt, PTuple(matched_t, patts_tc))

      | _ -> failwith "Match expression type does not match bool in pattern"
      end

  | Ctor(_, ctor_name, exp_patts) ->
      let ctor_fields =
        begin match matched_t with
        | Variant(_, ctors) ->
            (* TODO: This will just fail if the ctor_name does not match. We
              should have a nicer error message here (ie, "wrong variant") *)
            let {fields=ctor_fields; _} = List.find (
                fun {name; _} -> ctor_name = name
              ) ctors
            in
            ctor_fields
        | _ ->
            failwith (
              "Unexpectedly expecting non-variant type in " ^
              "variant constructor match: " ^ (fmt_type matched_t)
            )
        end
      in

      let ctor_fields_ts = List.map (fun {t} -> t) ctor_fields in

      let (tc_ctxt, exp_patts_tc) =
        fold_left_map2 type_check_pattern tc_ctxt ctor_fields_ts exp_patts
      in

      (tc_ctxt, Ctor(matched_t, ctor_name, exp_patts_tc))

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

  | (Ctor(_, lhs_ctor_name, lhs_patts), Ctor(_, rhs_ctor_name, rhs_patts)) ->
      if lhs_ctor_name = rhs_ctor_name then
        let each_dominates = List.map2 pattern_dominates lhs_patts rhs_patts in
        let all_dominates = List.fold_left (&&) true each_dominates in
        all_dominates
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
  | UnboundType(_, _) -> failwith "Cannot generate values for unbound type"
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
          fun {name=ctor_name; fields} ->
            let fields_ts = List.map (fun {t} -> t) fields in
            let fields_ts_patts = List.map generate_value_patts fields_ts in
            let fields_ts_patts_cart_prod = cartesian_product fields_ts_patts in
            let ctor_patts =
              begin match fields_ts_patts_cart_prod with
              | [] -> [Ctor(t, ctor_name, [])]
              | _ ->
                  List.map (
                    fun value_patt -> Ctor(t, ctor_name, value_patt)
                  ) fields_ts_patts_cart_prod
              end
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
