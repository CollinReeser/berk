open Ast
open Ir
open Template
open Typing
open Utility

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)

type module_context = {
  func_sigs: func_decl_t StrMap.t;
  func_templates: module_decl StrMap.t;
  generator_sigs: generator_decl_t StrMap.t;
  variants: variant_decl_t StrMap.t;
}

let default_mod_ctxt = {
  func_sigs = StrMap.empty;
  func_templates = StrMap.empty;
  generator_sigs = StrMap.empty;
  variants = StrMap.empty;
}

type typecheck_context = {
  vars: (berk_t * var_qual) StrMap.t;
  yield_t: berk_t;
  ret_t: berk_t;
  yield_t_candidates: berk_t list;
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
  yield_t = Nil;
  ret_t = typ;
  yield_t_candidates = [];
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

      (* Replace type variables with concrete types in the variant. *)
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
  | ExprStmt(_, expr)
  | YieldStmt(expr)
  | ReturnStmt(expr)
  | AssignStmt(_, _, _, expr) ->
      _is_concrete_expr expr

  | DeclStmt(_, _, typ, expr)
  | DeclDeconStmt(_, typ, expr) ->
      (_is_concrete_expr expr) && (_is_concrete_type typ)

  | DeclDefaultStmt(idents_quals_ts) ->
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

  | RefOf(typ, expr)
  | DerefOf(typ, expr)
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

  | IfIsThenElseExpr(typ, cond_exprs, expr_2, expr_3) ->
      let is_concrete_cond_exprs =
        List.for_all (
          fun cond ->
            begin match cond with
            | IfIsGeneral(exp) ->
                _is_concrete_expr exp

            | IfIsPattern(exp, patt) ->
                _is_concrete_expr exp &&
                _is_concrete_patt patt
            end
        ) cond_exprs
      in

      (_is_concrete_type typ) &&
        is_concrete_cond_exprs &&
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

  | UfcsCall(typ, exp, _, _, exprs) ->
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
  | TemplateVar(_)
  | TemplateMixinCall(_, _) -> false
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
  | PInt(_) -> true
  | Wild(t) -> (_is_concrete_type t)
  | RequireWild(t) -> (_is_concrete_type t)
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
        let consider_decl v_decl_t =
          (* If the variant declaration has the given constructor including
          any particular fields, then include that variant decl in the filter
          result. *)
          begin if v_decl_has_ctor v_decl_t ctor then
            true

          (* Special case: if the given ctor instantiation has zero fields, it
          may be that we're trying to instantiate a constructor that technically
          has one unbound type variable as the only field, but for which our
          instantiation is trying to use Nil as the type of the type variable.
          So, handle that case by pretending for a moment that our instantiated
          ctor has a single Nil field, and see if _that_ matches any variant
          declarations. *)
          else
            begin match ctor with
            | {name; fields=[]} ->
                v_decl_has_ctor v_decl_t {name; fields=[{t=Nil}]}
            | _ -> false
            end
          end
        in

        (* Consider variants of any name for a match. *)
        if disambiguator = "" then
          consider_decl v_decl_t

        (* Else, only entertain matching variants of a particular name. *)
        else
          variant_name = disambiguator && consider_decl v_decl_t
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


(* Given a templated module declaration, any pre-existing mappings from type
variable to type, and the ordered list of the types of each of the function
invocation arguments, attempt to fully monomorphize the templated invocation,
returning the monomorphized/instantiated func, and a mod_ctxt populated with
the monomorphized/instantiated func. *)
let instantiate_func_template
  mod_ctxt mod_decl tvars_to_args func_arg_ts
  : (module_context * string * module_decl)
=
  let tvars_to_ts = tvars_to_ts_from_tvars_to_args tvars_to_args in

  begin match mod_decl with
  | FuncExternTemplateDecl(
      {f_template_decl={f_name; _}; _} as f_template_decl
    ) ->
      let f_decl =
        instantiate_func_extern_template_decl
          f_template_decl tvars_to_ts func_arg_ts
      in

      let func_sigs = StrMap.add f_name f_decl mod_ctxt.func_sigs in
      let mod_ctxt = {mod_ctxt with func_sigs = func_sigs} in

      let func_extern_decl = FuncExternDecl(f_decl) in

      (mod_ctxt, f_name, func_extern_decl)

  | FuncTemplateDef(f_template_def) ->
      let {f_decl={f_name=mangled_f_name; _} as f_decl; _} as f_def =
        instantiate_func_template_def
          f_template_def tvars_to_args func_arg_ts
      in

      let func_sigs = StrMap.add mangled_f_name f_decl mod_ctxt.func_sigs in
      let mod_ctxt = {mod_ctxt with func_sigs = func_sigs} in

      let func_extern_decl = FuncDef(f_def) in

      (mod_ctxt, mangled_f_name, func_extern_decl)

  | _ ->
      failwith (
        Printf.sprintf
          "Unimplemented: instantiate_func_template: [[ %s ]]\n"
          (fmt_mod_decl mod_decl)
      )
  end
;;


let rec type_check_mod_decls mod_decls =
  let mod_ctxt = default_mod_ctxt in

  let rec _type_check_mod_decls mod_ctxt decls =
    match decls with
    | [] -> (mod_ctxt, [], [])
    | x::xs ->
      let (mod_ctxt_up, new_decls_first, decl_tced) =
        type_check_mod_decl mod_ctxt x
      in
      let (mod_ctxt_fin, new_decls_rest, decls_tced) =
        _type_check_mod_decls mod_ctxt_up xs
      in
      (mod_ctxt_fin, new_decls_first @ new_decls_rest, decl_tced :: decls_tced)
  in
  let (mod_ctxt, new_decls, mod_decls_typechecked) =
    _type_check_mod_decls mod_ctxt mod_decls
  in

  let _ = begin
    Printf.printf "NEW DECLS: [\n";
    let fmted = fmt_join_strs "\n" (List.map fmt_mod_decl new_decls) in
    Printf.printf "%s\n" fmted;
    Printf.printf "]\n"
  end in

  (* New decls come from template instantiations. Keep processing new decls
  until there are no new ones. *)
  let rec _type_check_mod_decls_exhaust mod_ctxt decls_rem decls_tced_so_far =
    let rec _filter_unique seen decls_so_far decls : module_decl list =
      let filtered_decls_rev =
        begin match decls with
        | [] -> decls_so_far
        | decl :: rest ->
            let (unique, seen) =
              begin match decl with
              | FuncExternTemplateDecl({f_template_decl={f_name; _}; _})
              | FuncTemplateDef(
                  {f_template_def_decl={f_template_decl={f_name; _}; _}; _}
                ) ->
                  let unique =
                    not (StrMap.mem f_name mod_ctxt.func_templates) &&
                    not (StrSet.mem f_name seen)
                  in
                  let seen = StrSet.add f_name seen in
                  (unique, seen)

              | FuncExternDecl({f_name; _})
              | FuncDef({f_decl={f_name; _}; _}) ->
                  let unique =
                    not (StrMap.mem f_name mod_ctxt.func_sigs) &&
                    not (StrSet.mem f_name seen)
                  in
                  let seen = StrSet.add f_name seen in
                  (unique, seen)

              | GeneratorDef({g_decl={g_name; _}; _}) ->
                  let unique =
                    not (StrMap.mem g_name mod_ctxt.generator_sigs) &&
                    not (StrSet.mem g_name seen)
                  in
                  let seen = StrSet.add g_name seen in
                  (unique, seen)

              | VariantDecl(_) -> (true, seen)
              end
            in
            if unique then
              _filter_unique seen (decl :: decls_so_far) rest
            else
              _filter_unique seen decls_so_far rest
        end
      in
      List.rev filtered_decls_rev
    in

    (* Filter out any apparent duplicates, as we assume any "duplicates" are in
    fact just templates that have been instantiated the same way more than once.
    *)
    let decls_rem = _filter_unique StrSet.empty [] decls_rem in

    begin match decls_rem with
    | [] -> (mod_ctxt, decls_tced_so_far)
    | _ ->
        let (mod_ctxt, new_decls, decls_tced) =
          _type_check_mod_decls mod_ctxt decls_rem
        in
        (* NOTE: This ordering is important to ensure that called functions,
        even template instantiations, are compiled first before the functions
        that call them. *)
        let decls_tced_so_far = decls_tced @ decls_tced_so_far in
        _type_check_mod_decls_exhaust mod_ctxt new_decls decls_tced_so_far
    end
  in

  let (_, mod_decls_typechecked) =
    _type_check_mod_decls_exhaust mod_ctxt new_decls mod_decls_typechecked
  in

  (* If we got here, then we don't need the template decls anymore. *)
  let mod_decls_typechecked_filtered =
    List.filter (
      fun mod_decl ->
        match mod_decl with
        | FuncExternTemplateDecl(_) | FuncTemplateDef(_) -> false
        | _ -> true
    ) mod_decls_typechecked
  in

  mod_decls_typechecked_filtered

(* Handle module-level declarations, ie, function decls/defs, type decls, etc *)
and type_check_mod_decl
  mod_ctxt mod_decl : (module_context * module_decl list * module_decl)
=
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
  | FuncExternTemplateDecl(
      {f_template_decl={f_name; f_params; _}; _} as f_extern_template_decl
    ) ->
      let _ = match (StrMap.find_opt f_name mod_ctxt.func_templates) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of func extern " ^ f_name)
      in

      if not (confirm_at_most_trailing_var_arg f_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let func_templates_up = begin
          StrMap.add
            f_name
            mod_decl
            mod_ctxt.func_templates
        end in
        let mod_ctxt_up = {
          mod_ctxt with func_templates = func_templates_up
        } in

        (mod_ctxt_up, [], FuncExternTemplateDecl(f_extern_template_decl))

  | FuncTemplateDef(
      {
        f_template_def_decl={f_template_decl={f_name; f_params; _}; _}; _
      } as f_template_def
    ) ->
      let _ = match (StrMap.find_opt f_name mod_ctxt.func_templates) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of func template " ^ f_name)
      in

      if not (confirm_at_most_trailing_var_arg f_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let func_templates_up = begin
          StrMap.add
            f_name
            mod_decl
            mod_ctxt.func_templates
        end in
        let mod_ctxt_up = {
          mod_ctxt with func_templates = func_templates_up
        } in

        (mod_ctxt_up, [], FuncTemplateDef(f_template_def))

  | FuncExternDecl({f_name; f_params; f_ret_t}) ->
      begin match (StrMap.find_opt f_name mod_ctxt.func_sigs) with
      | Some(f_decl) ->
          let _ =
            Printf.printf
              "NOTE: Ignoring duplicate extern declaration [%s]\n"
              f_name
          in
          (mod_ctxt, [], FuncExternDecl(f_decl))

      | None ->
          (* If the return type is a user-defined type, bind it now. *)
          let f_ret_t = bind_type mod_ctxt f_ret_t in
          let f_decl_ast = {f_name; f_params; f_ret_t} in

          if not (confirm_at_most_trailing_var_arg f_params)
          then failwith "Only zero-or-one trailing var-args permitted"
          else
            let func_sigs_up = begin
              StrMap.add
                f_name
                {f_name; f_params; f_ret_t}
                mod_ctxt.func_sigs
            end in
            let mod_ctxt_up = {mod_ctxt with func_sigs = func_sigs_up} in

            (mod_ctxt_up, [], FuncExternDecl(f_decl_ast))
      end


  | FuncDef(
      {f_decl = {f_name; f_params; f_ret_t}; f_stmts}
    ) ->
      let _ = match (StrMap.find_opt f_name mod_ctxt.func_sigs) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of func def " ^ f_name)
      in

      (* If the return type is a user-defined type, bind it now. *)
      let f_ret_t = bind_type mod_ctxt f_ret_t in
      let f_ast = {
        f_decl = {f_name; f_params; f_ret_t};
        f_stmts
      } in

      if not (confirm_at_most_trailing_var_arg f_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let func_sigs_up = begin
          StrMap.add
            f_name
            {f_name; f_params; f_ret_t}
            mod_ctxt.func_sigs
        end in
        let mod_ctxt_up = {mod_ctxt with func_sigs = func_sigs_up} in
        let (tc_decls, func_ast_typechecked) =
          type_check_func mod_ctxt_up f_ast
        in

        (mod_ctxt_up, tc_decls, FuncDef(func_ast_typechecked))

  | GeneratorDef(g_ast) ->
      let {g_decl = {g_name; g_params; g_yield_t; g_ret_t}; g_stmts} = g_ast in
      let _ = match (StrMap.find_opt g_name mod_ctxt.generator_sigs) with
        | None -> ()
        | Some(_) -> failwith ("Multiple declarations of gen def " ^ g_name)
      in

      (* If the return type is a user-defined type, bind it now. *)
      let g_ret_t = bind_type mod_ctxt g_ret_t in
      let g_ast = {g_decl = {g_name; g_params; g_yield_t; g_ret_t}; g_stmts} in

      if not (confirm_at_most_trailing_var_arg g_params)
      then failwith "Only zero-or-one trailing var-args permitted"
      else
        let generator_sigs_up = begin
          StrMap.add
            g_name
            {g_name; g_params; g_yield_t; g_ret_t}
            mod_ctxt.generator_sigs
        end in
        let mod_ctxt_up = {mod_ctxt with generator_sigs = generator_sigs_up} in
        let (tc_decls, generator_ast_typechecked) =
          type_check_generator mod_ctxt_up g_ast
        in

        (mod_ctxt_up, tc_decls, GeneratorDef(generator_ast_typechecked))

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

      (* Make sure the type variables used within each constructor are among the
      set of declared type variables. *)
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

      (mod_ctxt_up, [], VariantDecl(bound_v_decl_ast))

and type_check_callable_body tc_ctxt stmts ret_t =
  let (tc_ctxt_final, tc_decls, stmts_typechecked) =
    type_check_stmts tc_ctxt stmts
  in

  (* If the function declaration did not specify a return type, then we try to
  resolve that return type here. *)
  let resolved_ret_t = begin match ret_t with
    | Undecided -> common_type_of_lst tc_ctxt_final.ret_t_candidates
    | _ -> ret_t
  end in

  (tc_ctxt_final, tc_decls, stmts_typechecked, resolved_ret_t)

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

  let (_, tc_decls, f_stmts_typechecked, resolved_ret_t) =
    type_check_callable_body tc_ctxt_init f_stmts f_ret_t
  in

  (
    tc_decls,
    {
      f_stmts = f_stmts_typechecked;
      f_decl = {func_def.f_decl with f_ret_t = resolved_ret_t};
    }
  )

and type_check_generator mod_ctxt generator_def =
  let {g_decl = {g_params; g_yield_t; g_ret_t; _;}; g_stmts;} = generator_def in
  let tc_ctxt_base = default_tc_ctxt g_ret_t in
  let vars_base = tc_ctxt_base.vars in
  let vars_init = populate_ctxt_with_params g_params vars_base in
  let tc_ctxt_init = {
    tc_ctxt_base with
      yield_t = g_yield_t;
      vars = vars_init;
      mod_ctxt = mod_ctxt
  } in

  let (tc_ctxt_final, tc_decls, g_stmts_typechecked, resolved_ret_t) =
    type_check_callable_body tc_ctxt_init g_stmts g_ret_t
  in

  (* If the function declaration did not specify a yield type, then we try to
  resolve that yield type here. *)
  let resolved_yield_t = begin match g_yield_t with
    | Undecided -> common_type_of_lst tc_ctxt_final.yield_t_candidates
    | _ -> g_yield_t
  end in

  (
    tc_decls,
    {
      g_stmts = g_stmts_typechecked;
      g_decl = {
        generator_def.g_decl with
          g_ret_t = resolved_ret_t;
          g_yield_t = resolved_yield_t;
      };
    }
  )

and update_vars_with_idents_quals vars_init idents_quals types =
  let idents_quals_types = List.combine idents_quals types in
  List.fold_left (
    fun vars ((id, qual), typ) ->
      StrMap.add id (typ, qual) vars
  ) vars_init idents_quals_types

and type_check_stmt
  tc_ctxt stmt : (typecheck_context * module_decl list * stmt) =
  match stmt with
  | DeclStmt(ident, qual, decl_t, exp) ->
      (* If decl_t is an unbound type (some user-defined type we only have
      the name of), then bind it and shadow decl_t with our updated type. *)
      let decl_t = bind_type tc_ctxt.mod_ctxt decl_t in
      let (tc_decls, exp_typechecked) = type_check_expr tc_ctxt decl_t exp in
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
      let tc_ctxt = {tc_ctxt with vars = vars_up} in

      (tc_ctxt, tc_decls, DeclStmt(ident, qual, resolved_t, exp_typechecked))

  | DeclDefaultStmt((idents_quals_ts)) ->
      let tc_ctxt =
        List.fold_left (
          fun tc_ctxt (ident, qual, t) ->
            (* Only permit variable declarations with no associated expr
            assignment if the decl type has a deterministic default value. *)
            if (has_default_value t) then
              let vars_up = StrMap.add ident (t, qual) tc_ctxt.vars in
              {tc_ctxt with vars = vars_up}
            else
              failwith (
                Printf.sprintf
                  "Cannot declare variable with no default value: [%s]"
                  (fmt_type t)
              )
        ) tc_ctxt idents_quals_ts
      in

      (tc_ctxt, [], stmt)

  | DeclDeconStmt(idents_quals, decl_t, exp) ->
      let (tc_decls, exp_typechecked) = type_check_expr tc_ctxt decl_t exp in
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
      let tc_ctxt = {tc_ctxt with vars = vars_up} in

      (
        tc_ctxt,
        tc_decls,
        DeclDeconStmt(idents_quals, resolved_t, exp_typechecked)
      )

  | AssignStmt(ident, _, lval_idxs, exp) ->
      (* Typecheck the chain of indexing against the named LHS variable, if
      there is any, and yield the type of the resultant target for the
      assignment (as well as the typechecked index expressions). *)
      let apply_index (decls_so_far, cur_t) lval_idx =
        begin match lval_idx with
        | ALStaticIndex(_, i) ->
            let inner_t = unwrap_aggregate_indexable cur_t i in
            let lval_idx_tc = ALStaticIndex(inner_t, i) in

            ((decls_so_far, inner_t), lval_idx_tc)

        | ALIndex(_, idx_exp) ->
            (* Typecheck the indexing expression itself. *)
            let (tc_decls, idx_exp_tc) =
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

            let lval_idx_tc = ALIndex(inner_t, idx_exp_tc) in

            ((tc_decls @ decls_so_far, inner_t), lval_idx_tc)

        | ALDeref(_) ->
            let inner_t = unwrap_ref cur_t in
            let lval_idx_tc = ALDeref(inner_t) in

            ((decls_so_far, inner_t), lval_idx_tc)
        end
      in

      let (var_t, {mut}) = StrMap.find ident tc_ctxt.vars in

      let ((apply_decls, lval_t), lval_idxs_typechecked) =
        List.fold_left_map apply_index ([], var_t) lval_idxs
      in

      let (tc_decls, exp_typechecked) = type_check_expr tc_ctxt lval_t exp in
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
        (
          tc_ctxt,
          (apply_decls @ tc_decls),
          AssignStmt(ident, var_t, lval_idxs_typechecked, exp_typechecked)
        )
      else
        failwith (
          Printf.sprintf "Expr for assignment to [%s] does not typecheck" ident
        )

  | ExprStmt(({ignore} as es_mod), exp) ->
      let (tc_decls, exp_typechecked) = type_check_expr tc_ctxt Undecided exp in
      let exp_t = expr_type exp_typechecked in
      let _ =
        begin match exp_t with
        | Nil ->
            begin if ignore then
              failwith (
                Printf.sprintf
                  "Remove redundant `ignore` on nil expression [%s]."
                  (fmt_expr exp_typechecked)
              )
            else
              ()
            end
        | _ ->
            begin if ignore then
              ()
            else
              failwith (
                Printf.sprintf
                  "Must use expression [%s], of type [%s]. (`ignore`?)"
                  (fmt_expr exp_typechecked)
                  (fmt_type exp_t)
              )
            end
        end
      in
      (tc_ctxt, tc_decls, ExprStmt(es_mod, exp_typechecked))

  | YieldStmt(exp) ->
      let (tc_decls, exp_typechecked) =
        type_check_expr tc_ctxt tc_ctxt.yield_t exp
      in
      let exp_t = expr_type exp_typechecked in
      let yield_tuple = begin
        match tc_ctxt.yield_t with
        | Undecided ->
            let yield_t_candidates_up = exp_t :: tc_ctxt.yield_t_candidates in
            let tc_ctxt_up = {
              tc_ctxt with yield_t_candidates = yield_t_candidates_up
            } in
            (tc_ctxt_up, tc_decls, YieldStmt(exp_typechecked))
        | _ ->
            if type_convertible_to exp_t tc_ctxt.yield_t
              then (tc_ctxt, tc_decls, YieldStmt(exp_typechecked))
              else failwith "Expr for return does not typecheck with func yield_t"
        end
      in

      yield_tuple

  | ReturnStmt(exp) ->
      let (tc_decls, exp_typechecked) =
        type_check_expr tc_ctxt tc_ctxt.ret_t exp
      in
      let exp_t = expr_type exp_typechecked in
      let ret_tuple = begin match tc_ctxt.ret_t with
        | Undecided ->
            let ret_t_candidates_up = exp_t :: tc_ctxt.ret_t_candidates in
            let tc_ctxt_up = {
              tc_ctxt with ret_t_candidates = ret_t_candidates_up
            } in
            (tc_ctxt_up, tc_decls, ReturnStmt(exp_typechecked))
        | _ ->
            if type_convertible_to exp_t tc_ctxt.ret_t
              then (tc_ctxt, tc_decls, ReturnStmt(exp_typechecked))
              else failwith "Expr for return does not typecheck with func ret_t"
      end in

      ret_tuple

and type_check_stmts
  tc_ctxt stmts : (typecheck_context * module_decl list * stmt list)
=
  match stmts with
  | [] -> (tc_ctxt, [], [])
  | x::xs ->
      let (tc_ctxt_updated, tc_decls_first, stmt_tced) =
        type_check_stmt tc_ctxt x
      in
      let (tc_ctxt_final, tc_decls_rest, stmts_tced) =
        type_check_stmts tc_ctxt_updated xs
      in
      (tc_ctxt_final, (tc_decls_first @ tc_decls_rest), stmt_tced :: stmts_tced)

(* expected_t is what type the expression is expected to evaluate to. We
normally don't care about this, because the stmt-level typecheck will ensure the
expression is the right type. However, in cases of eg variants/structs that
might have type variables that the expression cannot infer, this information
can provide the needed type info. *)
and type_check_expr
  (tc_ctxt : typecheck_context) (expected_t : berk_t) (exp : expr)
  : (module_decl list * expr)
=
  (* Given a tc_ctxt, a list of types, and a list of expressions of equal size,
  "zip" the list of types as "expected types" against the list of expressions,
  and yield the list of typechecked expressions. *)
  let _type_check_t_exp_zip tc_ctxt ts exprs =
    let (tc_decls, exprs_typechecked) =
      fold_left_map2 (
        fun tc_decls_so_far t exp ->
          let (tc_decls, exp_typechecked) =
            type_check_expr tc_ctxt t exp
          in
          (tc_decls @ tc_decls_so_far, exp_typechecked)
      ) [] ts exprs
    in
    (tc_decls, exprs_typechecked)
  in

  let rec _type_check_expr exp : (module_decl list * expr) =
    begin match exp with
    | ValNil -> ([], ValNil)

    | ValF128(str) -> ([], ValF128(str))
    | ValF64(f)    -> ([], ValF64(f))
    | ValF32(f)    -> ([], ValF32(f))

    | ValBool(b) -> ([], ValBool(b))

    | ValStr(s) -> ([], ValStr(s))

    (* If our generic int type is not yet _any_ inferred/default type, determine
    one now with the information we have. This may change later, if we have more
    specific information with which we can better infer a type.

    NOTE: We never wholesale replace ValInt with a more specific type; we
    want it to remain fluid in case we can make a better inference later. *)
    | ValInt(Undecided, i) ->
        begin match expected_t with
        (* Barring more specific information, default to reasonable int type. *)
        | Undecided
        | Unbound(_) ->
            ([], ValInt(I32, i))

        | I64 | I32 | I16 | I8 -> ([], ValInt(expected_t, i))
        | U64 | U32 | U16 | U8 ->
            if i >= 0 then
              ([], ValInt(expected_t, i))
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
    | ValInt(_, _) -> ([], exp)

    | ValVar(_, id) ->
        let (var_t, _) =
          try StrMap.find id tc_ctxt.vars
          with Not_found ->
            failwith (Printf.sprintf "No variable [%s] in scope" id)
        in
        ([], ValVar(var_t, id))

    | ValFunc(_, func_name) ->
        let {f_params; f_ret_t; _} =
          StrMap.find func_name tc_ctxt.mod_ctxt.func_sigs
        in
        let f_param_t_lst = List.map (fun (_, _, t) -> t) f_params in
        let func_t = Function(f_ret_t, f_param_t_lst) in

        ([], ValFunc(func_t, func_name))

    | ValName(_, name) ->
        (* "Generic variable" lookup first searches for actual in-scope named
        variables, and if that fails, searches for functions of the same name,
        yielding a function pointer. *)
        begin
          try
            let (var_t, _) = StrMap.find name tc_ctxt.vars in
            ([], ValVar(var_t, name))
          with Not_found ->
          try
            begin
              let {f_params; f_ret_t; _} =
                StrMap.find name tc_ctxt.mod_ctxt.func_sigs
              in
              let f_param_t_lst = List.map (fun (_, _, t) -> t) f_params in
              let func_t = Function(f_ret_t, f_param_t_lst) in
              ([], ValFunc(func_t, name))
            end
          with Not_found ->
            failwith
              (Printf.sprintf "No variable or function [%s] in scope" name)
        end

    | ValRawArray(t) -> ([], ValRawArray(t))

    | RefOf(_, exp) ->
        let (tc_decls, exp_typechecked) = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in

        (* This helper function ensures we don't double-wrap a reference type.
        *)
        let ref_exp_t = wrap_ref exp_t in

        (tc_decls, RefOf(ref_exp_t, exp_typechecked))

    | DerefOf(_, exp) ->
        let (tc_decls, exp_typechecked) = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in

        begin match exp_t with
        | Ref(inner_t) -> (tc_decls, DerefOf(inner_t, exp_typechecked))
        | _ ->
          failwith (
            Printf.sprintf "Cannot dereference non-reference type [%s] for [%s]"
              (fmt_type exp_t)
              (fmt_expr exp_typechecked)
          )
        end

    | ValCast(target_t, op, exp) ->
        let (tc_decls, exp_typechecked) = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in

        let op_func_check =
          begin match op with
          | Truncate -> type_truncatable_to
          | Bitwise -> type_bitwise_to
          | Extend -> type_extendable_to
          end
        in

        if op_func_check exp_t target_t then
          (tc_decls, ValCast(target_t, op, exp_typechecked))
        else
          failwith (
            Printf.sprintf "Cannot [%s] incompatible types" (fmt_cast_op op)
          )

    | UnOp(_, op, exp) ->
        let (tc_decls, exp_typechecked) = _type_check_expr exp in
        let exp_t = expr_type exp_typechecked in

        begin match (op, exp_t) with
        | (LNot, Bool) -> (tc_decls, UnOp(exp_t, op, exp_typechecked))
        | _ ->
            failwith (
              Printf.sprintf "Invalid combination of op/type for [%s]/[%s]"
              (fmt_un_op op)
              (fmt_type exp_t)
            )
        end

    | BinOp(_, op, lhs, rhs) ->
        let (lhs_tc_decls, lhs_typechecked) = _type_check_expr lhs in
        let (rhs_tc_decls, rhs_typechecked) = _type_check_expr rhs in

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
        let (_, lhs_typechecked) = _type_check_expr lhs_typechecked in
        let (_, rhs_typechecked) = _type_check_expr rhs_typechecked in

        let tc_decls = lhs_tc_decls @ rhs_tc_decls in

        let lhs_t = expr_type lhs_typechecked in
        let rhs_t = expr_type rhs_typechecked in

        begin match op with
        | Add | Sub | Mul | Div | Mod ->
            let common_t = common_type_of_lr lhs_t rhs_t in
            (tc_decls, BinOp(common_t, op, lhs_typechecked, rhs_typechecked))

        | Eq | Ne | Lt | Le | Gt | Ge ->
            (* TODO: There should be an additional check that these are actually
            comparable, as relevant. *)
            (tc_decls, BinOp(Bool, op, lhs_typechecked, rhs_typechecked))

        | LOr | LAnd ->
            begin match (lhs_t, rhs_t) with
            | (Bool, Bool) ->
                (tc_decls, BinOp(Bool, op, lhs_typechecked, rhs_typechecked))

            | _ ->
                failwith (
                  Printf.sprintf
                    "Cannot logical-and/or on non-bool operands: [%s] vs [%s]"
                    (fmt_type lhs_t) (fmt_type rhs_t)
                )
            end
        end

    | BlockExpr(_, stmts, exp) ->
        let (tc_ctxt, stmts_tc_decls, stmts_typechecked) =
          type_check_stmts tc_ctxt stmts
        in

        let (expr_tc_decls, expr_typechecked) =
          type_check_expr tc_ctxt expected_t exp
        in
        let expr_t = expr_type expr_typechecked in

        let tc_decls = stmts_tc_decls @ expr_tc_decls in

        (tc_decls, BlockExpr(expr_t, stmts_typechecked, expr_typechecked))

    | IfThenElseExpr(_, if_cond, then_expr, else_expr) ->
        let (cond_tc_decls, if_cond_typechecked) = _type_check_expr if_cond in
        let if_cond_t = expr_type if_cond_typechecked in

        let _ = match if_cond_t with
        | Bool -> ()
        | _ -> failwith "if-expr condition must resolve to Bool"
        in

        let (then_tc_decls, then_expr_typechecked) =
          _type_check_expr then_expr
        in
        let (else_tc_decls, else_expr_typechecked) =
          _type_check_expr else_expr
        in

        let then_expr_t = expr_type then_expr_typechecked in
        let else_expr_t = expr_type else_expr_typechecked in

        let then_else_agreement_t = common_type_of_lr then_expr_t else_expr_t in

        let tc_decls = cond_tc_decls @ then_tc_decls @ else_tc_decls in

        (
          tc_decls,
          IfThenElseExpr(
            then_else_agreement_t,
            if_cond_typechecked,
            then_expr_typechecked,
            else_expr_typechecked
          )
        )

    | IfIsThenElseExpr(_, conds, then_expr, else_expr) ->
        let ((tc_ctxt, cond_tc_decls), conds_typechecked) =
          List.fold_left_map (
            fun (tc_ctxt, tc_decls_so_far) cond ->
              begin match cond with
              | IfIsGeneral(inner_cond) ->
                  (* Normal boolean conditions should evaluate to bool. *)

                  let (tc_decls, inner_cond_typechecked) =
                    type_check_expr tc_ctxt Undecided inner_cond
                  in
                  let inner_cond_t = expr_type inner_cond_typechecked in

                  let _ = match inner_cond_t with
                  | Bool -> ()
                  | _ -> failwith "if-expr condition must resolve to Bool"
                  in

                  (
                    (tc_ctxt, (tc_decls_so_far @ tc_decls)),
                    IfIsGeneral(inner_cond_typechecked)
                  )

              | IfIsPattern(matched_exp, patt) ->
                  (* is-bindings need to agree in type between the matchee and
                  the match pattern. The boolean conditional is implied by
                  whether or not the match actually succeeds. *)

                  let (tc_decls, matched_exp_typechecked) =
                    type_check_expr tc_ctxt Undecided matched_exp
                  in
                  let matched_exp_t = expr_type matched_exp_typechecked in

                  let (tc_ctxt, patt_typechecked) =
                    type_check_pattern tc_ctxt matched_exp_t patt
                  in

                  (
                    (tc_ctxt, (tc_decls_so_far @ tc_decls)),
                    IfIsPattern(matched_exp_typechecked, patt_typechecked)
                  )
              end
          ) (tc_ctxt, []) conds
        in

        (* Since there could be new variable bindings introduced from the
        conditional patterns, we need to use the updated tc_ctxt we have rather
        than the top-level one, as these bindings need to exist within the
        then-branch (but not the else-branch!) *)

        let (then_tc_decls, then_expr_typechecked) =
          type_check_expr tc_ctxt expected_t then_expr
        in
        let (else_tc_decls, else_expr_typechecked) =
          _type_check_expr else_expr
        in

        let then_expr_t = expr_type then_expr_typechecked in
        let else_expr_t = expr_type else_expr_typechecked in

        let then_else_agreement_t = common_type_of_lr then_expr_t else_expr_t in

        (
          (cond_tc_decls @ then_tc_decls @ else_tc_decls),
          IfIsThenElseExpr(
            then_else_agreement_t,
            conds_typechecked,
            then_expr_typechecked,
            else_expr_typechecked
          )
        )

    | WhileExpr(_, init_stmts, while_cond, then_stmts) ->
        (* NOTE: We keep the returned tc_ctxt for typechecking the init-stmts,
        as any declared variables in the init-stmts remain in scope for the
        while expr and body of the while. *)
        let (tc_ctxt, init_tc_decls, init_stmts_typechecked) =
          type_check_stmts tc_ctxt init_stmts
        in

        (* We call the top-level `type_check_expr`, and not `_type_check_expr`,
        because we want to use the tc_ctxt returned by typechecking the
        init-stmts, because we want visibility into any in-scope init-stmt vars.
        *)
        let (cond_tc_decls, while_cond_typechecked) =
          type_check_expr tc_ctxt expected_t while_cond
        in
        let while_cond_t = expr_type while_cond_typechecked in

        let (_, body_tc_decls, then_stmts_typechecked) =
          type_check_stmts tc_ctxt then_stmts
        in

        let _ = match while_cond_t with
        | Bool -> ()
        | _ -> failwith "if-expr condition must resolve to Bool"
        in

        (
          (init_tc_decls @ cond_tc_decls @ body_tc_decls),
          WhileExpr(
            Nil,
            init_stmts_typechecked,
            while_cond_typechecked,
            then_stmts_typechecked
          )
        )

    | FuncCall(dummy_t, f_name, exprs) ->
        begin match (StrMap.find_opt f_name tc_ctxt.mod_ctxt.func_sigs) with
        | Some({f_params; f_ret_t; _}) ->
          begin
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

            let (params_tc_decls, exprs_typechecked) =
              _type_check_t_exp_zip tc_ctxt params_t_lst_padded exprs
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

            (params_tc_decls, FuncCall(f_ret_t, f_name, exprs_typechecked))
          end

        | None ->
            begin match (
              StrMap.find_opt f_name tc_ctxt.mod_ctxt.generator_sigs
            ) with
            | Some({g_params; g_yield_t; g_ret_t; _}) ->
                g_params |> ignore;
                g_yield_t |> ignore;
                g_ret_t |> ignore;
                failwith (Printf.sprintf "Unimplemented: generator %s" f_name)

            | None ->
                let get_exprs_t f_params =
                  let (params_non_variadic_t_lst, is_var_arg) =
                    get_static_f_params f_params
                  in

                  if is_var_arg then
                    failwith "Unimplemented: VarArg FuncExternTemplateDecl"
                  ;

                  let params_t_lst_padded = begin
                      let len_diff =
                        (List.length exprs) -
                        (List.length params_non_variadic_t_lst)
                      in
                      if len_diff = 0 then
                        params_non_variadic_t_lst
                      else if len_diff > 0 then
                        let padding =
                          List.init len_diff (fun _ -> Undecided)
                        in
                        params_non_variadic_t_lst @ padding
                      else
                        failwith (
                          "Unexpected shorter expr list than non-variadic " ^
                          "params"
                        )
                    end
                  in

                  let (tc_decls, exprs_typechecked) =
                    _type_check_t_exp_zip tc_ctxt params_t_lst_padded exprs
                  in

                  let exprs_t = List.map expr_type exprs_typechecked in

                  (tc_decls, exprs_t)
                in

                begin match (
                  StrMap.find_opt f_name tc_ctxt.mod_ctxt.func_templates
                ) with
                | Some(
                    (
                      FuncExternTemplateDecl(
                        {f_template_decl={f_params; _}; f_template_params}
                      ) as f_template
                    )
                      |
                    (
                      FuncTemplateDef(
                        {
                          f_template_def_decl={
                            f_template_decl={f_params; _};
                            f_template_params
                          }; _
                        }
                      ) as f_template
                    )
                  ) ->

                    let (tc_decls, exprs_t) = get_exprs_t f_params in

                    let tvars_to_args =
                      List.fold_left (
                        fun tvars_to_args (name, maybe_arg) ->
                          begin match maybe_arg with
                          | Some(arg) -> StrMap.add name arg tvars_to_args
                          | None -> tvars_to_args
                          end
                      ) StrMap.empty f_template_params
                    in

                    let (
                      mod_ctxt, mangled_f_name, new_mod_decl
                    ) =
                      instantiate_func_template
                        tc_ctxt.mod_ctxt f_template tvars_to_args exprs_t
                    in
                    let tc_ctxt = {tc_ctxt with mod_ctxt = mod_ctxt} in

                    (* Recurse with what should now be a fully-instantiated
                    version of the templated signature. *)
                    let (recurse_tc_decls, exp_typechecked) =
                      type_check_expr
                        tc_ctxt
                        expected_t
                        (FuncCall(dummy_t, mangled_f_name, exprs))
                    in

                    (
                      (new_mod_decl :: tc_decls @ recurse_tc_decls),
                      exp_typechecked
                    )

                | _ ->
                    failwith (
                      Printf.sprintf "Error: no known function %s" f_name
                    )
                end
            end
        end

    | UfcsCall(_, exp, f_name, underscore_pos, exprs) ->
        let {f_name; f_params; f_ret_t} =
          StrMap.find f_name tc_ctxt.mod_ctxt.func_sigs
        in

        (* For now, a UFCS call is simply a different syntax for a normal
        function call. Later, a UFCS call might also be a method call, where
        we may need to do some additional checking. Unclear yet. *)

        let exprs = insert exprs underscore_pos exp in

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

        let (tc_decls, exprs_typechecked) =
          _type_check_t_exp_zip tc_ctxt params_t_lst_padded exprs
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

        (* Rewrite the UFCS call into a normal function call, and then recurse
        in case any additional processing needs to happen (like generator
        handling). *)
        let (recurse_tc_decls, exp_typechecked) =
          type_check_expr
            tc_ctxt expected_t (FuncCall(f_ret_t, f_name, exprs_typechecked))
        in
        (tc_decls @ recurse_tc_decls, exp_typechecked)

    | ExprInvoke(_, func_exp, exprs) ->
        let (lhs_tc_decls, func_exp_typechecked) = _type_check_expr func_exp in
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

        let (params_tc_decls, exprs_typechecked) =
          _type_check_t_exp_zip tc_ctxt params_t_lst_padded exprs
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

        (
          lhs_tc_decls @ params_tc_decls,
          ExprInvoke(ret_t, func_exp_typechecked, exprs_typechecked)
        )

    | ArrayExpr(_, exprs) ->
        let elem_expected_t = begin match expected_t with
          | Array(elem_t, _) -> elem_t
          | Undecided -> Undecided
          | _ -> failwith "Unexpectedly expecting non-array type in array expr"
        end in

        let (tc_decls, exprs_typechecked) =
          List.fold_left_map (
            fun tc_decls_so_far expr ->
              let (tc_decls, expr_typechecked) =
                type_check_expr tc_ctxt elem_expected_t expr
              in
              (tc_decls @ tc_decls_so_far, expr_typechecked)
          ) [] exprs
        in
        let expr_t_lst = List.map expr_type exprs_typechecked in
        let common_t = common_type_of_lst expr_t_lst in
        let arr_t = Array(common_t, List.length exprs) in

        (tc_decls, ArrayExpr(arr_t, exprs_typechecked))

    | IndexExpr(_, idx, arr) ->
        let (idx_tc_decls, idx_typechecked) =
          type_check_expr tc_ctxt Undecided idx
        in
        let (arr_tc_decls, arr_typechecked) = _type_check_expr arr in
        let tc_decls = idx_tc_decls @ arr_tc_decls in
        let idx_t = expr_type idx_typechecked in
        let arr_t = expr_type arr_typechecked in
        if is_index_type idx_t && is_indexable_type arr_t
          then
            begin match arr_t with
            | Ref(Array(elem_typ, sz))
            | Array(elem_typ, sz) ->
                (* If indexing into the array yields a base type (not an
                indexable type), then we default to yielding that value. But,
                if the index operation itself yields an indexable type, we will
                yield a _reference_ to that indexable type, that would require
                further indexing. *)
                let yielded_t =
                  if is_indexable_type elem_typ then
                    wrap_ref elem_typ
                  else
                    elem_typ
                in

                begin match idx_typechecked with
                | ValInt(_, i) ->
                    begin if i < sz && i >= 0 then
                      (
                        tc_decls,
                        IndexExpr(
                          yielded_t, idx_typechecked, arr_typechecked
                        )
                      )
                    else
                      failwith "Static out-of-bounds index into array"
                    end
                | _ ->
                    (
                      tc_decls,
                      IndexExpr(
                        yielded_t, idx_typechecked, arr_typechecked
                      )
                    )
                end

            | _ ->
                failwith (
                  Printf.sprintf
                    "Unexpected index target [%s] in index expr [%s]; [%s] [%s]"
                    (fmt_type arr_t)
                    (fmt_expr ~print_typ:true exp)
                    (fmt_type arr_t)
                    (fmt_type idx_t)
                )
            end
          else
            failwith (
              Printf.sprintf
                "Unexpected components of index operation: [%s] [%s]"
                (fmt_expr ~print_typ:true arr_typechecked)
                (fmt_expr ~print_typ:true idx_typechecked)
            )

    | TupleIndexExpr(_, idx, agg) ->
        let (tc_decls, agg_typechecked) = _type_check_expr agg in
        let agg_t = expr_type agg_typechecked in
        let tuple_idx_typechecked = begin
          match agg_t with
          | Ref((Tuple(_) as tuple_t))
          | (Tuple(_) as tuple_t) ->
              let elem_typ = unwrap_aggregate_indexable tuple_t idx in

              (* If indexing into the tuple yields a base type (not an
              indexable type), then we default to yielding that value. But,
              if the index operation itself yields an indexable type, we will
              yield a _reference_ to that indexable type, that would require
              further indexing. *)
              let yielded_t =
                if is_indexable_type elem_typ then
                  wrap_ref elem_typ
                else
                  elem_typ
              in

              TupleIndexExpr(yielded_t, idx, agg_typechecked)

          | _ ->
              failwith (
                Printf.sprintf "Unexpectedly indexing into non-tuple: [ %s ]"
                  (fmt_type agg_t)
              )
        end in

        (tc_decls, tuple_idx_typechecked)

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

        let (tc_decls, exprs_typechecked) =
          _type_check_t_exp_zip tc_ctxt elem_expected_t_lst exprs
        in
        let exprs_t_lst = List.map expr_type exprs_typechecked in
        let tuple_t = Tuple(exprs_t_lst) in

        (tc_decls, TupleExpr(tuple_t, exprs_typechecked))

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

        let _ =
          if (List.length field_exprs) <> (List.length ctor_expected_ts) then
            let matched_args_formatter str_so_far field_expr ctor_expected_t =
              Printf.sprintf "%s  %s : %s\n"
                str_so_far
                (fmt_expr field_expr)
                (fmt_type ctor_expected_t)
            in

            (* Get formatted strings for printing an error message like:
                <expr> : <type>
                <expr> : <type>
                <missing-expr> : <type>
                or
                <expr> : <missing-type-arg>
             *)
            let (matched_args_fmt, mismatched_args_fmt) = begin
              if (List.length field_exprs) > (List.length ctor_expected_ts) then
                let (matched_field_exprs, unmatched_field_exprs) =
                  take_with_tail (List.length ctor_expected_ts) field_exprs
                in

                let matched_field_exprs_fmt =
                  List.fold_left2
                    matched_args_formatter
                    "" matched_field_exprs ctor_expected_ts
                in
                let mismatched_field_exprs_fmt =
                  List.fold_left (
                    fun str_so_far unmatched_field_expr ->
                      Printf.sprintf "%s  %s : <missing-type-arg>\n"
                        str_so_far
                        (fmt_expr unmatched_field_expr)
                  ) "" unmatched_field_exprs
                in
                (matched_field_exprs_fmt, mismatched_field_exprs_fmt)

              else
                let (matched_ctor_expected_ts, unmatched_ctor_expected_ts) =
                  take_with_tail (List.length field_exprs) ctor_expected_ts
                in

                let matched_ctor_expected_ts_fmt =
                  List.fold_left2
                    matched_args_formatter
                    "" field_exprs matched_ctor_expected_ts
                in
                let mismatched_ctor_expected_ts_fmt =
                  List.fold_left (
                    fun str_so_far unmatched_ctor_expected_t ->
                      Printf.sprintf "%s  <missing-expr> : %s\n"
                        str_so_far
                        (fmt_type unmatched_ctor_expected_t)
                  ) "" unmatched_ctor_expected_ts
                in
                (matched_ctor_expected_ts_fmt, mismatched_ctor_expected_ts_fmt)
            end in

            failwith (
              Printf.sprintf
                (
                  "Error: Mismatch in variant ctor [%s] args, " ^^
                  "expect vs got:\n%s%s"
                )
                ctor_name
                matched_args_fmt
                mismatched_args_fmt
            )
          else
            ()
        in

        let (tc_decls, field_exprs_typechecked) =
          _type_check_t_exp_zip tc_ctxt ctor_expected_ts field_exprs
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

        (
          tc_decls,
          VariantCtorExpr(inferred_v_t, ctor_name, field_exprs_typechecked)
        )

    | MatchExpr(_, matched_expr, pattern_expr_pairs) ->
        let (matched_tc_decls, matched_expr_tc) =
          _type_check_expr matched_expr
        in
        let matched_t = expr_type matched_expr_tc in

        let typecheck_pattern_expr_pair arms_tc_decls (patt, exp) =
          let (tc_ctxt, patt_tc) = type_check_pattern tc_ctxt matched_t patt in
          let (arm_tc_decl, exp_tc) = type_check_expr tc_ctxt Undecided exp in

          ((arms_tc_decls @ arm_tc_decl), (patt_tc, exp_tc))
        in

        let (arms_tc_decls, pattern_expr_pairs_tc) =
          List.fold_left_map
            typecheck_pattern_expr_pair [] pattern_expr_pairs
        in

        let patts = List.map (fun (patt, _) -> patt) pattern_expr_pairs_tc in

        let _ = check_patt_usefulness_exhaustion patts matched_t in

        let common_t = common_type_of_lst (
          List.map (fun (_, exp) -> expr_type exp) pattern_expr_pairs_tc
        ) in

        (
          (matched_tc_decls @ arms_tc_decls),
          MatchExpr(common_t, matched_expr_tc, pattern_expr_pairs_tc)
        )

    | TemplateVar(_)
    | TemplateMixinCall(_, _) ->
        failwith (
          Printf.sprintf "Error: Cannot type_check_expr with %s\n"
            (dump_expr_ast exp)
        )
    end
  in

  (* First, allow the typechecker to try to infer types as much as possible. *)
  let (tc_decls, exp_typechecked) = _type_check_expr exp in
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

  (tc_decls, exp_typechecked_injected)

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

  | RequireWild(_) ->
      failwith (
        Printf.sprintf "Error: Cannot have RequireWild as match pattern."
      )

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

  | PInt(_, range) ->
      begin match matched_t with
      | I8 | I16 | I32 | I64 ->
          (tc_ctxt, PInt(matched_t, range))

      | U8 | U16 | U32 | U64 ->
          begin match range with
          | IRangeAll ->
              (tc_ctxt, PInt(matched_t, range))

          | IRangeAllFrom(i)
          | IRangeAllUntil(i)
          | IRangeFromUntil(i, _)
          | IRangeLiteral(i) ->
              if i >= 0 then
                (tc_ctxt, PInt(matched_t, range))
              else
                failwith (
                  Printf.sprintf
                    "Cannot match negative int pattern against type [%s]"
                    (fmt_type matched_t)
                )
          end

      | _ -> failwith "Match expression type does not match int in pattern"
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
            let found_ctor =
              List.find_opt (fun {name; _} -> ctor_name = name) ctors
            in
            begin match found_ctor with
            | Some({fields=ctor_fields; _}) -> ctor_fields
            | None ->
                failwith (
                  Printf.sprintf "Could not find ctor %s in variant patt %s\n"
                    ctor_name
                    (fmt_pattern patt)
                )
            end
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

(* Whether the left range dominates any portion of the right range. Also returns
a possibly-empty list of the "split" ranges left over in the RHS range after
"cutting out" the LHS range from the RHS range. *)
and int_range_dominates lhs_range rhs_range : (bool * int_range list) =
  let (dominates, new_ranges) =
    begin match (lhs_range, rhs_range) with
    | (IRangeLiteral(i), IRangeLiteral(j)) ->
        if i = j then (true, []) else (false, [])

    | (IRangeLiteral(i), IRangeAll) ->
        (true, [IRangeAllUntil(i); IRangeAllFrom(i + 1)])

    | (IRangeLiteral(i), IRangeAllFrom(j)) ->
        begin if i = j then
          (true, [IRangeAllFrom(i + 1)])
        else if i > j then
          (true, [IRangeFromUntil(j, i); IRangeAllFrom(i + 1)])
        else
          (false, [])
        end

    | (IRangeLiteral(i), IRangeAllUntil(j)) ->
        begin if i = j then
          (* "until" is exclusive *)
          (false, [])
        else if i = j - 1 then
          (true, [IRangeAllUntil(i)])
        else if i < j - 1 then
          (true, [IRangeAllUntil(i); IRangeFromUntil(i + 1, j)])
        else
          (false, [])
        end

    | (IRangeLiteral(i), IRangeFromUntil(j, k)) ->
        begin if j >= k then
          failwith (
            Printf.sprintf "Cannot have IRangeFromUntil(%d, %d)" j k
          )
        (* "until" is exclusive *)
        else if i = k then
          (false, [])
        else if i = k - 1 then
          (true, [IRangeFromUntil(j, i)])
        else if i = j then
          (true, [IRangeFromUntil(i + 1, k)])
        else if i > j && i < k then
          (true, [IRangeFromUntil(j, i); IRangeFromUntil(i + 1, k)])
        else
          let _ = assert (i < j || i >= k) in
          (false, [])
        end

    | (IRangeAllFrom(i), IRangeLiteral(j)) ->
        if i <= j then (true, []) else (false, [])

    | (IRangeAllFrom(i), IRangeAll) ->
        (true, [IRangeAllUntil(i)])

    | (IRangeAllFrom(i), IRangeAllFrom(j)) ->
        begin if i <= j then
          (true, [])
        else
          (true, [IRangeFromUntil(j, i)])
        end

    | (IRangeAllFrom(i), IRangeAllUntil(j)) ->
        begin if i >= j then
          (false, [])
        else
          (true, [IRangeAllUntil(i - 1)])
        end

    | (IRangeAllFrom(i), IRangeFromUntil(j, k)) ->
        begin if i <= j then
          (true, [])
        else if i >= k then
          (false, [])
        else
          (true, [IRangeFromUntil(j, i - 1)])
        end

    | (IRangeAllUntil(i), IRangeLiteral(j)) ->
        if i > j then (true, []) else (false, [])

    | (IRangeAllUntil(i), IRangeAll) ->
        (true, [IRangeAllFrom(i)])

    | (IRangeAllUntil(i), IRangeAllFrom(j)) ->
        begin if i <= j then
          (false, [])
        else
          (true, [IRangeAllFrom(i)])
        end

    | (IRangeAllUntil(i), IRangeAllUntil(j)) ->
        begin if i >= j then
          (true, [])
        else
          (true, [IRangeFromUntil(i, j)])
        end

    | (IRangeAllUntil(i), IRangeFromUntil(j, k)) ->
        begin if i >= k then
          (true, [])
        else if i <= j then
          (false, [])
        else
          (true, [IRangeFromUntil(i, k)])
        end

    | (IRangeFromUntil(i, j), IRangeLiteral(k)) ->
        begin if i >= j then
          failwith (
            Printf.sprintf "Cannot have IRangeFromUntil(%d, %d)" i j
          )
        else if k >= i && k < j then
          (true, [])
        else
          (false, [])
        end

    | (IRangeFromUntil(i, j), IRangeAll) ->
        begin if i >= j then
          failwith (
            Printf.sprintf "Cannot have IRangeFromUntil(%d, %d)" i j
          )
        else
          (true, [IRangeAllUntil(i); IRangeAllFrom(j)])
        end

    | (IRangeFromUntil(i, j), IRangeAllFrom(k)) ->
        begin if i >= j then
          failwith (
            Printf.sprintf "Cannot have IRangeFromUntil(%d, %d)" i j
          )
        else if j <= k then
          (false, [])
        else if i <= k then
          (true, [IRangeAllFrom(j)])
        else
          let _ = assert (i > k && j > k) in
          (true, [IRangeFromUntil(k, i); IRangeAllFrom(j)])
        end

    | (IRangeFromUntil(i, j), IRangeAllUntil(k)) ->
        begin if i >= j then
          failwith (
            Printf.sprintf "Cannot have IRangeFromUntil(%d, %d)" i j
          )
        else if i >= k then
          (false, [])
        else if j >= k then
          (true, [IRangeAllUntil(i)])
        else
          let _ = assert (i < k && j < k) in
          (true, [IRangeAllUntil(i); IRangeFromUntil(j, k)])
        end

    | (IRangeFromUntil(i, j), IRangeFromUntil(k, m)) ->
        begin if i >= j then
          failwith (
            Printf.sprintf "Cannot have IRangeFromUntil(%d, %d)" i j
          )
        else if i >= m || j <= k then
          (false, [])
        else if i <= k && j >= m then
          (true, [])
        else if i <= k && j < m then
          (true, [IRangeFromUntil(j, m)])
        else if i > k && j >= m then
          (true, [IRangeFromUntil(k, i)])
        else
          let _ = assert (i > k && j < m) in
          (true, [IRangeFromUntil(k, i); IRangeFromUntil(j, m)])
        end

    | (IRangeAll, _) -> (true, [])
    end
  in

  (* The above process may generate new ranges that are not in canonical form.
  ie, a "range" from [1, 2) should just be the literal [1]. *)
  let rec _filter_new_ranges new_ranges_rest new_ranges_filtered_rev =
    begin match new_ranges_rest with
    | [] -> new_ranges_filtered_rev

    | (
        (
          IRangeLiteral(_) | IRangeAllFrom(_) | IRangeAllUntil(_) | IRangeAll
        ) as valid_range
      ) :: rest ->
        _filter_new_ranges rest (valid_range :: new_ranges_filtered_rev)

    | (IRangeFromUntil(i, j) as valid_range) :: rest ->
        if i = j then
          failwith (
            Printf.sprintf
              "(Probably shouldn't fail): i = j in IRangeFromUntil(%d, %d)"
              i j
          )
        else if i = j - 1 then
          _filter_new_ranges rest (IRangeLiteral(i) :: new_ranges_filtered_rev)
        else
          _filter_new_ranges rest (valid_range :: new_ranges_filtered_rev)
    end
  in

  let new_ranges_filtered_rev = _filter_new_ranges new_ranges [] in
  let new_ranges_filtered = List.rev new_ranges_filtered_rev in

  (dominates, new_ranges_filtered)


(* Does the LHS pattern dominate the RHS pattern?

Returns a pair: (bool, pattern list)

The boolean indicates whether the LHS pattern should be considered to dominate
the RHS pattern. The pattern list is some possibly-empty list of _new_ patterns
generated because the LHS pattern "split" the RHS pattern into sub-patterns. *)
and pattern_dominates lhs_patt rhs_patt : (bool * pattern list) =
  begin match (lhs_patt, rhs_patt) with
  | ((Wild(_) | VarBind(_, _)), _) -> (true, [])

  | (_, (Wild(_) | VarBind(_, _))) ->
      Printf.printf "No pattern dominates wildcards other than wildcards.\n" ;
      (false, [])

  | (PNil, PNil) -> (true, [])

  | (PBool(lhs_b), PBool(rhs_b)) ->
      if lhs_b = rhs_b then (true, []) else (false, [])

  | (PInt(t, lhs_range), PInt(_, rhs_range)) ->
      let (dominates, new_ranges) = int_range_dominates lhs_range rhs_range in
      let new_patts = List.map (fun range -> PInt(t, range)) new_ranges in
      (dominates, new_patts)

  | (PTuple(_, lhs_patts), PTuple(_ as rhs_t, rhs_patts)) ->
      let (each_dominates, each_new_patts) =
        List.split (
          map2i (
            fun i lhs rhs ->
              (* This call to pattern_dominates may yield non-zero new patterns
              based off the _sub_-pattern we're currently examining. If so, we
              need to translate this into new full-size patterns where the
              currently-examined field pattern is replaced by the new
              pattern(s). *)
              let (dominates, new_sub_patts) = pattern_dominates lhs rhs in
              let new_patts =
                begin if List.length new_sub_patts = 0 then
                  []
                else
                  let (pre_fields, post_fields) = partition_i i rhs_patts in
                  List.map (
                    fun new_sub_patt ->
                      PTuple(rhs_t, pre_fields @ [new_sub_patt] @ post_fields)
                  ) new_sub_patts
                end
              in

              (dominates, new_patts)
          ) lhs_patts rhs_patts
        )
      in
      let all_dominates = List.fold_left (&&) true each_dominates in
      let all_new_patts = List.fold_left (List.append) [] each_new_patts in
      (all_dominates, all_new_patts)

  | (
      Ctor(_, lhs_ctor_name, lhs_patts),
      Ctor(_ as rhs_t, rhs_ctor_name, rhs_patts)
    ) ->
      if lhs_ctor_name = rhs_ctor_name then
        let (each_dominates, each_new_patts) =
          List.split(
            map2i (
              fun i lhs rhs ->
              (* This call to pattern_dominates may yield non-zero new patterns
              based off the _sub_-pattern we're currently examining. If so, we
              need to translate this into new full-size patterns where the
              currently-examined field pattern is replaced by the new
              pattern(s). *)
              let (dominates, new_sub_patts) = pattern_dominates lhs rhs in
              let new_patts =
                begin if List.length new_sub_patts = 0 then
                  []
                else
                  let (pre_fields, post_fields) = partition_i i rhs_patts in
                  List.map (
                    fun new_sub_patt ->
                      Ctor(
                        rhs_t,
                        rhs_ctor_name,
                        pre_fields @ [new_sub_patt] @ post_fields
                      )
                  ) new_sub_patts
                end
              in

              (dominates, new_patts)
            ) lhs_patts rhs_patts
          )
        in
        let all_dominates = List.fold_left (&&) true each_dominates in
        let all_new_patts = List.fold_left (List.append) [] each_new_patts in
        (all_dominates, all_new_patts)
      else
        (false, [])

  | (PatternAs(_, lhs_patt, _), PatternAs(_, rhs_patt, _)) ->
      pattern_dominates lhs_patt rhs_patt

  | (PatternAs(_, lhs_patt, _), rhs_patt) ->
      pattern_dominates lhs_patt rhs_patt

  | (PNil, _)
  | (PBool(_), _)
  | (
      PInt(_),
      (
        PNil | PBool(_) | PTuple(_, _) | Ctor(_, _, _) | PatternAs(_, _, _) |
        RequireWild(_)
      )
    )
  | (PTuple(_, _), _)
  | (Ctor(_, _, _), _) -> failwith "Non-matching pattern types."

  | (RequireWild(_), _) ->
      failwith (
        Printf.sprintf "Cannot use RequireWild(_) as match pattern."
      )

  end

(* Given a LHS pattern (something found in the source) and a list of RHS
patterns expected to structurally match the LHS (a subset of all possible
permutations of patterns the LHS should at least partially match), return
whether the LHS pattern was useful (dominated at least one RHS pattern), and
return the filtered list of RHS patterns that the LHS pattern does not dominate.
*)
and filter_dominated lhs_patt rhs_patts : (bool * pattern list) =
  let rec _filter_dominated
    rhs_patts_rest has_dominated rhs_patts_unfiltered_rev new_patts_so_far
  =
    match rhs_patts_rest with
    | [] ->
        (has_dominated, rhs_patts_unfiltered_rev, new_patts_so_far)

    | rhs_patt :: rhs_patts_rest ->
        let (dominates, new_patts) = pattern_dominates lhs_patt rhs_patt in
        begin if dominates then
          _filter_dominated
            rhs_patts_rest
            (dominates || has_dominated)
            rhs_patts_unfiltered_rev
            (new_patts_so_far @ new_patts)
        else
          _filter_dominated
            rhs_patts_rest
            (dominates || has_dominated)
            (rhs_patt :: rhs_patts_unfiltered_rev)
            (new_patts_so_far @ new_patts)
        end
  in
  let (dominates, rhs_patts_unfiltered_rev, new_patts_so_far) =
    _filter_dominated rhs_patts false [] []
  in
  let rhs_patts_unfiltered = List.rev rhs_patts_unfiltered_rev in
  let all_unfiltered_patts =
    List.append rhs_patts_unfiltered new_patts_so_far
  in
  (dominates, all_unfiltered_patts)

(* Returns a pair. The left list is the list of patterns that are useless
because the patterns before them are sufficient to match all pattern values, and
the right list is the list of pattern values not matched by any pattern (lacking
exhaustion). *)
and determine_pattern_completeness lhs_patts rhs_patts =
  let rec _determine_pattern_completeness
    lhs_patts_useless lhs_patts_rest rhs_patts_rest
  =
    begin match (lhs_patts_rest, rhs_patts_rest) with
    | ([], []) -> ((List.rev lhs_patts_useless), [])
    | (_, []) -> ((List.rev lhs_patts_useless) @ lhs_patts_rest, [])
    | ([], _) -> ((List.rev lhs_patts_useless), rhs_patts_rest)
    | (patt::lhs_patts_rest, _) ->
        (* Non-exhaustion of patterns is when there are remaining pattern values
        after exhausting all match pattern arms. *)
        let (dominated, filtered_rhs_patts) =
          filter_dominated patt rhs_patts_rest
        in
        (* Useless patterns are patterns that did not dominate any of the
        remaining pattern values. *)
        let lhs_patts_useless =
          if not dominated
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
  | UnboundSize(_) -> failwith "Cannot generate values for unbound size"
  | SizeTemplatedArray(_, _) ->
      failwith "Cannot generate values for templated array type"
  | VarArgSentinel -> failwith "Cannot generate values for var-arg sentinel"

  | Nil -> [PNil]

  | U64 | U32 | U16 | U8
  | I64 | I32 | I16 | I8 -> [PInt(Undecided, IRangeAll)]

  | F128 | F64 | F32 -> [RequireWild(t)]

  | String -> [RequireWild(t)]

  | Array(_, _) -> failwith "generate_value_patts: Array: Unimplemented"

  | Tuple(ts) ->
      let ts_patts = List.map generate_value_patts ts in
      let ts_patts_cart_prod = cartesian_product ts_patts in
      List.map (fun ts_patt -> PTuple(t, ts_patt)) ts_patts_cart_prod

  | Ref(_) -> [RequireWild(t)]
  | Function(_, _) -> failwith "generate_value_patts: Function: Unimplemented"

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
          List.map (fmt_pattern ~print_typ:false) useless
        )
      in
      Printf.printf "Useless LHS pattern(s):\n%s\n%!" useless_fmt ;
      failwith "Match patterns must all be useful."

  | ([], unmatched) ->
      let unmatched_fmt =
        fmt_join_strs "\n" (
          List.map (fmt_pattern ~print_typ:false) unmatched
        )
      in
      Printf.printf "Unmatched pattern value(s):\n%s\n%!" unmatched_fmt ;
      failwith "Match patterns must be exhaustive."

  | (useless, unmatched) ->
      let unmatched_fmt =
        fmt_join_strs "\n" (
          List.map (fmt_pattern ~print_typ:false) unmatched
        )
      in
      let useless_fmt =
        fmt_join_strs "\n" (
          List.map (fmt_pattern ~print_typ:false) useless
        )
      in
      Printf.printf "Unmatched pattern value(s):\n%s\n%!" unmatched_fmt ;
      Printf.printf "Useless LHS pattern(s):\n%s\n%!" useless_fmt ;
      failwith (
        "Match patterns must be exhaustive and not contain useless patterns."
      )
