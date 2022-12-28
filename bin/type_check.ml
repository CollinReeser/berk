open Ast
open Pretty_print
open Typing

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
  end in

  let _ = if verbose then
    begin
      Printf.printf "is_concrete_stmt[[ " ;
      print_stmt ~print_typ:true "" stmt ;
      Printf.printf " ]] == %B\n%!" res
    end
  else
    ()
  in

  res

and is_concrete_expr ?(verbose=false) expr =
  let _is_concrete_expr expr = is_concrete_expr ~verbose:verbose expr in
  let _is_concrete_stmt stmt = is_concrete_stmt ~verbose:verbose stmt in
  let _is_concrete_type typ  = is_concrete_type ~verbose:verbose typ in

  let res = begin match expr with
  | ValU64(_)  | ValU32(_) | ValU16(_) | ValU8(_)
  | ValI64(_)  | ValI32(_) | ValI16(_) | ValI8(_)
  | ValF128(_) | ValF64(_) | ValF32(_)
  | ValBool(_)
  | ValStr(_)
  | ValNil -> true

  | ValVar(typ, _) -> _is_concrete_type typ

  | ValCastTrunc(typ, expr)
  | ValCastBitwise(typ, expr)
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

  | WhileExpr(typ, expr_1, stmts, expr_2) ->
      (_is_concrete_type typ) &&
        (_is_concrete_expr expr_1) &&
        (_is_concrete_expr expr_2) &&
        (List.fold_left (&&) true (List.map _is_concrete_stmt stmts))

  | ArrayExpr(typ, exprs)
  | TupleExpr(typ, exprs)
  | FuncCall(typ, _, exprs) ->
      (_is_concrete_type typ) &&
        (List.fold_left (&&) true (List.map _is_concrete_expr exprs))
  end in

  let _ = if verbose then
    begin
      Printf.printf "is_concrete_stmt[[ " ;
      print_expr ~print_typ:true "" expr ;
      Printf.printf " ]] == %B\n%!" res
    end
  else
    ()
  in

  res
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
        if type_convertible_to exp_t decl_t
        then decl_t
        else
          begin
            Printf.printf (
                "Explicitly declared type [[ %s ]] " ^^
                "disagrees with deduced type [[ %s ]] "
              )
              (fmt_type decl_t)
              (fmt_type exp_t) ;
            Printf.printf "over expression [[ " ;
            print_expr ~print_typ:true "" exp_typechecked ;
            Printf.printf " ]]\n%!" ;
            failwith "Explicitly declared type disagrees with expr"
          end
      in

      let vars_up = StrMap.add ident (resolved_t, qual) tc_ctxt.vars in
      let tc_ctxt_up = {tc_ctxt with vars = vars_up} in

      (tc_ctxt_up, DeclStmt(ident, qual, resolved_t, exp_typechecked))

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

  | AssignStmt(ident, exp) ->
      let (var_t, {mut}) = StrMap.find ident tc_ctxt.vars in

      let exp_typechecked = type_check_expr tc_ctxt var_t exp in
      let exp_t = expr_type exp_typechecked in

      let _ =
        if mut
          then ()
          else failwith "Cannot assign to immutable var"
      in

      if type_convertible_to exp_t var_t
        then (tc_ctxt, AssignStmt(ident, exp_typechecked))
        else failwith "Expr for assignment does not typecheck"

  | AssignDeconStmt(idents, exp) ->
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

          (tc_ctxt, AssignDeconStmt(idents, exp_typechecked))

        | Tuple(types) ->
          let _ =
            if List.length idents == List.length types
              then typecheck_id_typ_pairs idents types
              else failwith "Mismatch in number of idents vs tuple expr in assi"
          in

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

    | ValVar(_, id) ->
        let (var_t, _) = StrMap.find id tc_ctxt.vars in
        ValVar(var_t, id)

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

    | BinOp(_, op, lhs, rhs) ->
        begin match op with
        | Add | Sub | Mul | Div | Mod ->
            let lhs_typechecked = _type_check_expr lhs in
            let rhs_typechecked = _type_check_expr rhs in
            let lhs_t = expr_type lhs_typechecked in
            let rhs_t = expr_type rhs_typechecked in
            let common_t = common_type_of_lr lhs_t rhs_t in
            BinOp(common_t, op, lhs_typechecked, rhs_typechecked)

        | Eq | NotEq | Less | LessEq | Greater | GreaterEq ->
            let lhs_typechecked = _type_check_expr lhs in
            let rhs_typechecked = _type_check_expr rhs in
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

        let then_expr_typechecked = _type_check_expr then_expr in
        let then_expr_t = expr_type then_expr_typechecked in

        let else_expr_typechecked = _type_check_expr else_expr in
        let else_expr_t = expr_type else_expr_typechecked in

        let _ = match if_cond_t with
        | Bool -> ()
        | _ -> failwith "if-expr condition must resolve to Bool"
        in

        let then_else_agreement_t = common_type_of_lr then_expr_t else_expr_t in

        IfThenElseExpr(
          then_else_agreement_t,
          if_cond_typechecked,
          then_expr_typechecked,
          else_expr_typechecked
        )

    | WhileExpr(_, while_cond, then_stmts, finally_expr) ->
        let while_cond_typechecked = _type_check_expr while_cond in
        let while_cond_t = expr_type while_cond_typechecked in

        let (_, then_stmts_typechecked) = type_check_stmts tc_ctxt then_stmts in

        let finally_expr_typechecked = _type_check_expr finally_expr in
        let finally_expr_t = expr_type finally_expr_typechecked in

        let _ = match while_cond_t with
        | Bool -> ()
        | _ -> failwith "if-expr condition must resolve to Bool"
        in

        WhileExpr(
          finally_expr_t,
          while_cond_typechecked,
          then_stmts_typechecked,
          finally_expr_typechecked
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

        let take lst n =
          let rec _take accum remain n =
            begin match (remain, n) with
            | (_, 0)  -> accum
            | ([], _) -> failwith "Could not take remaining items: empty list"
            | (x::xs, _) -> _take (accum @ [x]) xs (n - 1)
            end
          in
          _take [] lst n
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
        let idx_typechecked = _type_check_expr idx in
        let arr_typechecked = _type_check_expr arr in
        let idx_t = expr_type idx_typechecked in
        let arr_t = expr_type arr_typechecked in
        if is_index_type idx_t && is_indexable_type arr_t
          then
            begin match arr_t with
            | Array(elem_typ, sz) ->
                begin match idx_typechecked with
                  | ValU64(i)
                  | ValU32(i)
                  | ValU16(i)
                  | ValU8(i) ->
                      if i < sz
                        then
                          IndexExpr(
                            elem_typ, idx_typechecked, arr_typechecked
                          )
                        else failwith "Static out-of-bounds index into array"
                  | _ ->
                      IndexExpr(
                        elem_typ, idx_typechecked, arr_typechecked
                      )
                end
            | _ -> failwith "Unexpected index target in index expr"
            end
          else failwith "Unexpected components of index operation"

    | StaticIndexExpr(_, idx, arr) ->
        let arr_typechecked = _type_check_expr arr in
        let arr_t = expr_type arr_typechecked in
        let static_idx_typechecked = begin
          match arr_t with
          | Array(elem_typ, sz) ->
            begin
              if idx < 0 || idx >= sz
              then failwith "out-of-bounds idx for array"
              else StaticIndexExpr(elem_typ, idx, arr_typechecked)
            end
          | _ -> failwith "Unexpectedly indexing into non-array"
        end in

        static_idx_typechecked

    | TupleExpr(_, exprs) ->
        let elem_expected_t_lst = begin match expected_t with
          | Tuple(typs) -> typs
          | Undecided ->
              let tuple_len = List.length exprs in
              List.init tuple_len (fun _ -> Undecided)
          | _ -> failwith "Unexpectedly expecting non-array type in array expr"
        end in

        let exprs_typechecked =
          List.map2 (type_check_expr tc_ctxt) elem_expected_t_lst exprs
        in
        let exprs_t_lst = List.map expr_type exprs_typechecked in
        let tuple_t = Tuple(exprs_t_lst) in

        TupleExpr(tuple_t, exprs_typechecked)

    | VariantCtorExpr(_, ctor_name, ctor_exp) ->
        let ctor_exp_typechecked = _type_check_expr ctor_exp in
        let ctor_exp_typ = expr_type ctor_exp_typechecked in
        let resolved_v_t : berk_t =
          variant_ctor_to_variant_type tc_ctxt.mod_ctxt ctor_name ctor_exp_typ
        in

        let final_v_t = begin match expected_t with
          | Undecided -> resolved_v_t
          | Variant(_, _) ->
            if not (is_concrete_type expected_t) then
              failwith "Variant expression given explicit but unresolved type"
            else
              let tvars_to_t = map_tvars_to_types resolved_v_t expected_t in
              concretify_unbound_types tvars_to_t resolved_v_t
          | _ ->
            failwith "Unexpected non-variant type expected in variant ctor expr"
        end in

        VariantCtorExpr(final_v_t, ctor_name, ctor_exp_typechecked)
  end in

  let exp_typechecked = _type_check_expr exp in

  let _ = if is_concrete_expr exp_typechecked then
      ()
    else
      begin
        Printf.printf "[" ;
        print_expr ~print_typ:true "" exp_typechecked ;
        Printf.printf "]\n%!" ;
        failwith "Non-concrete expr!"
      end
    in

  exp_typechecked
;;
