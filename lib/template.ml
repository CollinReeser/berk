(* Functions and infrastructure for "instantiating" templated function
signatures and function definitions, yielding "concrete" (but possibly
incompletely typechecked) versions of the input. These functions fail if a
given template cannot be fully concretified. *)

open Ast
open Typing
open Utility

module StrMap = Map.Make(String)

(* Format a type for the purposes of function name mangling. *)
let rec fmt_type_mangle t : string =
  Printf.printf "Mangling: %s\n%!" (fmt_type t) ;

  begin match t with
  | VarArgSentinel
  | Unbound(_)
  | UnboundType(_)
  | UnboundSize(_)
  | SizeTemplatedArray(_, _)
  | Undecided ->
      failwith (
        Printf.sprintf "Error: fmt_type_mangle: unsupported for %s" (fmt_type t)
      )

  | Nil -> "n"

  | U64 -> "u6"
  | U32 -> "u3"
  | U16 -> "u1"
  | U8  -> "u"
  | I64 -> "i6"
  | I32 -> "i3"
  | I16 -> "i1"
  | I8  -> "i"
  | F128 -> "f1"
  | F64  -> "f6"
  | F32  -> "f3"
  | Bool -> "b"
  | String -> "s"

  | Ref (refed_t) -> Printf.sprintf "r%s" (fmt_type_mangle refed_t)
  | Array (arr_t, sz) -> Printf.sprintf "a%d%s" sz (fmt_type_mangle arr_t)

  | Tuple (ts) ->
      Printf.sprintf "t%szt" (fmt_join_strs "" (List.map fmt_type_mangle ts))

  | Variant (name, v_ctors) ->
      Printf.sprintf
        "V%sh%szV"
        name
        (fmt_join_strs "" (List.map fmt_v_ctor_mangle v_ctors))

  | Function (ret_t, arg_ts) ->
      Printf.sprintf "F%sh%szF"
        (fmt_type_mangle ret_t)
        (fmt_join_strs "" (List.map fmt_type_mangle arg_ts))
  end

and fmt_v_ctor_mangle {name; fields} : string =
  let fields_ts = List.map (fun {t} -> t) fields in
  Printf.sprintf
    "v%sh%svz"
    name
    (fmt_join_strs "" (List.map fmt_type_mangle fields_ts))
;;

(* Given an initial function name, and the argument types and return type, yield
a deterministic mangled name. *)
let mangle_f_name f_name (arg_ts : berk_t list) ret_t : string =
  (* Get the list of instantiating types in sorted order (courtesy of the
  behavior of `bindings`). *)
  let mangled_args_fmt = fmt_join_strs "_" (List.map fmt_type_mangle arg_ts) in
  let mangled_ret_fmt = fmt_type_mangle ret_t in
  Printf.sprintf "%s_R%s_%s" f_name mangled_ret_fmt mangled_args_fmt
;;


let tvars_to_ts_from_tvars_to_args tvars_to_args =
  List.fold_left (
    fun tvars_to_ts (tvar, arg) ->
      begin match arg with
      | TemplateType(t) -> StrMap.add tvar t tvars_to_ts
      | _ -> tvars_to_ts
      end
  ) StrMap.empty (StrMap.bindings tvars_to_args)
;;


let update_tvars_to_args_with_tvars_to_ts tvars_to_args tvars_to_ts =
  List.fold_left (
    fun tvars_to_args (tvar, t) ->
      StrMap.add tvar (TemplateType(t)) tvars_to_args
  ) tvars_to_args (StrMap.bindings tvars_to_ts)
;;


let instantiate_func_template_decl
  {f_name; f_params; f_ret_t}
  (tvars_to_ts : berk_t StrMap.t)
  func_arg_ts
  : (berk_t StrMap.t * func_decl_t)
=
  (* Attempt to acquire a mapping from type variables to types, given the
  arguments to the function, and any tvars that might be in the templated
  function signature. *)
  let tvars_to_ts =
    List.fold_left2 (
      fun tvars_to_ts (_, _, param_t) arg_t ->
        map_tvars_to_types ~init_map:tvars_to_ts param_t arg_t
    ) tvars_to_ts f_params func_arg_ts
  in

  (* Attempt to fully instantiate the parameters of the templated signature. *)
  let f_params =
    List.map (
      fun (name, qual, t) ->
        let concrete_t = concretify_unbound_types tvars_to_ts t in

        if (is_concrete_type ~verbose:true concrete_t) then
          (name, qual, concrete_t)
        else
          failwith (
            Printf.sprintf
              "Error: instantiate_func_template_decl: type %s\n"
              (fmt_type t)
          )

    ) f_params
  in

  (* Attempt to fully instantiate the return type of the templated signature. *)
  let f_ret_t = begin
    let concrete_t = concretify_unbound_types tvars_to_ts f_ret_t in

    if (is_concrete_type ~verbose:true concrete_t) then
      concrete_t
    else
      failwith (
        Printf.sprintf
          "Error: instantiate_func_template_decl: type %s\n"
          (fmt_type concrete_t)
      )
  end in

  (tvars_to_ts, {f_name; f_params; f_ret_t})
;;


(* Attempt to unify a templated extern fn declaration with the types of the
arguments used to instantiate it. *)
let instantiate_func_extern_template_decl
  {
    f_template_decl=f_template_decl;
    f_template_params
  }
  (tvars_to_ts : berk_t StrMap.t)
  func_arg_ts
  : func_decl_t
=
  f_template_params |> ignore;

  let (_, f_decl) =
    instantiate_func_template_decl
      f_template_decl tvars_to_ts func_arg_ts
  in
  f_decl
;;


let rec instantiate_patt
  (tvars_to_args : template_arg StrMap.t)
  patt
  : pattern
=
  let tvars_to_ts = tvars_to_ts_from_tvars_to_args tvars_to_args in

  let _instantiate_patt p = instantiate_patt tvars_to_args p in
  let _concretify_unbound_types t = concretify_unbound_types tvars_to_ts t in

  begin match patt with
  | PNil
  | PBool(_) -> patt

  | Wild(t) -> Wild(_concretify_unbound_types t)
  | RequireWild(t) -> RequireWild(_concretify_unbound_types t)
  | VarBind(t, name) -> VarBind(_concretify_unbound_types t, name)
  | PInt(t, range) -> PInt(_concretify_unbound_types t, range)

  | PTuple(t, patts) ->
      PTuple(_concretify_unbound_types t, List.map _instantiate_patt patts)

  | Ctor(t, name, patts) ->
      Ctor(_concretify_unbound_types t, name, List.map _instantiate_patt patts)

  | PatternAs(t, patt, name) ->
      PatternAs(_concretify_unbound_types t, _instantiate_patt patt, name)
  end
;;


let rec instantiate_expr
  (tvars_to_args : template_arg StrMap.t)
  exp
  : expr
=
  let tvars_to_ts = tvars_to_ts_from_tvars_to_args tvars_to_args in

  let _instantiate_expr e = instantiate_expr tvars_to_args e in
  let _concretify_unbound_types t = concretify_unbound_types tvars_to_ts t in

  begin match exp with
  | ValF128(_) | ValF64(_) | ValF32(_)
  | ValBool(_)
  | ValStr(_)
  | ValNil -> exp

  | ValInt(t, i) -> ValInt(_concretify_unbound_types t, i)

  | ValVar(t, name) -> ValVar(_concretify_unbound_types t, name)
  | ValFunc(t, name) -> ValFunc(_concretify_unbound_types t, name)
  | ValName(t, name) -> ValName(_concretify_unbound_types t, name)

  | ValRawArray(t) -> ValRawArray(_concretify_unbound_types t)

  | RefOf(t, e) -> RefOf(_concretify_unbound_types t, _instantiate_expr e)
  | DerefOf(t, e) -> DerefOf(_concretify_unbound_types t, _instantiate_expr e)

  | ValCast(t, op, e) ->
      ValCast(_concretify_unbound_types t, op, _instantiate_expr e)

  | UnOp(t, op, e) ->
      UnOp(_concretify_unbound_types t, op, _instantiate_expr e)

  | BinOp(t, op, lhs_e, rhs_e) ->
      BinOp(
        _concretify_unbound_types t,
        op,
        _instantiate_expr lhs_e,
        _instantiate_expr rhs_e
      )

  | TupleIndexExpr(t, i, e) ->
      TupleIndexExpr(_concretify_unbound_types t, i, _instantiate_expr e)

  | IndexExpr(t, idx_e, arr_e) ->
      IndexExpr(
        _concretify_unbound_types t,
        _instantiate_expr idx_e,
        _instantiate_expr arr_e
      )

  | IfThenElseExpr(t, cond_e, then_e, else_e) ->
      IfThenElseExpr(
        _concretify_unbound_types t,
        _instantiate_expr cond_e,
        _instantiate_expr then_e,
        _instantiate_expr else_e
      )

  | IfIsThenElseExpr(t, cond_es, then_e, else_e) ->
      let concrete_cond_es =
        List.map (
          fun cond ->
            begin match cond with
            | IfIsGeneral(e) -> IfIsGeneral(_instantiate_expr e)
            | IfIsPattern(e, patt) ->
                IfIsPattern(
                  _instantiate_expr e, instantiate_patt tvars_to_args patt
                )
            end
        ) cond_es
      in

      IfIsThenElseExpr(
        _concretify_unbound_types t,
        concrete_cond_es,
        _instantiate_expr then_e,
        _instantiate_expr else_e
      )

  | BlockExpr(t, stmts, e) ->
      BlockExpr(
        _concretify_unbound_types t,
        instantiate_stmts tvars_to_args stmts,
        _instantiate_expr e
      )

  | WhileExpr(t, init_stmts, cond_e, then_stmts) ->
      WhileExpr(
        _concretify_unbound_types t,
        instantiate_stmts tvars_to_args init_stmts,
        _instantiate_expr cond_e,
        instantiate_stmts tvars_to_args then_stmts
      )

  | ArrayExpr(t, es) ->
      ArrayExpr(_concretify_unbound_types t, List.map _instantiate_expr es)

  | TupleExpr(t, es) ->
      TupleExpr(_concretify_unbound_types t, List.map _instantiate_expr es)

  | FuncCall(t, name, es) ->
      FuncCall(_concretify_unbound_types t, name, List.map _instantiate_expr es)

  | VariantCtorExpr(t, name, es) ->
      VariantCtorExpr(
        _concretify_unbound_types t,
        name,
        List.map _instantiate_expr es
      )

  | UfcsCall(t, e, name, i, es) ->
      UfcsCall(
        _concretify_unbound_types t,
        _instantiate_expr e,
        name,
        i,
        List.map _instantiate_expr es
      )

  | ExprInvoke(t, func_e, es) ->
      ExprInvoke(
        _concretify_unbound_types t,
        _instantiate_expr func_e,
        List.map _instantiate_expr es
      )

  | MatchExpr(t, matched_e, patt_e_pairs) ->
      let concrete_patt_e_pairs =
        List.map (
          fun (patt, e) ->
            (instantiate_patt tvars_to_args patt, _instantiate_expr e)
        ) patt_e_pairs
      in

      MatchExpr(
        _concretify_unbound_types t,
        _instantiate_expr matched_e,
        concrete_patt_e_pairs
      )

  | TemplateVar(tv) ->
      let arg = StrMap.find tv tvars_to_args in
      begin match arg with
      | TemplateExpr(e) -> _instantiate_expr e
      | TemplateType(UnboundSize(sz)) -> ValInt(Undecided, sz)
      | _ ->
          failwith (
            Printf.sprintf "Error: Cannot instantiate TemplateVar with %s"
              (dump_template_arg_ast arg)
          )
      end

  | TemplateMixinCall(tv, arg_es) ->
      let concrete_arg_es = List.map _instantiate_expr arg_es in

      let arg = StrMap.find tv tvars_to_args in
      begin match arg with
      | TemplateMixin(params, body_e) ->
          if List.length concrete_arg_es <> List.length params then
            failwith (
              Printf.sprintf
                "Error: Mismatch in arguments to parameters in: %s of %s"
                (fmt_expr exp)
                (dump_template_arg_ast arg)
            )
          ;

          (* TODO: This is pretty weak, but should do the job for now. *)
          let uniq_params =
            List.fold_left (
              fun uniq_params param ->
                StrMap.add param ("__" ^ param) uniq_params
            ) StrMap.empty params
          in

          (* Create let bindings to create named variables that map to the
          expression arguments the mixin was called with. *)
          let bindings =
            List.map2 (
              fun param concrete_e ->
                let uniq_param = StrMap.find param uniq_params in
                DeclStmt(uniq_param, {mut=false}, Undecided, concrete_e)
            ) params concrete_arg_es
          in

          (* Locally update the template variable mapping to include mappings
          from the mixin parameters to their new named let-binding variables. *)
          let tvars_to_args =
            List.fold_left (
              fun tvars_to_args param ->
                let uniq_param = StrMap.find param uniq_params in
                let t_e = TemplateExpr(ValVar(Undecided, uniq_param)) in
                StrMap.add param t_e tvars_to_args
            ) tvars_to_args params
          in

          (* Instantiate the body of the mixin with our _updated_ mapping of
          tvars_to_args that includes the mapping from the mixin's params to
          the named variables created from let bindings that bind variable names
          to the mixin params. *)
          let concrete_body_e = instantiate_expr tvars_to_args body_e in

          BlockExpr(
            Undecided,
            bindings,
            concrete_body_e
          )

      | _ ->
          failwith (
            Printf.sprintf "Error: Cannot instantiate TemplateMixinCall with %s"
              (dump_template_arg_ast arg)
          )
      end
  end


and instantiate_assign_idx_lval
  tvars_to_args assign_idx_lval : assign_idx_lval
=
  let tvars_to_ts = tvars_to_ts_from_tvars_to_args tvars_to_args in

  let _instantiate_expr e = instantiate_expr tvars_to_args e in
  let _concretify_unbound_types t = concretify_unbound_types tvars_to_ts t in

  begin match assign_idx_lval with
  | ALStaticIndex(t, i) -> ALStaticIndex(_concretify_unbound_types t, i)
  | ALIndex(t, e) -> ALIndex(_concretify_unbound_types t, _instantiate_expr e)
  | ALDeref(t) -> ALDeref(_concretify_unbound_types t)
  end


and instantiate_stmt tvars_to_args stmt : stmt =
  let tvars_to_ts = tvars_to_ts_from_tvars_to_args tvars_to_args in

  let _instantiate_expr e = instantiate_expr tvars_to_args e in
  let _concretify_unbound_types t = concretify_unbound_types tvars_to_ts t in

  begin match stmt with
  | YieldStmt(e) -> YieldStmt(_instantiate_expr e)
  | ReturnStmt(e) -> ReturnStmt(_instantiate_expr e)
  | ExprStmt(stmt_mod, e) -> ExprStmt(stmt_mod, _instantiate_expr e)

  | DeclStmt(name, qual, decl_t, e) ->
      DeclStmt(
        name,
        qual,
        _concretify_unbound_types decl_t,
        _instantiate_expr e
      )

  | DeclDefaultStmt(name_qual_t_lst) ->
      let concrete_name_qual_t_lst =
        List.map (
          fun (name, qual, t) ->
            (name, qual, _concretify_unbound_types t)
        ) name_qual_t_lst
      in

      DeclDefaultStmt(concrete_name_qual_t_lst)

  | DeclDeconStmt(name_qual_lst, decl_t, e) ->
      DeclDeconStmt(
        name_qual_lst, _concretify_unbound_types decl_t, _instantiate_expr e
      )

  | AssignStmt(name, decl_t, assign_idx_lvals, e) ->
      AssignStmt(
        name,
        _concretify_unbound_types decl_t,
        List.map (instantiate_assign_idx_lval tvars_to_args) assign_idx_lvals,
        _instantiate_expr e
      )

  end


and instantiate_stmts
  (tvars_to_args : template_arg StrMap.t)
  stmts
  : stmt list
=
  List.map (instantiate_stmt tvars_to_args) stmts
;;


(* Attempt to create a fully instantiated concrete function definition given
the template and the arguments and template arguments used to instantiate. *)
let instantiate_func_template_def
  {
    f_template_def_decl={f_template_params; f_template_decl=f_template_decl};
    f_template_stmts
  }
  (tvars_to_args : template_arg StrMap.t)
  func_arg_ts
  : func_def_t
=
  f_template_params |> ignore;

  let tvars_to_ts = tvars_to_ts_from_tvars_to_args tvars_to_args in

  let (tvars_to_ts, {f_name; f_params; f_ret_t}) =
    instantiate_func_template_decl
      f_template_decl tvars_to_ts func_arg_ts
  in

  let tvars_to_args =
    update_tvars_to_args_with_tvars_to_ts tvars_to_args tvars_to_ts
  in

  let f_stmts = instantiate_stmts tvars_to_args f_template_stmts in

  let f_name_mangled =
    mangle_f_name f_name (List.map (fun (_, _, t) -> t) f_params) f_ret_t
  in

  Printf.printf "Name mangling: [%s] -> [%s]\n%!" f_name f_name_mangled ;

  let f_decl = {f_name=f_name_mangled; f_params; f_ret_t} in
  let func_def = {f_decl; f_stmts} in
  func_def
;;
