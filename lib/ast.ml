open Typing
open Ir
open Utility


(*
AST for the berk language.
*)

type ident_t = string

and maybe_bounds_check =
  | NoBoundsCheck
  | DoBoundsCheck
  | Undecided

and expr =
  | ValNil
  | ValU64 of int
  | ValU32 of int
  | ValU16 of int
  | ValU8  of int
  | ValI64 of int
  | ValI32 of int
  | ValI16 of int
  | ValI8  of int
  | ValF128 of string
  | ValF64 of float
  | ValF32 of float
  | ValBool of bool
  | ValStr of string
  | ValVar of berk_t * ident_t
  | ValFunc of berk_t * string
  | ValCastTrunc of berk_t * expr
  | ValCastBitwise of berk_t * expr
  | ValCastExtend of berk_t * expr
  | BinOp of berk_t * bin_op * expr * expr
  (* Sequence of statements followed by an expression, where if the expression
  is None, then the BlockExpr resolves to a nil value. *)
  | BlockExpr of berk_t * stmt list * expr
  (* if expr, then expr, else expr *)
  | IfThenElseExpr of berk_t * expr * expr * expr
  (* while expr, then stmts, else expr *)
  | WhileExpr of berk_t * expr * stmt list * expr
  (* A direct call to an in-scope named function. *)
  | FuncCall of berk_t * ident_t * expr list
  (* An indirect invocation of a function inside a variable. *)
  | VarInvoke of berk_t * ident_t * expr list
  | ArrayExpr of berk_t * expr list
  (* First expr is index, second is array *)
  | IndexExpr of berk_t * expr * expr
  (* int is index, expr is array *)
  | StaticIndexExpr of berk_t * int * expr
  | TupleExpr of berk_t * expr list
  (* Top-level variant type, ctor name, ctor expr,  *)
  | VariantCtorExpr of berk_t * string * expr

and stmt =
  | DeclStmt of ident_t * var_qual * berk_t * expr
  | DeclDeconStmt of (ident_t * var_qual) list * berk_t * expr
  | AssignStmt of ident_t * expr
  | AssignDeconStmt of ident_t list * expr
  | ExprStmt of expr
  | ReturnStmt of expr
;;

let expr_type exp =
  match exp with
  | ValNil -> Nil
  | ValU64(_) -> U64
  | ValU32(_) -> U32
  | ValU16(_) -> U16
  | ValU8(_)  -> U8
  | ValI64(_) -> I64
  | ValI32(_) -> I32
  | ValI16(_) -> I16
  | ValI8(_)  -> I8
  | ValF128(_) -> F128
  | ValF64(_)  -> F64
  | ValF32(_)  -> F32
  | ValBool(_) -> Bool
  | ValStr(_) -> String
  | ValVar(typ, _) -> typ
  | ValFunc(typ, _) -> typ
  | ValCastTrunc(typ, _) -> typ
  | ValCastBitwise(typ, _) -> typ
  | ValCastExtend(typ, _) -> typ
  | BinOp(typ, _, _, _) -> typ
  | BlockExpr(typ, _, _) -> typ
  | IfThenElseExpr(typ, _, _, _) -> typ
  | WhileExpr(typ, _, _, _) -> typ
  | FuncCall(typ, _, _) -> typ
  | VarInvoke(typ, _, _) -> typ
  | ArrayExpr(typ, _) -> typ
  | IndexExpr(typ, _, _) -> typ
  | StaticIndexExpr(typ, _, _) -> typ
  | TupleExpr(typ, _) -> typ
  | VariantCtorExpr(typ, _, _) -> typ
;;

let fmt_bin_op op =
  match op with
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%%"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="

let rec fmt_join_exprs ?(print_typ = false) ind delim exprs : string =
  match exprs with
  | [] -> ""
  | [x] -> fmt_expr ~print_typ:print_typ ind x
  | x::xs ->
      (fmt_expr ~print_typ:print_typ ind x) ^ delim ^
      (fmt_join_exprs ~print_typ:print_typ ind delim xs)

and fmt_expr ?(init_ind = false) ?(print_typ = false) ind ex : string =
  let init_ind = if init_ind then ind else "" in
  let (typ_s, typ_s_rev) =
    if print_typ
    then
      let typ_formatted = expr_type ex |> fmt_type in
      (Printf.sprintf ":%s" typ_formatted, Printf.sprintf "%s:" typ_formatted)
    else ("", "")
  in
  match ex with
  | ValNil -> Printf.sprintf "%s()%s" init_ind typ_s

  | ValU64(value) | ValU32(value) | ValU16(value) | ValU8(value) ->
      Printf.sprintf "%s%d%s" init_ind value typ_s

  | ValI64(value) | ValI32(value) | ValI16(value) | ValI8(value) ->
      Printf.sprintf "%s%d%s" init_ind value typ_s

  | ValF128(str) -> Printf.sprintf "%s%s%s" init_ind str typ_s

  | ValF64(value) | ValF32(value) ->
      Printf.sprintf "%s%f%s" init_ind value typ_s

  | ValBool(value) -> Printf.sprintf "%s%B%s" init_ind value typ_s

  | ValStr(str) ->
      Printf.sprintf "%s\"%s\"%s" init_ind (String.escaped str) typ_s

  | ValVar(_, id) -> Printf.sprintf "%s%s%s" init_ind id typ_s

  | ValFunc(_, func_name) ->
      Printf.sprintf "%sfn<%s%s>" init_ind func_name typ_s

  | ValCastTrunc (target_t, exp) ->
      Printf.sprintf "%scast_trunc<%s>(%s)%s"
        init_ind
        (fmt_type target_t)
        (fmt_expr ~print_typ:print_typ "" exp)
        typ_s

  | ValCastBitwise (target_t, exp) ->
      Printf.sprintf "%scast_bitwise<%s>(%s)%s"
        init_ind
        (fmt_type target_t)
        (fmt_expr ~print_typ:print_typ "" exp)
        typ_s

  | ValCastExtend (target_t, exp) ->
      Printf.sprintf "%scast_extend<%s>(%s)%s"
        init_ind
        (fmt_type target_t)
        (fmt_expr ~print_typ:print_typ "" exp)
        typ_s

  | BinOp (_, op, lh, rh) ->
      Printf.sprintf "%s(%s %s %s)%s"
        init_ind
        (fmt_expr ~print_typ:print_typ "" lh)
        (fmt_bin_op op)
        (fmt_expr ~print_typ:print_typ "" rh)
        typ_s

  | BlockExpr (_, stmts, exp) ->
      let formatted_stmts =
        List.fold_left (^) "" (
          List.map (fmt_stmt ~print_typ:print_typ (ind ^ "  ")) stmts
        )
      in
      Printf.sprintf "%s%s{\n%s%s\n%s}"
        init_ind
        typ_s_rev
        formatted_stmts
        (fmt_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") exp)
        ind
  | IfThenElseExpr (_, if_cond, then_expr, else_expr) ->
      Printf.sprintf "%s%sif (%s) {\n%s\n%s} else {\n%s\n%s}"
        init_ind
        typ_s_rev
        (fmt_expr ~print_typ:print_typ "" if_cond)
        (fmt_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") then_expr)
        ind
        (fmt_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") else_expr)
        ind

  | WhileExpr (_, while_cond, then_stmts, finally_expr) ->
      let formatted_stmts =
        List.fold_left (^) "" (
          List.map (fmt_stmt ~print_typ:print_typ (ind ^ "  ")) then_stmts
        )
      in

      Printf.sprintf "%s%swhile (%s) {\n%s%s} finally {\n%s\n%s}"
        init_ind
        typ_s_rev
        (fmt_expr ~print_typ:print_typ "" while_cond)
        formatted_stmts
        ind
        (fmt_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") finally_expr)
        ind

  | FuncCall(_, id, exprs) ->
      Printf.sprintf "%s%s%s(%s)"
        init_ind
        typ_s_rev
        id
        (fmt_join_exprs ~print_typ:print_typ ind ", " exprs)

  | VarInvoke(_, id, exprs) ->
      Printf.sprintf "%s%s%s->(%s)"
        init_ind
        typ_s_rev
        id
        (fmt_join_exprs ~print_typ:print_typ ind ", " exprs)

  | ArrayExpr(_, exprs) ->
      Printf.sprintf "%s[%s]%s"
        init_ind
        (fmt_join_exprs ~print_typ:print_typ ind ", " exprs)
        typ_s

  | StaticIndexExpr(_, idx, arr) ->
      Printf.sprintf "%s%s[%d]->%s"
        init_ind
        (fmt_expr ~print_typ:print_typ "" arr)
        idx
        typ_s

  | IndexExpr(_, idx, arr) ->
      Printf.sprintf "%s%s[%s]->%s"
        init_ind
        (fmt_expr ~print_typ:print_typ "" arr)
        (fmt_expr ~print_typ:print_typ "" idx)
        typ_s

  | TupleExpr(_, exprs) ->
      Printf.sprintf "%s(%s)%s"
        init_ind
        (fmt_join_exprs ~print_typ:print_typ ind ", " exprs)
        typ_s

  | VariantCtorExpr(_, ctor_name, expr) ->
      Printf.sprintf "%s%s(%s)%s"
        init_ind
        ctor_name
        (fmt_expr ~print_typ:print_typ "" expr)
        typ_s

and fmt_join_idents_quals delim idents_quals : string =
  match idents_quals with
  | [] -> ""
  | [(ident, qual)] -> Printf.sprintf "%s%s" (fmt_var_qual qual) ident
  | (ident, qual)::xs ->
      Printf.sprintf "%s%s%s%s"
        (fmt_var_qual qual)
        ident
        delim
        (fmt_join_idents_quals delim xs)

and fmt_stmt ?(print_typ = false) ind stmt =
  match stmt with
  | DeclStmt (ident, qual, btype, ex) ->
      let typ_s = match btype with
        | Undecided -> ""
        | x -> fmt_type x |> Printf.sprintf ": %s"
      in
      Printf.sprintf "%slet %s%s%s = %s;\n"
        ind
        (fmt_var_qual qual)
        ident
        typ_s
        (fmt_expr ~print_typ:print_typ ind ex)

  | DeclDeconStmt (idents_quals, btype, ex) ->
      let typ_s = match btype with
        | Undecided -> ""
        | x -> fmt_type x |> Printf.sprintf ": %s"
      in
      Printf.sprintf "%slet (%s)%s = %s;\n"
        ind
        (fmt_join_idents_quals ", " idents_quals)
        typ_s
        (fmt_expr ~print_typ:print_typ ind ex)

  | AssignStmt (ident, ex) ->
      Printf.sprintf "%s%s = %s;\n"
        ind
        ident
        (fmt_expr ~print_typ:print_typ ind ex)

  | AssignDeconStmt (idents, ex) ->
      Printf.sprintf "%s(%s) = %s;\n"
        ind
        (fmt_join_strs ", " idents)
        (fmt_expr ~print_typ:print_typ ind ex);

  | ExprStmt (ex) ->
      Printf.sprintf "%s%s;\n"
        ind
        (fmt_expr ~print_typ:print_typ ind ex)

  | ReturnStmt (ex) ->
      Printf.sprintf "%sreturn %s;\n"
        ind
        (fmt_expr ~print_typ:print_typ ind ex)
;;

let pprint_expr ppf exp =
  Format.fprintf ppf "%s" (fmt_expr ~print_typ:true "" exp)
;;

(* Force-apply a top-level type to the given expression, recursively. *)
let rec inject_type_into_expr ?(ind="") injected_t exp =
  let exp_t = expr_type exp in
  let tvars_to_t = map_tvars_to_types injected_t exp_t in

  (* Shadow the old `injected_t`; we now have a possibly-more-concrete type. *)
  let injected_t = concretify_unbound_types tvars_to_t injected_t in

  if not (type_convertible_to exp_t injected_t) then
    failwith (
      "Injection type [[" ^ (fmt_type injected_t) ^
      "]] disagrees with existing " ^ "type [[" ^ (fmt_type exp_t) ^ "]]"
    )
  else
    match (injected_t, exp) with
    | (
        Function(inj_ret_t, inj_args_t_lst), (
          ValFunc(Function(has_ret_t, has_args_t_lst), _) |
          VarInvoke(Function(has_ret_t, has_args_t_lst), _, _)
        )
      ) ->
        let args_match =
          List.fold_left (=) true (
            List.map2 (=) inj_args_t_lst has_args_t_lst
          )
        in

        (* TODO: This is probably overly restrictive, but it's unclear
        how to handle non-matching argument types. *)
        if args_match then
          if has_ret_t = inj_ret_t then
            exp
          else if type_extendable_to has_ret_t inj_ret_t then
            ValCastExtend(inj_ret_t, exp)
          else
            failwith "Cannot extend func ret type to injected"
        else
          failwith "Cannot inject function type with non-matching args"


    | (Function(_, _), _) ->
        failwith (
          Printf.sprintf
            "Cannot inject function type into non-func value: [[ %s ]]"
            (fmt_expr ~print_typ:true "" exp)
        )

    | (Undecided, _) -> failwith "Refuse to inject undecided type into expr"

    | (Unbound(a), _) ->
        let exp_t = expr_type exp in
        begin match exp_t with
        | Unbound(b) ->
            if a = b then
              exp
            else
              failwith "Refuse to bind typevar to dissimilar typevar"
        | _ ->
            exp
        end

    | (_, ValCastTrunc  (t, _))
    | (_, ValCastExtend (t, _))
    | (_, ValCastBitwise(t, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCastExtend(injected_t, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into casted type [[ %s ]]"
              (fmt_type injected_t)
              (fmt_type t)
          )

    | (_, ValVar(t, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCastExtend(injected_t, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into var type [[ %s ]]"
              (fmt_type injected_t)
              (fmt_type t)
          )

    | (_, FuncCall(t, _, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCastExtend(injected_t, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into func ret_t [[ %s ]]"
              (fmt_type injected_t)
              (fmt_type t)
          )

    | (_, VarInvoke(t, _, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCastExtend(injected_t, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into invoke ret_t [[ %s ]]"
              (fmt_type injected_t)
              (fmt_type t)
          )

    | (_, BlockExpr(_, stmts, exp_res)) ->
        (* We're not smart enough yet to influence the types of any expressions
        within the statements within the block. So, just make sure the trailing
        expression is type-injected. *)
        let exp_res_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") injected_t exp_res
        in

        BlockExpr(injected_t, stmts, exp_res_injected)

    | (_, IndexExpr(_, idx_exp, arr_exp)) ->
        (* We can't use our injection type info to assist with typechecking the
        index expression, but we _can_ use it to assist in typechecking the
        indexed array itself, by assuming the array expression type is expected
        to be an "array of" the target type. *)
        let arr_t = expr_type arr_exp in
        let arr_injection_type = begin match arr_t with
          | Array(_, sz) -> Array(injected_t, sz)
          | _ -> failwith ("Unexpected non-array type: " ^ (fmt_type arr_t))
        end in
        let arr_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") arr_injection_type arr_exp
        in
        IndexExpr(injected_t, idx_exp, arr_exp_injected)

    | (_, StaticIndexExpr(_, idx, arr_exp)) ->
        (* We can't use our injection type info to assist with typechecking the
        index expression, but we _can_ use it to assist in typechecking the
        indexed array itself, by assuming the array expression type is expected
        to be an "array of" the target type. *)
        let arr_t = expr_type arr_exp in
        let arr_injection_type = begin match arr_t with
          | Array(_, sz) -> Array(injected_t, sz)
          | _ -> failwith ("Unexpected non-array type: " ^ (fmt_type arr_t))
        end in
        let arr_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") arr_injection_type arr_exp
        in
        StaticIndexExpr(injected_t, idx, arr_exp_injected)

    | (Array(elem_t, sz), ArrayExpr(_, elem_lst)) ->
        let elem_t_lst = List.init sz (fun _ -> elem_t) in
        let elem_exp_injected_lst =
          List.map2
            (inject_type_into_expr ~ind:(ind ^ "  ")) elem_t_lst elem_lst
        in
        ArrayExpr(injected_t, elem_exp_injected_lst)

    | (Tuple(exp_t_lst), TupleExpr(_, exp_lst)) ->
        let exp_injected_lst =
          List.map2 (inject_type_into_expr ~ind:(ind ^ "  ")) exp_t_lst exp_lst
        in
        TupleExpr(injected_t, exp_injected_lst)

    | (Tuple(_), _)
    | (_, TupleExpr(_, _))
    | (Array(_, _), _)
    | (_, ArrayExpr(_, _)) ->
        failwith (
          "Cannot inject incompatible aggregate types: " ^ (fmt_type injected_t)
        )

    (* BinOps are an interesting case because they can "switch types"
    arbitrarily deep into a nested bin-op tree, we don't want to eg
    propagate the expectation of a bool due to an eg LessEq op into the
    arithmetic branches, and in general we expect the bottom-up typecheck to
    have correctly inferred everything (or failed eagerly due to type
    mismatch.) *)
    | (_, BinOp(t, bin_op, lhs, rhs)) -> BinOp(t, bin_op, lhs, rhs)

    | (_, IfThenElseExpr(_, cond_exp, then_exp, else_exp)) ->
        (* The injected type into an if-expr should be the common type that
        all branches agree on, but that is still convertible to the injected
        type itself. Put another way, the "most concrete" type to use is the one
        that combines the possibly-incomplete information shared between the
        injected type, the then-branch type, and the else-branch type, but this
        common type must not be a superset of the injected type. *)

        let then_t = expr_type then_exp in
        let else_t = expr_type else_exp in
        let common_then_else_t = common_type_of_lr then_t else_t in
        let common_t = common_type_of_lr injected_t common_then_else_t in

        (* The common type of the then/else/expected types, if it exists, may be
        a superset of the injected type, but the injected type is expected to
        dominate. *)
        let common_t = if type_convertible_to common_t injected_t then
          common_t
        else
          failwith (
            Printf.sprintf
              (
                "then/else branches do not agree on type that is compatible " ^^
                "with injected type: then [[ %s ]], else [[ %s ]], " ^^
                "common then/else [[ %s ]], common all [[ %s ]], " ^^
                "injected [[ %s ]]"
              )
              (fmt_type then_t)
              (fmt_type else_t)
              (fmt_type common_then_else_t)
              (fmt_type common_t)
              (fmt_type injected_t)
          )
        in

        let then_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") common_t then_exp
        in
        let else_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") common_t else_exp
        in

        IfThenElseExpr(common_t, cond_exp, then_exp_injected, else_exp_injected)

    | (_, WhileExpr(_, cond_expr, stmts, exp_res)) ->
        let exp_res_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") injected_t exp_res
        in

        WhileExpr(injected_t, cond_expr, stmts, exp_res_injected)

    | (Variant(_, ctors), VariantCtorExpr(_, ctor_name, ctor_exp)) ->
        let (_, ctor_exp_t) = List.find (
            fun (name, _) -> name = ctor_name
          ) ctors
        in
        let ctor_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") ctor_exp_t ctor_exp
        in

        VariantCtorExpr(injected_t, ctor_name, ctor_exp_injected)

    | (Variant(_, _), _)
    | (_, VariantCtorExpr(_, _, _)) ->
        failwith (
          "Unexpectedly encountered mismatch in variant typing: " ^
          "[[ " ^ (fmt_type injected_t) ^ " ]]"
        )

    | (U8,  ValU8 (_)) -> exp
    | (U16, ValU16(_)) -> exp
    | (U32, ValU32(_)) -> exp
    | (U64, ValU64(_)) -> exp
    | (U16, ValU8 (_))                          -> ValCastExtend(U16, exp)
    | (U32, (ValU8(_) | ValU16(_)))             -> ValCastExtend(U32, exp)
    | (U64, (ValU8(_) | ValU16(_) | ValU32(_))) -> ValCastExtend(U64, exp)

    | (I8,  ValI8 (_)) -> exp
    | (I16, ValI16(_)) -> exp
    | (I32, ValI32(_)) -> exp
    | (I64, ValI64(_)) -> exp
    | (I16, ValI8 (_))                          -> ValCastExtend(I16, exp)
    | (I32, (ValI8(_) | ValI16(_)))             -> ValCastExtend(I32, exp)
    | (I64, (ValI8(_) | ValI16(_) | ValI32(_))) -> ValCastExtend(I64, exp)

    | (F32,  ValF32 (_)) -> exp
    | (F64,  ValF64 (_)) -> exp
    | (F128, ValF128(_)) -> exp

    | (F64,   ValF32(_))              -> ValCastExtend( F64, exp)
    | (F128, (ValF32(_) | ValF64(_))) -> ValCastExtend(F128, exp)

    | (Nil,    ValNil)
    | (Bool,   ValBool(_))
    | (String, ValStr(_)) -> exp

    | ((U64 | U32 | U16 | U8 | I64 | I32 | I16 | I8 | F128 | F64 | F32), _)
    | ((Nil | Bool | String), _)
    | (VarArgSentinel, _) ->
        let _ =
          Printf.printf "%sGiven expr: [[ %s ]]\n"
            ind
            (fmt_expr ~print_typ:true "" exp)
        in
        failwith (
          Printf.sprintf "Cannot inject type [[ %s ]] into expr [[ %s ]]"
            (fmt_type injected_t)
            (fmt_expr ~print_typ:true "" exp)
        )

    | (Ptr(_), _) -> failwith "Unimplemented"
;;

type v_ctor = (string * berk_t)

and variant_decl_t = {
  v_name: string;
  v_ctors: v_ctor list;
  v_typ_vars: string list;
}

type f_param = (ident_t * var_qual * berk_t)

and func_decl_t = {
  f_name: string;
  f_params: f_param list;
  f_ret_t: berk_t;
}

and func_def_t = {
  f_decl: func_decl_t;
  f_stmts: stmt list;
}

type module_decl =
  | FuncExternDecl of func_decl_t
  | FuncDef of func_def_t
  | VariantDecl of variant_decl_t

let rec fmt_func_decl ?(print_typ = false) ?(extern = false) f_decl : string =
  let maybe_extern =
    if extern
      then "extern "
      else ""
  in
  Printf.sprintf "%s%s;\n"
    maybe_extern
    (fmt_func_signature ~print_typ:print_typ f_decl)

and fmt_func_signature
  ?(print_typ = false) {f_name; f_params; f_ret_t;} : string
=
  let ret_t_s = begin match f_ret_t with
    | Nil
    | Undecided ->
        if print_typ
        then Printf.sprintf ": %s" (fmt_type f_ret_t)
        else ""
    | _ -> Printf.sprintf ": %s" (fmt_type f_ret_t)
  end in

  Printf.sprintf "fn %s(%s)%s"
    f_name
    (fmt_join_func_params "," f_params)
    ret_t_s

and fmt_func_param (p_name, p_qual, p_type) : string =
  Printf.sprintf "%s%s: %s"
    (fmt_var_qual p_qual)
    p_name
    (fmt_type p_type)

and fmt_join_func_params delim params : string =
  match params with
  | [] -> ""
  | [x] -> fmt_func_param x
  | x::xs ->
      Printf.sprintf "%s%s %s"
        (fmt_func_param x)
        delim
        (fmt_join_func_params delim xs)

let fmt_func_ast ?(print_typ = false) {f_decl; f_stmts;} : string =
  let formatted_stmts =
    List.fold_left (^) "" (
      List.map (fmt_stmt ~print_typ:print_typ "  ") f_stmts
    )
  in

  Printf.sprintf "%s {\n%s}\n"
    (fmt_func_signature ~print_typ:print_typ f_decl)
    formatted_stmts
;;

let fmt_variant_ctor ?(pretty_unbound=false) (ctor_name, ctor_typ) : string =
  let fmt_typ = begin
    match ctor_typ with
    | Nil -> ""
    | _ ->
        Printf.sprintf " of %s"
          (fmt_type ~pretty_unbound:pretty_unbound ctor_typ)
  end in

  Printf.sprintf " | %s%s\n" ctor_name fmt_typ
;;

let fmt_variant_decl
  ?(pretty_unbound=false) {v_name; v_ctors; v_typ_vars} : string
=
  let formatted_type_vars = begin
    match v_typ_vars with
    | [] -> ""
    | xs ->
        Printf.sprintf "<%s>"
          (fmt_join_strs ", " xs)
  end in

  let formatted_ctors =
    List.fold_left (^) "" (
      List.map (fmt_variant_ctor ~pretty_unbound:pretty_unbound) v_ctors
    )
  in

  Printf.sprintf "%s %s {\n%s}\n"
    v_name
    formatted_type_vars
    formatted_ctors
;;

(* Return the pair of all the non-variadic function parameter types, and whether
the parameter list ends with a variadic-args sentinel. Fails if ill-formed. *)
let rec get_static_f_params f_params =
  begin match f_params with
  | [] -> ([], false)
  | [(_, _, VarArgSentinel)] -> ([], true)
  | (_, _, VarArgSentinel)::_ ->
      failwith "Variadic arguments may exist only once, at end of param list"
  | (_, _, x)::xs ->
      let (rest, is_vararg) = get_static_f_params xs in
      (x::rest, is_vararg)
  end
