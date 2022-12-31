open Typing


(*
AST for the berk language.
*)

type ident_t = string

and bin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | NotEq
  | Less
  | LessEq
  | Greater
  | GreaterEq

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
  | ValCastTrunc of berk_t * expr
  | ValCastBitwise of berk_t * expr
  | BinOp of berk_t * bin_op * expr * expr
  (* Sequence of statements followed by an expression, where if the expression
  is None, then the BlockExpr resolves to a nil value. *)
  | BlockExpr of berk_t * stmt list * expr
  (* if expr, then expr, else expr *)
  | IfThenElseExpr of berk_t * expr * expr * expr
  (* while expr, then stmts, else expr *)
  | WhileExpr of berk_t * expr * stmt list * expr
  | FuncCall of berk_t * ident_t * expr list
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
  | ValCastTrunc(typ, _) -> typ
  | ValCastBitwise(typ, _) -> typ
  | BinOp(typ, _, _, _) -> typ
  | BlockExpr(typ, _, _) -> typ
  | IfThenElseExpr(typ, _, _, _) -> typ
  | WhileExpr(typ, _, _, _) -> typ
  | FuncCall(typ, _, _) -> typ
  | ArrayExpr(typ, _) -> typ
  | IndexExpr(typ, _, _) -> typ
  | StaticIndexExpr(typ, _, _) -> typ
  | TupleExpr(typ, _) -> typ
  | VariantCtorExpr(typ, _, _) -> typ
;;

let print_bin_op op =
  match op with
  | Add -> Printf.printf " + "
  | Sub -> Printf.printf " - "
  | Mul -> Printf.printf " * "
  | Div -> Printf.printf " / "
  | Mod -> Printf.printf " %% "
  | Eq -> Printf.printf " == "
  | NotEq -> Printf.printf " != "
  | Less -> Printf.printf " < "
  | LessEq -> Printf.printf " <= "
  | Greater -> Printf.printf " > "
  | GreaterEq -> Printf.printf " >= "

let rec print_join_exprs ?(print_typ = false) ind delim exprs =
  match exprs with
  | [] -> ()
  | [x] -> print_expr ~print_typ:print_typ ind x
  | x::xs ->
      print_expr ~print_typ:print_typ ind x ;
      Printf.printf delim;
      print_join_exprs ~print_typ:print_typ ind delim xs

and print_expr ?(init_ind = false) ?(print_typ = false) ind ex =
  let init_ind = if init_ind then ind else "" in
  let (typ_s, typ_s_rev) =
    if print_typ
    then
      let typ_formatted = expr_type ex |> fmt_type in
      (Printf.sprintf ":%s" typ_formatted, Printf.sprintf "%s:" typ_formatted)
    else ("", "")
  in
  match ex with
  | ValNil -> Printf.printf "%s()%s" init_ind typ_s

  | ValU64 (value)
  | ValU32 (value)
  | ValU16 (value)
  | ValU8  (value) -> Printf.printf "%s%d%s" init_ind value typ_s

  | ValI64 (value)
  | ValI32 (value)
  | ValI16 (value)
  | ValI8  (value) -> Printf.printf "%s%d%s" init_ind value typ_s

  | ValF128 (str)   -> Printf.printf "%s%s%s" init_ind str   typ_s

  | ValF64  (value)
  | ValF32  (value) -> Printf.printf "%s%f%s" init_ind value typ_s

  | ValBool (value) -> Printf.printf "%s%B%s" init_ind value typ_s

  | ValStr (str) ->
    begin
      let escaped = String.escaped str in
      Printf.printf "%s\"%s\"%s" init_ind escaped typ_s
    end

  | ValVar (_, id) -> Printf.printf "%s%s%s" init_ind id typ_s

  | ValCastTrunc (target_t, exp) ->
    begin
      let target_t_s = fmt_type target_t in
      Printf.printf "cast_trunc<%s>(" target_t_s;
      print_expr ~print_typ:print_typ "" exp;
      Printf.printf ")%s" typ_s
    end

  | ValCastBitwise (target_t, exp) ->
    begin
      let target_t_s = fmt_type target_t in
      Printf.printf "cast_bitwise<%s>(" target_t_s;
      print_expr ~print_typ:print_typ "" exp;
      Printf.printf ")%s" typ_s
    end

  | BinOp (_, op, lh, rh) ->
      Printf.printf "%s(" init_ind;
      print_expr ~print_typ:print_typ "" lh;
      print_bin_op op;
      print_expr ~print_typ:print_typ "" rh;
      Printf.printf ")%s" typ_s
  | BlockExpr (_, stmts, exp) ->
      Printf.printf "%s%s{\n" init_ind typ_s_rev;
      List.iter (print_stmt ~print_typ:print_typ (ind ^ "  ")) stmts;
      print_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") exp ;
      Printf.printf "\n" ;
      Printf.printf "%s}" ind
  | IfThenElseExpr (_, if_cond, then_expr, else_expr) ->
      Printf.printf "%s%sif (" init_ind typ_s_rev;
      print_expr ~print_typ:print_typ "" if_cond;
      Printf.printf ") {\n";
      print_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") then_expr;
      Printf.printf "\n%s} else {\n" ind;
      print_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") else_expr;
      Printf.printf "\n%s}" ind
  | WhileExpr (_, while_cond, then_stmts, finally_expr) ->
      Printf.printf "%s%swhile (" init_ind typ_s_rev;
      print_expr ~print_typ:print_typ "" while_cond;
      Printf.printf ") {\n";
      List.iter (print_stmt ~print_typ:print_typ (ind ^ "  ")) then_stmts;
      Printf.printf "\n%s} finally {\n" ind;
      print_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") finally_expr;
      Printf.printf "\n%s}" ind
  | FuncCall(_, id, exprs) ->
    begin
      Printf.printf "%s%s%s(" init_ind typ_s_rev id;
      print_join_exprs ~print_typ:print_typ ind ", " exprs;
      Printf.printf ")"
    end
  | ArrayExpr(_, exprs) ->
      Printf.printf "%s[" init_ind;
      print_join_exprs ~print_typ:print_typ ind ", " exprs;
      Printf.printf "]%s" typ_s

  | StaticIndexExpr(_, idx, arr) ->
      Printf.printf "%s" init_ind;
      print_expr ~print_typ:print_typ "" arr;
      Printf.printf "[";
      Printf.printf "%d" idx;
      Printf.printf "]->%s" typ_s

  | IndexExpr(_, idx, arr) ->
      Printf.printf "%s" init_ind;
      print_expr ~print_typ:print_typ "" arr;
      Printf.printf "[";
      print_expr ~print_typ:print_typ "" idx;
      Printf.printf "]->%s" typ_s

  | TupleExpr(_, exprs) ->
      Printf.printf "%s(" init_ind;
      print_join_exprs ~print_typ:print_typ ind ", " exprs;
      Printf.printf ")%s" typ_s

  | VariantCtorExpr(_, ctor_name, expr) ->
      Printf.printf "%s%s(" init_ind ctor_name ;
      print_expr ~print_typ:print_typ "" expr ;
      Printf.printf ")%s" typ_s

and print_join_idents_quals delim idents_quals =
  match idents_quals with
  | [] -> ()
  | [(ident, qual)] -> Printf.printf "%s%s" (fmt_var_qual qual) ident
  | (ident, qual)::xs ->
      Printf.printf "%s%s%s" (fmt_var_qual qual) ident delim;
      print_join_idents_quals delim xs

and print_join_strs delim idents =
  match idents with
  | [] -> ()
  | [ident] -> Printf.printf "%s" ident
  | ident::xs ->
      Printf.printf "%s%s" ident delim;
      print_join_strs delim xs

and print_stmt ?(print_typ = false) ind stmt =
  match stmt with
  | DeclStmt (ident, qual, btype, ex) -> begin
      let typ_s = match btype with
        | Undecided -> ""
        | x -> fmt_type x |> Printf.sprintf ": %s"
      in
      Printf.printf "%slet %s%s%s = " ind (fmt_var_qual qual) ident typ_s;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
    end
  | DeclDeconStmt (idents_quals, btype, ex) -> begin
      let typ_s = match btype with
        | Undecided -> ""
        | x -> fmt_type x |> Printf.sprintf ": %s"
      in
      Printf.printf "%slet (" ind;
      print_join_idents_quals ", " idents_quals;
      Printf.printf ")%s = " typ_s;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n"
    end
  | AssignStmt (ident, ex) ->
      Printf.printf "%s%s" ind ident;
      Printf.printf " = ";
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n"
  | AssignDeconStmt (idents, ex) ->
      Printf.printf "%s(" ind;
      print_join_strs ", " idents;
      Printf.printf ")";
      Printf.printf " = ";
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n"
  | ExprStmt (ex) ->
      Printf.printf "%s" ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
  | ReturnStmt (ex) ->
      Printf.printf "%sreturn " ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
;;

(* let coerce_expr_to_type typ exp =
  begin match (typ, exp) with
    | (Undecided, _) ->
        failwith "Refusing to coerce expression to undecided type."

    | (U64, (ValU8(x) | ValU16(x) | ValU32(x) | ValU64(x))) -> ValU64(x)
    | (U32, (ValU8(x) | ValU16(x) | ValU32(x)))             -> ValU32(x)
    | (U16, (ValU8(x) | ValU16(x)))                         -> ValU16(x)
    | (U8,   ValU8(x))                                      -> ValU8 (x)
    | (I64, (ValI8(x) | ValI16(x) | ValI32(x) | ValI64(x))) -> ValI64(x)
    | (I32, (ValI8(x) | ValI16(x) | ValI32(x)))             -> ValI32(x)
    | (I16, (ValI8(x) | ValI16(x)))                         -> ValI16(x)
    | (I8,   ValI8(x))                                      -> ValI8 (x)


  end
;; *)

(* Force-apply a top-level type to the given expression, recursively. *)
let rec inject_type_into_expr ?(ind="") typ exp =
  Printf.printf "%sInjecting: [[ %s ]] into expr [[ " ind (fmt_type typ) ;
  print_expr ~print_typ:true ind exp ;
  Printf.printf "%s ]]\n" ind ;

  let exp_t = expr_type exp in
  let tvars_to_t = map_tvars_to_types typ exp_t in

  (* Shadow the old `typ`; we now have a possibly-more-concrete type. *)
  let typ = concretify_unbound_types tvars_to_t typ in

  if not (type_convertible_to exp_t typ) then
    failwith (
      "Injection type [[" ^ (fmt_type typ) ^ "]] disagrees with existing " ^
      "type [[" ^ (fmt_type exp_t) ^ "]]"
    )
  else
    let exp_up = begin match (typ, exp) with
    | (Undecided, _) ->
        failwith "Refuse to inject undecided type into expr"

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

    | (_, ValCastTrunc  (t, exp_trunc))   -> ValCastTrunc  (t, exp_trunc)
    | (_, ValCastBitwise(t, exp_bitwise)) -> ValCastBitwise(t, exp_bitwise)
        (* TODO, applying to both of the above: In general,
        `type_convertible_to` will fail for the interesting cases for
        ValCastTrunc, and doesn't cover what ValCastBitwise wants to do. So,
        we'll need some special logic to cover these, and any other
        "explicit conversion" expressions. *)

    | (_, ValVar(t, var_name)) -> ValVar(t, var_name)
        (* TODO: We probably need some sort of "extension" expression, if
        necessary to "promote" whatever type is in this variable. *)

    | (_, FuncCall(t, f_name, exp_lst)) -> FuncCall(t, f_name, exp_lst)
      (* The return type of a function does not influence its parameters. *)
      (* TODO: That said, we should probably be injecting a conversion
      expression rather than blanket overriding the claimed return type of the
      function. *)

    | (_, BlockExpr(_, stmts, exp_res)) ->
        (* We're not smart enough yet to influence the types of any expressions
        within the statements within the block. So, just make sure the trailing
        expression is type-injected. *)
        let exp_res_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") typ exp_res
        in

        BlockExpr(typ, stmts, exp_res_injected)

    | (_, IndexExpr(_, idx_exp, arr_exp)) ->
        (* We can't use our injection type info to assist with typechecking the
        index expression, but we _can_ use it to assist in typechecking the
        indexed array itself, by assuming the array expression type is expected
        to be an "array of" the target type. *)
        let arr_t = expr_type arr_exp in
        let arr_injection_type = begin match arr_t with
          | Array(_, sz) -> Array(typ, sz)
          | _ -> failwith ("Unexpected non-array type: " ^ (fmt_type arr_t))
        end in
        let arr_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") arr_injection_type arr_exp
        in
        IndexExpr(typ, idx_exp, arr_exp_injected)

    | (_, StaticIndexExpr(_, idx, arr_exp)) ->
        (* We can't use our injection type info to assist with typechecking the
        index expression, but we _can_ use it to assist in typechecking the
        indexed array itself, by assuming the array expression type is expected
        to be an "array of" the target type. *)
        let arr_t = expr_type arr_exp in
        let arr_injection_type = begin match arr_t with
          | Array(_, sz) -> Array(typ, sz)
          | _ -> failwith ("Unexpected non-array type: " ^ (fmt_type arr_t))
        end in
        let arr_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") arr_injection_type arr_exp
        in
        StaticIndexExpr(typ, idx, arr_exp_injected)

    | (Array(elem_t, sz), ArrayExpr(_, elem_lst)) ->
        let elem_t_lst = List.init sz (fun _ -> elem_t) in
        let elem_exp_injected_lst =
          List.map2
            (inject_type_into_expr ~ind:(ind ^ "  ")) elem_t_lst elem_lst
        in
        ArrayExpr(typ, elem_exp_injected_lst)

    | (Tuple(exp_t_lst), TupleExpr(_, exp_lst)) ->
        let exp_injected_lst =
          List.map2 (inject_type_into_expr ~ind:(ind ^ "  ")) exp_t_lst exp_lst
        in
        TupleExpr(typ, exp_injected_lst)

    | (Tuple(_), _)
    | (_, TupleExpr(_, _))
    | (Array(_, _), _)
    | (_, ArrayExpr(_, _)) ->
        failwith (
          "Cannot inject incompatible aggregate types: " ^ (fmt_type typ)
        )

    (* BinOps are an interesting case because they can "switch types"
    arbitrarily deep into a nested bin-op tree, we don't want to eg
    propagate the expectation of a bool due to an eg LessEq op into the
    arithmetic branches, and in general we expect the bottom-up typecheck to
    have correctly inferred everything (or failed eagerly due to type
    mismatch.) *)
    | (_, BinOp(t, bin_op, lhs, rhs)) -> BinOp(t, bin_op, lhs, rhs)

    | (_, IfThenElseExpr(_, cond_exp, then_exp, else_exp)) ->
        let then_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") typ then_exp
        in
        let else_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") typ else_exp
        in

        IfThenElseExpr (typ, cond_exp, then_exp_injected, else_exp_injected)

    | (_, WhileExpr(_, cond_expr, stmts, exp_res)) ->
        let exp_res_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") typ exp_res
        in

        WhileExpr(typ, cond_expr, stmts, exp_res_injected)

    | (Variant(_, ctors), VariantCtorExpr(_, ctor_name, ctor_exp)) ->
        let (_, ctor_exp_t) = List.find (
            fun (name, _) -> name = ctor_name
          ) ctors
        in
        let ctor_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") ctor_exp_t ctor_exp
        in

        VariantCtorExpr(typ, ctor_name, ctor_exp_injected)

    | (Variant(_, _), _)
    | (_, VariantCtorExpr(_, _, _)) ->
        failwith (
          "Unexpectedly encountered mismatch in variant typing: " ^
          "[[ " ^ (fmt_type typ) ^ " ]]"
        )

    | (U8,   ValU8(x))                                      -> ValU8 (x)
    | (U16, (ValU8(x) | ValU16(x)))                         -> ValU16(x)
    | (U32, (ValU8(x) | ValU16(x) | ValU32(x)))             -> ValU32(x)
    | (U64, (ValU8(x) | ValU16(x) | ValU32(x) | ValU64(x))) -> ValU64(x)

    | (I8,   ValI8(x))                                      -> ValI8 (x)
    | (I16, (ValI8(x) | ValI16(x)))                         -> ValI16(x)
    | (I32, (ValI8(x) | ValI16(x) | ValI32(x)))             -> ValI32(x)
    | (I64, (ValI8(x) | ValI16(x) | ValI32(x) | ValI64(x))) -> ValI64(x)

    | (F32,  ValF32(x))                                     -> ValF32(x)
    | (F64, (ValF32(x) | ValF64(x)))                        -> ValF64(x)

    | (F128, (ValF32(x) | ValF64(x))) -> ValF128(Printf.sprintf "%f" x)
    | (F128, ValF128(str))            -> ValF128(str)

    | (Nil,    ValNil)
    | (Bool,   ValBool(_))
    | (String, ValStr(_)) -> exp

    | ((U64 | U32 | U16 | U8 | I64 | I32 | I16 | I8 | F128 | F64 | F32), _)
    | ((Nil | Bool | String), _)
    | (VarArgSentinel, _) ->
        Printf.printf "%sGiven expr: [[ " ind ;
        print_expr ~print_typ:true "" exp ;
        Printf.printf "%s ]]\n" ind ;
        failwith ("Cannot inject type [[ " ^ (fmt_type typ) ^ " ]] into expr")

    end in
    Printf.printf "%s  Injected [[ %s ]] to yield expr [[ " ind (fmt_type typ) ;
    print_expr ~print_typ:true (ind ^ "  ") exp_up ;
    Printf.printf "%s ]]\n" ind ;
    exp_up
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

let rec print_func_decl ?(print_typ = false) ?(extern = false) f_decl =
  begin if extern
    then Printf.printf "extern "
    else ()
  end ;
  begin
    print_func_signature ~print_typ:print_typ f_decl ;
    Printf.printf ";\n"
  end

and print_func_signature ?(print_typ = false) {f_name; f_params; f_ret_t;} =
  let ret_t_s = begin match f_ret_t with
    | Nil
    | Undecided ->
        if print_typ
        then Printf.sprintf ": %s" (fmt_type f_ret_t)
        else ""
    | _ -> Printf.sprintf ": %s" (fmt_type f_ret_t)
  end in

  Printf.printf "fn %s(" f_name;
  print_join_func_params "," f_params;
  Printf.printf ")%s" ret_t_s

and print_func_param (p_name, p_qual, p_type) =
  Printf.printf "%s%s: " (fmt_var_qual p_qual) p_name;
  Printf.printf "%s" (fmt_type p_type)

and print_join_func_params delim params =
  begin match params with
    | [] -> ()
    | [x] -> print_func_param x
    | x::xs ->
        print_func_param x;
        Printf.printf "%s " delim;
        print_join_func_params delim xs
  end

let print_func_ast ?(print_typ = false) {f_decl; f_stmts;} =
  print_func_signature ~print_typ:print_typ f_decl ;
  Printf.printf " {\n" ;
  List.iter (print_stmt ~print_typ:print_typ "  ") f_stmts ;
  Printf.printf "}\n"
;;

let print_variant_ctor ?(pretty_unbound=false) (ctor_name, ctor_typ) =
  let fmt_typ = begin
    match ctor_typ with
    | Nil -> ""
    | _ ->
        let typ_formatted = fmt_type ~pretty_unbound:pretty_unbound ctor_typ in
        Printf.sprintf " of %s" typ_formatted
  end in

  Printf.printf "  | %s%s\n" ctor_name fmt_typ
;;

let print_variant_decl ?(pretty_unbound=false) {v_name; v_ctors; v_typ_vars} =
  Printf.printf "%s " v_name ;
  let _ = begin
    match v_typ_vars with
      | [] -> ()
      | xs ->
          Printf.printf "<" ;
          print_join_strs ", " xs ;
          Printf.printf "> " ;
  end in

  Printf.printf "{\n" ;
  List.iter (print_variant_ctor ~pretty_unbound:pretty_unbound) v_ctors ;
  Printf.printf "}\n" ;
;;

(* Return the pair of all the non-variadic function parameter types, and whether
the parameter list ends with a variadic-args sentinel. Fails if ill-formed. *)
let rec get_static_f_params (f_params : f_param list) =
  begin match f_params with
  | [] -> ([], false)
  | [(_, _, VarArgSentinel)] -> ([], true)
  | (_, _, VarArgSentinel)::_ ->
      failwith "Variadic arguments may exist only once, at end of param list"
  | (_, _, x)::xs ->
      let (rest, is_vararg) = get_static_f_params xs in
      (x::rest, is_vararg)
  end
