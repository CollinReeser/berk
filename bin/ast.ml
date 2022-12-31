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

(* Force-apply a top-level type to the given expression, recursively. Fails
if any component subtype disagrees with what the expression had already
determined was its type. *)
let rec inject_type_into_expr typ exp =
  Printf.printf "Injecting: [[ %s ]] into expr [[ " (fmt_type typ) ;
  print_expr ~print_typ:true "" exp ;
  Printf.printf " ]]\n" ;

  let exp_t = expr_type exp in
  if not (type_convertible_to exp_t typ) then
    failwith (
      "Injection type [[" ^ (fmt_type typ) ^ "]] disagrees with existing " ^
      "type [[" ^ (fmt_type exp_t) ^ "]]"
    )
  else
    match (exp, typ) with
    | (
        (
          ValNil
          | ValU64 (_) | ValU32 (_) | ValU16 (_) | ValU8  (_)
          | ValI64 (_) | ValI32 (_) | ValI16 (_) | ValI8  (_)
          | ValF128(_) | ValF64 (_) | ValF32 (_)
          | ValBool(_)
          | ValStr (_)
        ),
        _
      ) -> exp

    | (ValVar(_, var_name),            _) -> ValVar        (typ, var_name)

    | (ValCastTrunc  (_, exp_trunc),   _) -> ValCastTrunc  (typ, exp_trunc)
    | (ValCastBitwise(_, exp_bitwise), _) -> ValCastBitwise(typ, exp_bitwise)

    (* The return type of a function does not influence its parameters. *)
    | (FuncCall(_, f_name, exp_lst), _) -> FuncCall(typ, f_name, exp_lst)

    | (BlockExpr(_, stmts, exp_res), _) ->
        (* We're not smart enough yet to influence the types of any expressions
        within the statements within the block. So, just make sure the trailing
        expression is type-injected. *)
        let exp_res_injected = inject_type_into_expr typ exp_res in
        BlockExpr(typ, stmts, exp_res_injected)

    | (IndexExpr(_, idx_exp, arr_exp), _) ->
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
          inject_type_into_expr arr_injection_type arr_exp
        in
        IndexExpr(typ, idx_exp, arr_exp_injected)

    | (StaticIndexExpr(_, idx, arr_exp), _) ->
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
          inject_type_into_expr arr_injection_type arr_exp
        in
        StaticIndexExpr(typ, idx, arr_exp_injected)

    | (ArrayExpr(_, elem_lst), Array(elem_t, sz)) ->
        let elem_t_lst = List.init sz (fun _ -> elem_t) in
        let elem_exp_injected_lst =
          List.map2 inject_type_into_expr elem_t_lst elem_lst
        in
        ArrayExpr(typ, elem_exp_injected_lst)

    | (ArrayExpr(_, _), _) ->
        failwith (
          "Cannot inject non-array type into array expr: " ^ (fmt_type typ)
        )

    | (TupleExpr(_, exp_lst), Tuple(exp_t_lst)) ->
        let exp_injected_lst =
          List.map2 inject_type_into_expr exp_t_lst exp_lst
        in
        TupleExpr(typ, exp_injected_lst)

    | (TupleExpr(_, _), _) ->
        failwith (
          "Cannot inject non-tuple type into tuple expr: " ^ (fmt_type typ)
        )

    | (BinOp(_, bin_op, lhs, rhs), _) ->
        let lhs_injected = inject_type_into_expr typ lhs in
        let rhs_injected = inject_type_into_expr typ rhs in
        BinOp(typ, bin_op, lhs_injected, rhs_injected)

    | (IfThenElseExpr(_, cond_exp, then_exp, else_exp), _) ->
        let then_exp_injected = inject_type_into_expr typ then_exp in
        let else_exp_injected = inject_type_into_expr typ else_exp in
        IfThenElseExpr (typ, cond_exp, then_exp_injected, else_exp_injected)

    | (WhileExpr(_, cond_expr, stmts, exp_res), _) ->
        let exp_res_injected = inject_type_into_expr typ exp_res in
        WhileExpr(typ, cond_expr, stmts, exp_res_injected)

    | (VariantCtorExpr(_, ctor_name, ctor_exp), Variant(_, ctors)) ->
        let (_, ctor_exp_t) = List.find (
            fun (name, _) -> name = ctor_name
          ) ctors
        in
        let ctor_exp_injected = inject_type_into_expr ctor_exp_t ctor_exp in
        VariantCtorExpr(typ, ctor_name, ctor_exp_injected)

    | (VariantCtorExpr(_, _, _), _) ->
        failwith (
          "Unexpectedly encountered non-variant type for variant " ^
          "constructor expr: [[ " ^ (fmt_type typ) ^ " ]]"
        )
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
