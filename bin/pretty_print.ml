open Ast
open Typing


let print_func_param (p_name, p_qual, p_type) =
  Printf.printf "%s%s: " (fmt_var_qual p_qual) p_name;
  Printf.printf "%s" (fmt_type p_type)
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
      Printf.printf ")"
    end

  | ValCastBitwise (target_t, exp) ->
    begin
      let target_t_s = fmt_type target_t in
      Printf.printf "cast_bitwise<%s>(" target_t_s;
      print_expr ~print_typ:print_typ "" exp;
      Printf.printf ")"
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
      Printf.printf "]"

  | StaticIndexExpr(_, idx, arr) ->
      Printf.printf "%s" init_ind;
      print_expr ~print_typ:print_typ "" arr;
      Printf.printf "[";
      Printf.printf "%d" idx;
      Printf.printf "]";

  | IndexExpr(_, idx, arr) ->
      Printf.printf "%s" init_ind;
      print_expr ~print_typ:print_typ "" arr;
      Printf.printf "[";
      print_expr ~print_typ:print_typ "" idx;
      Printf.printf "]";

  | TupleExpr(_, exprs) ->
      Printf.printf "%s(" init_ind;
      print_join_exprs ~print_typ:print_typ ind ", " exprs;
      Printf.printf ")"

  | VariantCtorExpr(_, ctor_name, expr) ->
      Printf.printf "%s%s(" init_ind ctor_name ;
      print_expr ~print_typ:print_typ "" expr ;
      Printf.printf ")"

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

let rec print_join_func_params delim params =
  begin match params with
    | [] -> ()
    | [x] -> print_func_param x
    | x::xs ->
        print_func_param x;
        Printf.printf "%s " delim;
        print_join_func_params delim xs
  end
;;

let print_func_signature ?(print_typ = false) {f_name; f_params; f_ret_t;} =
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
;;

let print_func_decl ?(print_typ = false) ?(extern = false) f_decl =
  begin if extern
    then Printf.printf "extern "
    else ()
  end ;
  print_func_signature ~print_typ:print_typ f_decl ;
  Printf.printf ";\n"
;;

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
