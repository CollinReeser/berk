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
  | BlockExpr (_, stmts) ->
      Printf.printf "%s%s{\n" init_ind typ_s_rev;
      List.iter (print_stmt ~print_typ:print_typ (ind ^ "  ")) stmts;
      Printf.printf "%s}" ind
  | IfThenElseExpr (_, if_cond, then_expr, else_expr) ->
      Printf.printf "%s%sif (" init_ind typ_s_rev;
      print_expr ~print_typ:print_typ "" if_cond;
      Printf.printf ") {\n";
      print_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") then_expr;
      Printf.printf "\n%s} else {\n" ind;
      print_expr ~init_ind:true ~print_typ:print_typ (ind ^ "  ") else_expr;
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

and print_join_idents_quals delim idents_quals =
  match idents_quals with
  | [] -> ()
  | [(ident, qual)] -> Printf.printf "%s%s" (fmt_var_qual qual) ident
  | (ident, qual)::xs ->
      Printf.printf "%s%s%s" (fmt_var_qual qual) ident delim;
      print_join_idents_quals delim xs

and print_join_idents delim idents =
  match idents with
  | [] -> ()
  | [ident] -> Printf.printf "%s" ident
  | ident::xs ->
      Printf.printf "%s%s" ident delim;
      print_join_idents delim xs

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
      print_join_idents ", " idents;
      Printf.printf ")";
      Printf.printf " = ";
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n"
  | ExprStmt (ex) ->
      Printf.printf "%s" ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
  | BlockStmt (stmts) ->
      Printf.printf "%s{\n" ind;
      List.iter (print_stmt ~print_typ:print_typ (ind ^ "  ")) stmts;
      Printf.printf "%s}\n" ind
  | IfThenElseStmt (if_cond, then_block, else_block) ->
      Printf.printf "%sif (" ind;
      print_expr ~print_typ:print_typ "" if_cond;
      Printf.printf ") {\n";
      print_stmt ~print_typ:print_typ (ind ^ "  ") then_block;
      Printf.printf "%s} else {\n" ind;
      print_stmt ~print_typ:print_typ (ind ^ "  ") else_block;
      Printf.printf "%s}\n" ind;
  | ResolveStmt (ex) ->
      Printf.printf "%sresolve " ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
  | ReturnStmt (ex) ->
      Printf.printf "%sreturn " ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
;;

let print_func_ast
  ?(print_typ = false) {f_decl = {f_name; f_params; f_ret_t;}; f_stmts;}
=
  let rec print_join_func_params delim params =
    begin match params with
      | [] -> ()
      | [x] -> print_func_param x
      | x::xs ->
          print_func_param x;
          Printf.printf "%s " delim;
          print_join_func_params delim xs
    end
  in

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
  Printf.printf ")%s {\n" ret_t_s;
  List.iter (print_stmt ~print_typ:print_typ "  ") f_stmts;
  Printf.printf "}\n"
;;
