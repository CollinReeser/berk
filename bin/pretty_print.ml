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

let rec print_expr ?(init_ind = false) ?(print_typ = false) ind ex =
  let init_ind = if init_ind then ind else "" in
  let (typ_s, typ_s_rev) =
    if print_typ
    then
      let typ_formatted = expr_type ex |> fmt_type in
      (Printf.sprintf ":%s" typ_formatted, Printf.sprintf "%s:" typ_formatted)
    else ("", "")
  in
  match ex with
  | ValU64 (value) -> Printf.printf "%s%d%s" init_ind value typ_s
  | ValU32 (value) -> Printf.printf "%s%d%s" init_ind value typ_s
  | ValU16 (value) -> Printf.printf "%s%d%s" init_ind value typ_s
  | ValU8  (value) -> Printf.printf "%s%d%s" init_ind value typ_s

  | ValI64 (value) -> Printf.printf "%s%d%s" init_ind value typ_s
  | ValI32 (value) -> Printf.printf "%s%d%s" init_ind value typ_s
  | ValI16 (value) -> Printf.printf "%s%d%s" init_ind value typ_s
  | ValI8  (value) -> Printf.printf "%s%d%s" init_ind value typ_s

  | ValF128 (str)   -> Printf.printf "%s%s%s" init_ind str   typ_s
  | ValF64  (value) -> Printf.printf "%s%f%s" init_ind value typ_s
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

and print_stmt ?(print_typ = false) ind stmt =
  match stmt with
  | DeclStmt (ident, qual, btype, ex) -> (
    let typ_s = match btype with
      | Undecided -> ""
      | x -> fmt_type x |> Printf.sprintf ": %s"
    in
    Printf.printf "%slet %s%s" ind (fmt_var_qual qual) ident;
    Printf.printf "%s" typ_s;
    Printf.printf " = ";
    print_expr ~print_typ:print_typ ind ex;
    Printf.printf ";\n"
  )
  | AssignStmt (ident, ex) ->
      Printf.printf "%s%s" ind ident;
      Printf.printf " = ";
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n"
  | ExprStmt (ex) ->
      Printf.printf "%s" ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
  | ResolveStmt (ex) ->
      Printf.printf "%sresolve " ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
  | ReturnStmt (ex) ->
      Printf.printf "%sreturn " ind;
      print_expr ~print_typ:print_typ ind ex;
      Printf.printf ";\n";
;;

let print_func_ast ?(print_typ = false) {f_name; f_params; f_stmts; f_ret_t;} =
  let ret_t_s = begin match f_ret_t with
    | Nil
    | Undecided ->
        if print_typ
        then Printf.sprintf ": %s" (fmt_type f_ret_t)
        else ""
    | _ -> Printf.sprintf ": %s" (fmt_type f_ret_t)
  end in
  Printf.printf "fn %s(" f_name;
  List.iter print_func_param f_params;
  Printf.printf ")%s {\n" ret_t_s;
  List.iter (print_stmt ~print_typ:print_typ "  ") f_stmts;
  Printf.printf "}\n"
;;
