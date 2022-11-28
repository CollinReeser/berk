open Ast
open Typing


let fmt_type berk_type =
  match berk_type with
  | I64 -> "i64"
  | I32 -> "i32"
  | F32 -> "f32"
  | Bool -> "bool"
  | Nil -> "()"
  | Undecided -> "<?undecided?>"
;;


let print_func_param {p_name; p_type} =
  Printf.printf "%s: " p_name;
  Printf.printf "%s" (fmt_type p_type)
;;


let print_bin_op op =
  match op with
  | Add -> Printf.printf " + "
  | Sub -> Printf.printf " - "
  | Mul -> Printf.printf " * "

let rec print_expr ind ex =
  match ex with
  | ValI64 (value) -> Printf.printf "%d:%s" value (expr_type ex |> fmt_type)
  | ValI32 (value) -> Printf.printf "%d:%s" value (expr_type ex |> fmt_type)
  | ValF32 (value) -> Printf.printf "%f:%s" value (expr_type ex |> fmt_type)
  | ValBool (value) -> Printf.printf "%B:%s" value (expr_type ex |> fmt_type)
  | BinOp (typ, op, lh, rh) ->
      Printf.printf "(";
      print_expr "" lh; print_bin_op op; print_expr "" rh;
      Printf.printf "):%s" (fmt_type typ)
  | BlockExpr (_, stmts) ->
      Printf.printf "%s{\n" ind;
      List.iter (print_stmt (ind ^ "  ")) stmts;
      Printf.printf "%s}\n" ind
  | IfThenElseExpr (_, if_cond, then_expr, else_expr) ->
      Printf.printf "%sif (" ind;
      print_expr "" if_cond;
      Printf.printf ") {\n";
      print_expr (ind ^ "  ") then_expr;
      Printf.printf "%s} else {\n" ind;
      print_expr (ind ^ "  ") else_expr;
      Printf.printf "%s}\n" ind

and print_stmt ind stmt =
  match stmt with
  | DeclStmt (ident, btype, ex) -> (
    Printf.printf "%slet %s: " ind ident;
    Printf.printf "%s" (fmt_type btype);
    Printf.printf " = ";
    print_expr ind ex;
    Printf.printf ";\n"
  )
  | ExprStmt (ex) ->
      Printf.printf "%s" ind;
      print_expr ind ex;
      Printf.printf ";\n";
  | ResolveStmt (ex) ->
      Printf.printf "%sresolve " ind;
      print_expr ind ex;
      Printf.printf ";\n";
  | ReturnStmt (ex) ->
      Printf.printf "%sreturn " ind;
      print_expr ind ex;
      Printf.printf ";\n";
;;

let print_func_ast {f_name; f_params; f_stmts} =
  Printf.printf "fn %s(" f_name;
  List.iter print_func_param f_params;
  Printf.printf ") {\n";
  List.iter (print_stmt "  ") f_stmts;
  Printf.printf "\n}\n"
;;
