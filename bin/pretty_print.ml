open Ast
open Typing

let print_berk_type berk_type =
  match berk_type with
  | I64 -> Printf.printf "i64"
  | I32 -> Printf.printf "i32"
  | Bool -> Printf.printf "bool"
;;

let print_func_param {p_name; p_type} =
  Printf.printf "%s: " p_name;
  print_berk_type p_type
;;

(* let rec print_interleaved_list delimiter func target_list =
  match target_list with
  | [] -> ()
  | [x] -> func x
  | x :: xs -> (
    func x;
    Printf.printf "%s" delimiter;
    print_interleaved_list delimiter func xs
  ) *)

let rec print_expr ind ex =
  match ex with
  | Add (lhs, rhs) -> print_expr "" lhs; Printf.printf " + "; print_expr "" rhs
  | Sub (lhs, rhs) -> print_expr "" lhs; Printf.printf " - "; print_expr "" rhs
  | Mul (lhs, rhs) -> print_expr "" lhs; Printf.printf " * "; print_expr "" rhs
  | ValI64 (value) -> Printf.printf "%d" value
  | ValI32 (value) -> Printf.printf "%d" value
  | ValBool (value) -> Printf.printf "%B" value
  | IfExpr ({
      if_block = {
        cond = if_cond; stmts = if_stmts
      };
      else_if_blocks;
      else_block
    }) ->
      Printf.printf "if (";
      print_expr "" if_cond;
      Printf.printf ") {\n";
      List.iter (print_stmt (ind ^ "  ")) if_stmts;
      Printf.printf "%s}" ind;
      List.iter (
        fun ({cond = else_if_cond; stmts = else_if_stmts}) ->
          Printf.printf "\n%selse if (" ind;
          print_expr "" else_if_cond;
          Printf.printf ") {\n";
          List.iter (print_stmt (ind ^ "  ")) else_if_stmts;
          Printf.printf "%s}" ind;
      ) else_if_blocks;
      match else_block with
      | None -> ()
      | Some (else_stmts) ->
        Printf.printf "\n%selse {\n" ind;
        List.iter (print_stmt (ind ^ "  ")) else_stmts;
        Printf.printf "%s}" ind;

and print_stmt ind stmt =
  match stmt with
  | DeclDef (ident, btype, ex) -> (
    Printf.printf "%slet %s: " ind ident;
    print_berk_type btype;
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
  | IfStmt ({
      if_block = {
        cond = if_cond; stmts = if_stmts
      };
      else_if_blocks;
      else_block
    }) ->
      Printf.printf "%sif (" ind;
      print_expr "" if_cond;
      Printf.printf ") {\n";
      List.iter (print_stmt (ind ^ "  ")) if_stmts;
      Printf.printf "%s}\n" ind;
      List.iter (
        fun ({cond = else_if_cond; stmts = else_if_stmts}) ->
          Printf.printf "%selse if (" ind;
          print_expr "" else_if_cond;
          Printf.printf ") {\n";
          List.iter (print_stmt (ind ^ "  ")) else_if_stmts;
          Printf.printf "%s}\n" ind;
      ) else_if_blocks;
      match else_block with
      | None -> ()
      | Some (else_stmts) ->
        Printf.printf "%selse {\n" ind;
        List.iter (print_stmt (ind ^ "  ")) else_stmts;
        Printf.printf "%s}" ind;
;;

let print_func_ast {f_name; f_params; f_stmts} =
  Printf.printf "fn %s(" f_name;
  List.iter print_func_param f_params;
  Printf.printf ") {\n";
  List.iter (print_stmt "  ") f_stmts;
  Printf.printf "\n}\n"
;;
