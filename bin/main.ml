open Core;;

(*
AST for the berk language.
*)

type berk_type =
  | Int

type ident_t = string

type expr =
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | ValInt of int
;;

type statement =
  | DeclDef of ident_t * berk_type * expr
;;

type func_param = {
  p_name: string;
  p_type: berk_type;
}

type func_ast = {
  f_name: string;
  f_params: func_param list;
  f_stmts: statement list;
}

let build_example_ast =
  {
    f_name = "example_func";
    f_params = [{
      p_name = "arg_1";
      p_type = Int;
    }];
    f_stmts = [
      DeclDef (
        "sdf", Int,
        Add(ValInt(5), Mul(Sub(ValInt(6), ValInt(7)), ValInt (8)))
      )
    ];
  }
;;

let print_berk_type berk_type =
  match berk_type with
  | Int -> Printf.printf "int"
;;

let print_func_param {p_name; p_type} =
  Printf.printf "%s: " p_name;
  print_berk_type p_type
;;

let rec print_expr ex =
  match ex with
  | Add (lhs, rhs) -> print_expr lhs; Printf.printf " + "; print_expr rhs
  | Sub (lhs, rhs) -> print_expr lhs; Printf.printf " - "; print_expr rhs
  | Mul (lhs, rhs) -> print_expr lhs; Printf.printf " * "; print_expr rhs
  | ValInt (value) -> Printf.printf "%d" value
;;

let print_stmt indent stmt =
  match stmt with
  | DeclDef (ident, btype, ex) -> (
    Printf.printf "%slet %s: " indent ident;
    print_berk_type btype;
    Printf.printf " = ";
    print_expr ex;
    Printf.printf ";\n"
  )
;;

let print_func_ast {f_name; f_params; f_stmts} =
  Printf.printf "fn %s(" f_name;
  List.iter ~f:print_func_param f_params;
  Printf.printf ") {\n";
  List.iter ~f:(print_stmt "  ") f_stmts;
  Printf.printf "}\n"
;;

let main =
  print_func_ast build_example_ast
;;

main;;
