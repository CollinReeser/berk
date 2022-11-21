(*
AST for the berk language.
*)

type berk_type =
  | Int

type ident_t = string

type cond_block = {
  cond: expr;
  stmts: stmt list;
}
and expr =
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | ValInt of int
  | IfExpr of {
      if_block: cond_block;
      else_if_blocks: cond_block list;
      else_block: (stmt list) option;
    }
and stmt =
  | DeclDef of ident_t * berk_type * expr
  | ExprStmt of expr
  | IfStmt of {
      if_block: cond_block;
      else_if_blocks: cond_block list;
      else_block: (stmt list) option;
    }
;;

type func_param = {
  p_name: string;
  p_type: berk_type;
}

type func_ast = {
  f_name: string;
  f_params: func_param list;
  f_stmts: stmt list;
}

let build_example_ast =
  {
    f_name = "example_func";
    f_params = [
      {
        p_name = "arg_1";
        p_type = Int;
      };
      {
        p_name = "arg_2";
        p_type = Int;
      }
    ];
    f_stmts = [
      DeclDef(
        "abc", Int,
        Add(ValInt(5), Mul(Sub(ValInt(6), ValInt(7)), ValInt (8)))
      );
      ExprStmt(
        IfExpr({
          if_block = {cond = ValInt(30); stmts = [ExprStmt(ValInt(31))]};
          else_if_blocks = [
            {cond = ValInt(32); stmts = [ExprStmt(ValInt(33))]};
            {cond = ValInt(34); stmts = [ExprStmt(ValInt(35))]};
          ];
          else_block = Some([ExprStmt(ValInt(35))])
        })
      );
      DeclDef(
        "def", Int,
        IfExpr({
          if_block = {cond = ValInt(50); stmts = [ExprStmt(ValInt(51))]};
          else_if_blocks = [];
          else_block = Some([ExprStmt(ValInt(55))])
        })
      );
      DeclDef(
        "ghi", Int,
        IfExpr({
          if_block = {cond = ValInt(50); stmts = [ExprStmt(ValInt(51))]};
          else_if_blocks = [];
          else_block = None;
        })
      );
      IfStmt({
        if_block = {cond = ValInt(40); stmts = [ExprStmt(ValInt(41))]};
        else_if_blocks = [
          {cond = ValInt(42); stmts = [ExprStmt(ValInt(43))]};
        ];
        else_block = Some([ExprStmt(ValInt(45))])
      })
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
  | ValInt (value) -> Printf.printf "%d" value
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

let main =
  print_func_ast build_example_ast
;;

main;;
