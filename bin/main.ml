(*
AST for the berk language.
*)

type berk_type =
  | I64
  | I32
  | Bool

type ident_t = string

type cond_block = {
  cond: expr;
  stmts: stmt list;
}
and expr =
  | ValI64 of int
  | ValI32 of int
  | ValBool of bool
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
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
  | ResolveStmt of expr
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

let rec common_type_of_lr lhs rhs =
  match (lhs, rhs) with
  | (Some(I64), Some(I64)) -> Some(I64)
  | (Some(Bool), Some(Bool)) -> Some(Bool)
  | _ -> None

and common_type_of_lst lst =
  match lst with
  | [] -> None
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs


let rec type_check_if_expr_stmts stmts =
  let resolve_stmt_types =
    List.filter_map (
      fun st ->
        match st with
        | ResolveStmt ex -> Some(type_check_expr ex)
        | _ -> None
    ) stmts
  in
  match resolve_stmt_types with
  | [] -> None
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs
and type_check_expr exp =
  match exp with
  | ValI64(_) -> Some(I64)
  | ValI32(_) -> Some(I32)
  | ValBool(_) -> Some(Bool)
  | Add(lhs, rhs) ->
      let lhs_type = type_check_expr lhs in
      let rhs_type = type_check_expr rhs in
      common_type_of_lr lhs_type rhs_type
  | Sub(lhs, rhs) ->
      let lhs_type = type_check_expr lhs in
      let rhs_type = type_check_expr rhs in
      common_type_of_lr lhs_type rhs_type
  | Mul(lhs, rhs) ->
      let lhs_type = type_check_expr lhs in
      let rhs_type = type_check_expr rhs in
      common_type_of_lr lhs_type rhs_type
  | IfExpr({
      if_block = {cond = if_cond; stmts = if_stmts};
      else_if_blocks;
      else_block;
    }) ->
      let if_cond_type = type_check_expr if_cond in
      let if_stmts_type = type_check_if_expr_stmts if_stmts in
      let else_if_cond_type = (
        List.fold_left (
          fun lhs rhs ->
            match (lhs, rhs) with
            | (Some(Bool), Some(Bool)) -> Some(Bool)
            | _ -> None
        )
        (Some(Bool))
        (
          List.map (
            fun {cond; stmts = _} ->
              type_check_expr cond
          ) else_if_blocks
        )
      ) in
      let else_if_stmts_type =
        let else_if_stmts_types =
          List.map
            type_check_if_expr_stmts (
              List.map
                (fun {cond = _; stmts} -> stmts)
                else_if_blocks
            )
        in
        match else_if_stmts_types with
        | [] -> None
        | [x] -> x
        | x::xs -> List.fold_left common_type_of_lr x xs
      in
      let else_stmts_type =
        match else_block with
        | None -> None
        | Some(stmts) -> type_check_if_expr_stmts stmts
      in
      match (if_cond_type, else_if_cond_type) with
      | (Some(Bool), Some(Bool)) ->
          common_type_of_lst [
            if_stmts_type; else_if_stmts_type; else_stmts_type
          ]
      | _ -> None
;;


let build_example_ast =
  {
    f_name = "example_func";
    f_params = [
      {
        p_name = "arg_1";
        p_type = I64;
      };
      {
        p_name = "arg_2";
        p_type = I64;
      }
    ];
    f_stmts = [
      DeclDef(
        "abc", I64,
        Add(ValI64(5), Mul(Sub(ValI64(6), ValI64(7)), ValI64 (8)))
      );
      ExprStmt(
        IfExpr({
          if_block = {cond = ValI64(30); stmts = [ResolveStmt(ValI64(31))]};
          else_if_blocks = [
            {cond = ValI64(32); stmts = [ResolveStmt(ValI64(33))]};
            {cond = ValI64(34); stmts = [ResolveStmt(ValI64(35))]};
          ];
          else_block = Some([ResolveStmt(ValI64(35))])
        })
      );
      DeclDef(
        "def", I64,
        IfExpr({
          if_block = {cond = ValI64(50); stmts = [ExprStmt(ValI64(51))]};
          else_if_blocks = [];
          else_block = Some([ExprStmt(ValI64(55))])
        })
      );
      DeclDef(
        "ghi", I64,
        IfExpr({
          if_block = {cond = ValI64(50); stmts = [ExprStmt(ValI64(51))]};
          else_if_blocks = [];
          else_block = None;
        })
      );
      IfStmt({
        if_block = {cond = ValI64(40); stmts = [ExprStmt(ValI64(41))]};
        else_if_blocks = [
          {cond = ValI64(42); stmts = [ExprStmt(ValI64(43))]};
        ];
        else_block = Some([ExprStmt(ValI64(45))])
      })
    ];
  }
;;

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

let test_typecheck ast =
  Printf.printf "Expression [";
  print_expr "" ast;
  Printf.printf "] typechecks to: ";
  match type_check_expr ast with
  | None -> Printf.printf "<typecheck failed>\n"
  | Some(t) -> print_berk_type t; Printf.printf "\n"
;;

let main = (
  print_func_ast build_example_ast;

  test_typecheck (Add(ValI64(5), ValI64(6)));

  test_typecheck (
    IfExpr({
      if_block = {cond = ValBool(true); stmts = [ResolveStmt(ValI32(31))]};
      else_if_blocks = [
        {cond = ValBool(true); stmts = [ResolveStmt(ValI64(33))]};
        {cond = ValBool(true); stmts = [ResolveStmt(ValI32(35))]};
      ];
      else_block = Some([ResolveStmt(ValI64(35))])
    })
  );

  test_typecheck (
    IfExpr({
      if_block = {cond = ValBool(true); stmts = [ResolveStmt(ValI64(31))]};
      else_if_blocks = [
        {cond = ValBool(true); stmts = [ResolveStmt(ValBool(true))]};
        {cond = ValBool(true); stmts = [ResolveStmt(ValI64(35))]};
      ];
      else_block = Some([ResolveStmt(ValBool(false))])
    })
  );

  test_typecheck (
    IfExpr({
      if_block = {cond = ValBool(true); stmts = [ResolveStmt(ValBool(true))]};
      else_if_blocks = [
        {cond = ValBool(true); stmts = [ResolveStmt(ValBool(false))]};
      ];
      else_block = Some([ResolveStmt(ValBool(false))])
    })
  );
)
;;

main;;
