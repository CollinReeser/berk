open Ast
open Pretty_print
open Typing
open Type_check


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
