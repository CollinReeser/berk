open Ast
open Pretty_print
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
      DeclStmt(
        "abc", Undecided,
        BinOp(
          Undecided, Add,
          ValI32(5),
          BinOp(
            Undecided, Mul,
            BinOp(
              Undecided, Sub,
              ValI32(6),
              ValI32(7)
            ),
            ValI32(8)
          )
        )
      );
      ExprStmt(
        IfThenElseExpr(
          Undecided,
          ValBool(true),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(31));
            ]
          ),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(32));
            ]
          )
        )
      );
      DeclStmt(
        "def", I64,
        IfThenElseExpr(
          Undecided,
          ValBool(false),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(33));
            ]
          ),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(34));
            ]
          )
        )
      );
    ];
  }
;;


let test_typecheck ?(tc_ctxt : typecheck_ctxt = {vars = StrMap.empty}) ast =
  Printf.printf "Expression [";
  print_expr "" ast;
  Printf.printf "] typechecks to: ";
  let expr_typechecked = type_check_expr tc_ctxt ast in
  let expr_t = expr_type expr_typechecked in
  Printf.printf "%s" (fmt_type expr_t);
  Printf.printf "\n"
;;


let test_suite =
  print_func_ast build_example_ast;

  test_typecheck (BinOp(Undecided, Add, ValI32(1), ValI32(2)));
  test_typecheck (BinOp(Undecided, Add, ValI32(1), ValI64(2)));
  test_typecheck (BinOp(Undecided, Add, ValI64(1), ValI64(2)));

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(true),
      BlockExpr(Undecided, []),
      BlockExpr(Undecided, [])
    )
  );

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(true),
      BlockExpr(
        Undecided, [
          ResolveStmt(ValI32(11));
        ]
      ),
      BlockExpr(
        Undecided, [
          ResolveStmt(ValI64(12));
        ]
      )
    )
  );

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(false),
      BlockExpr(
        Undecided, [
          DeclStmt(
            "egh", I64,
            BinOp(
              Undecided, Add,
              ValI64(5),
              BinOp(
                Undecided, Mul,
                BinOp(
                  Undecided, Sub,
                  ValI64(6),
                  ValI64(7)
                ),
                ValI64 (8)
              )
            )
          );
          ResolveStmt(ValI64(22));
        ]
      ),
      BlockExpr(
        Undecided, [
          DeclStmt("ijk", Undecided, ValBool(false));
          ResolveStmt(ValI64(24));
        ]
      )
    )
  );

  Printf.printf "%!" ;

  ()
