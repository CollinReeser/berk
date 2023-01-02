open Berk.Ast
open Berk.Type_check
open Berk.Typing


let build_example_ast : func_def_t =
  {
    f_decl = {
      f_name = "example_func";
      f_params = [
        ("arg_1", def_var_qual, I64);
        ("arg_2", def_var_qual, I64);
      ];
      f_ret_t = Undecided;
    };
    f_stmts = [
      DeclStmt(
        "abc", def_var_qual, Undecided,
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
          BlockExpr(Undecided, [], ValI64(31)),
          BlockExpr(Undecided, [], ValI64(32))
        )
      );
      DeclStmt(
        "def", def_var_qual, I64,
        IfThenElseExpr(
          Undecided,
          ValBool(false),
          BlockExpr(Undecided, [], ValI64(33)),
          BlockExpr(Undecided, [], ValI64(34))
        )
      );
    ];
  }
;;


let test_typecheck ?(
  tc_ctxt : typecheck_context = {
    vars = StrMap.empty;
    ret_t = Undecided;
    ret_t_candidates = [];
    mod_ctxt = default_mod_ctxt
  }
) ast =
  let expr_typechecked = type_check_expr tc_ctxt Undecided ast in
  let expr_t = expr_type expr_typechecked in

  Printf.printf "Expression [[ %s ]] typechecks to [[ %s ]]\n"
    (fmt_expr "" ast)
    (fmt_type expr_t)
;;


let test_suite =
  Printf.printf "%s" (fmt_func_ast build_example_ast);

  test_typecheck (BinOp(Undecided, Add, ValI32(1), ValI32(2)));
  test_typecheck (BinOp(Undecided, Add, ValI32(1), ValI64(2)));
  test_typecheck (BinOp(Undecided, Add, ValI64(1), ValI64(2)));

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(true),
      BlockExpr(Undecided, [], ValNil),
      BlockExpr(Undecided, [], ValNil)
    )
  );

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(true),
      BlockExpr(Undecided, [], ValI32(11)),
      BlockExpr(Undecided, [], ValI64(12))
    )
  );

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(false),
      BlockExpr(
        Undecided, [
          DeclStmt(
            "egh", def_var_qual, I64,
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
        ],
        ValI64(22)
      ),
      BlockExpr(
        Undecided, [
          DeclStmt("ijk", def_var_qual, Undecided, ValBool(false));
        ],
        ValI64(24)
      )
    )
  );

  Printf.printf "%!" ;

  ()
