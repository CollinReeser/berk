open Printexc

open Ast
open Pretty_print
open Typing
open Type_check
open Codegen
open Test


let main = begin
  record_backtrace true;
  Llvm.enable_pretty_stacktrace ();
  test_suite;

  begin
    let llvm_ctxt = Llvm.global_context () in
    let the_module = Llvm.create_module llvm_ctxt "main" in
    let the_fpm = Llvm.PassManager.create_function the_module in
    let builder = Llvm.builder llvm_ctxt in
    let _ = begin
      initialize_fpm the_fpm |> ignore ;

      let decl_stmt_raw = (
        DeclStmt(
          "my_var", def_var_qual, Undecided,
          BlockExpr(
            Undecided, [
              DeclStmt(
                "my_inner_var_1", def_var_qual, Undecided,
                ValI64(51)
              );
              DeclStmt(
                "my_inner_var_2", {mut = true}, Undecided,
                ValVar(Undecided, "my_inner_var_1")
              );
              DeclStmt(
                "my_inner_var_3", def_var_qual, Undecided,
                IfThenElseExpr(
                  Undecided,
                  BinOp(Undecided, Less, ValI8(11), ValI64(9)),
                  ValI64(6),
                  IfThenElseExpr(
                    Undecided,
                    BinOp(Undecided, GreaterEq, ValF64(11.12), ValF32(9.34)),
                    BlockExpr(Undecided, [ResolveStmt(ValI64(9))]),
                    ValI64(8)
                  )
                )
              );
              AssignStmt(
                "my_inner_var_2", ValVar(Undecided, "my_inner_var_3")
              );
              ResolveStmt(
                BinOp(
                  Undecided, Add,
                  ValVar(Undecided, "my_inner_var_2"),
                  BinOp(
                    Undecided, Mul,
                    BinOp(
                      Undecided, Sub,
                      ValI32(11),
                      ValI64(7)
                    ),
                    ValVar(Undecided, "my_inner_var_3")
                  )
                )
              );
            ]
          )
        )
      ) in
      let decl_stmt_float_raw = (
        DeclStmt(
          "my_float_var", def_var_qual, Undecided,
          BinOp(
            Undecided, Add,
            ValF32(123.456),
            BinOp(
              Undecided, Mul,
              BinOp(
                Undecided, Sub,
                ValF128("12345.6789"),
                ValF64(2345.6789)
              ),
              ValF64(1234.5678)
            )
          )
        )
      ) in
      let decl_stmt_bool_raw = (
        DeclStmt(
          "my_bool_var", def_var_qual, Undecided,
          BinOp(
            Undecided, Eq,
            BinOp(
              Undecided, Mod,
              ValI16(7), ValI16(2)
            ),
            ValI32(1)
          )
        )
      ) in
      let decl_stmt_bitcast_raw = (
        DeclStmt(
          "my_bitcast_var", def_var_qual,
          U32,
          ValCastBitwise(U32, ValI32(-32000))
        )
      ) in
      let decl_dodge_recursion_raw = (
        DeclStmt(
          "my_recursive_dodge_var", def_var_qual, Undecided,
          IfThenElseExpr(
            Undecided,
            ValBool(true),
            ValI8(6),
            FuncCall(Undecided, "main", [])
          )
        )
      ) in
      let decl_call_recursion_raw = (
        DeclStmt(
          "my_recursive_dodge_var", def_var_qual, Undecided,
          FuncCall(Undecided, "rec_me", [ValI8(100)])
        )
      ) in
      let decl_array_raw = (
        DeclStmt(
          "my_array_var", def_var_qual, Undecided,
          ArrayExpr(
            Undecided, [
              ValI8(10);
              ValI8(9);
              ValI8(8);
              ValI8(7);
              ValI8(6);
            ]
          )
        )
      ) in
      let decl_array_static_idx_raw = (
        DeclStmt(
          "my_array_static_idx_var", def_var_qual, Undecided,
          StaticIndexExpr(
            Undecided, 2,
            ValVar(Undecided, "my_array_var")
          )
        )
      ) in
      let decl_array_idx_raw = (
        DeclStmt(
          "my_array_idx_var", def_var_qual, Undecided,
          IndexExpr(
            Undecided,
            ValU64(2),
            ValVar(Undecided, "my_array_var")
          )
        )
      ) in
      let decl_tuple_raw = (
        DeclStmt(
          "my_tuple_var", def_var_qual, Undecided,
          TupleExpr(
            Undecided, [
              ValI8(10);
              ValU8(9);
              ValI32(8);
              ValU32(7);
              ValBool(false);
            ]
          )
        )
      ) in
      let decl_tuple_unpack_lit_raw = (
        DeclDeconStmt(
          [
            ("my_tuple_lit_unpack_var_1", {mut = true});
            ("my_tuple_lit_unpack_var_2", def_var_qual);
            ("my_tuple_lit_unpack_var_3", {mut = true});
          ],
          Undecided,
          TupleExpr(
            Undecided, [
              ValI8(13);
              ValU16(12);
              ValI32(11);
            ]
          )
        )
      ) in
      let decl_tuple_unpack_var_raw = (
        DeclDeconStmt(
          [
            ("my_tuple_var_unpack_var_1", def_var_qual);
            ("my_tuple_var_unpack_var_2", def_var_qual);
            ("my_tuple_var_unpack_var_3", def_var_qual);
            ("my_tuple_var_unpack_var_4", def_var_qual);
            ("my_tuple_var_unpack_var_5", def_var_qual);
          ],
          Undecided,
          ValVar(Undecided, "my_tuple_var")
        )
      ) in
      let assign_tuple_unpack_lit_raw = (
        AssignDeconStmt(
          [
            ("my_tuple_lit_unpack_var_1");
            ("my_tuple_lit_unpack_var_3");
          ],
          TupleExpr(
            Undecided, [
              ValI8(13);
              ValI32(11);
            ]
          )
        )
      ) in
      let expr_raw = (
        BinOp(
          Undecided, Add,
          ValI64(5),
          ValVar(Undecided, "my_var")
        )
      )
      in
      let tc_ctxt : typecheck_context = default_tc_ctxt Undecided in
      let (tc_ctxt_up, _) = type_check_stmt tc_ctxt decl_stmt_raw in
        test_typecheck ~tc_ctxt:tc_ctxt_up expr_raw;
        Printf.printf "Expr type: %s\n" (
          type_check_expr tc_ctxt_up expr_raw |> expr_type |> fmt_type
        );
        print_expr "" expr_raw;
        Printf.printf "\n";
        print_expr "" (type_check_expr tc_ctxt_up expr_raw);
        Printf.printf "\n";
      let return_stmt_raw = ReturnStmt(
        (* BinOp(
          Undecided, Add,
          ValVar(Undecided, "my_array_idx_var"),
          BinOp(
            Undecided, Add,
            ValCastTrunc(I8, expr_raw),
            ValVar(Undecided, "my_recursive_dodge_var")
          )
        ) *)

        ValCastBitwise(
          I8,
          FuncCall(
            Undecided, "tailcall_collatz_len", [ValU8(12)]
          )
        )
      ) in

      let main_func_def = {
        f_name = "main";
        f_ret_t = I8;
        f_params = [];
        f_stmts = [
          decl_stmt_raw;
          decl_stmt_float_raw;
          decl_stmt_bool_raw;
          decl_stmt_bitcast_raw;
          decl_dodge_recursion_raw;
          decl_call_recursion_raw;
          decl_array_raw;
          decl_array_static_idx_raw;
          decl_array_idx_raw;
          decl_tuple_raw;
          decl_tuple_unpack_lit_raw;
          decl_tuple_unpack_var_raw;
          assign_tuple_unpack_lit_raw;
          return_stmt_raw;
        ];
      } in

      print_func_ast main_func_def ;

      let rec_func_def = {
        f_name = "rec_me";
        f_ret_t = I8;
        f_params = ["counter", def_var_qual, I8];
        f_stmts = [
          ReturnStmt(
            IfThenElseExpr(
              Undecided,
              BinOp(Undecided, Eq, ValVar(Undecided, "counter"), ValI8(5)),
              ValVar(Undecided, "counter"),
              FuncCall(
                Undecided, "rec_me", [
                  BinOp(Undecided, Sub, ValVar(Undecided, "counter"), ValI8(1))
                ]
              )
            )
          )
        ];
      } in

      let collatz_len_internal_func_def = {
        f_name = "collatz_len_internal";
        f_ret_t = U64;
        f_params = [("cur", def_var_qual, U64); ("len", def_var_qual, U64)];
        f_stmts = [
          ReturnStmt(
            IfThenElseExpr(
              Undecided,
              BinOp(Undecided, Eq, ValVar(Undecided, "cur"), ValU64(1)),
              ValVar(Undecided, "len"),
              IfThenElseExpr(
                Undecided,
                BinOp(
                  Undecided, Eq,
                  ValU64(1),
                  BinOp(Undecided, Mod, ValVar(Undecided, "cur"), ValU64(2))
                ),
                FuncCall(
                  Undecided, "collatz_len_internal", [
                    BinOp(
                      Undecided, Add,
                      ValU64(1),
                      BinOp(Undecided, Mul, ValVar(Undecided, "cur"), ValU64(3))
                    );
                    BinOp(Undecided, Add, ValVar(Undecided, "len"), ValU64(1));
                  ]
                ),
                FuncCall(
                  Undecided, "collatz_len_internal", [
                    BinOp(
                      Undecided, Div,
                      ValVar(Undecided, "cur"),
                      ValU64(2)
                    );
                    BinOp(Undecided, Add, ValVar(Undecided, "len"), ValU64(1));
                  ]
                )
              )
            )
          )
        ];
      } in

      let collatz_len_func_def = {
        f_name = "collatz_len";
        f_ret_t = U64;
        f_params = ["start", def_var_qual, U64];
        f_stmts = [
          ReturnStmt(
            FuncCall(
              Undecided, "collatz_len_internal", [
                ValVar(Undecided, "start");
                ValU64(1);
              ]
            )
          )
        ];
      } in

      let tailcall_collatz_len_internal_func_def = {
        f_name = "tailcall_collatz_len_internal";
        f_ret_t = U8;
        f_params = [("cur", def_var_qual, U8); ("len", def_var_qual, U8)];
        f_stmts = [
          BlockStmt(
            [
              IfThenElseStmt(
                BinOp(Undecided, Eq, ValVar(Undecided, "cur"), ValU8(1)),
                BlockStmt(
                  [
                    ReturnStmt(
                      ValVar(Undecided, "len")
                    );
                  ]
                ),
                IfThenElseStmt(
                  BinOp(
                    Undecided, Eq,
                    ValU8(1),
                    BinOp(Undecided, Mod, ValVar(Undecided, "cur"), ValU8(2))
                  ),
                  BlockStmt(
                    [
                      ReturnStmt(
                        FuncCall(
                          Undecided, "tailcall_collatz_len_internal", [
                            BinOp(
                              Undecided, Add,
                              ValU8(1),
                              BinOp(
                                Undecided, Mul,
                                ValVar(Undecided, "cur"),
                                ValU8(3)
                              )
                            );
                            BinOp(
                              Undecided, Add,
                              ValVar(Undecided, "len"),
                              ValU8(1)
                            );
                          ]
                        )
                      );
                    ]
                  ),
                  BlockStmt(
                    [
                      ReturnStmt(
                        FuncCall(
                          Undecided, "tailcall_collatz_len_internal", [
                            BinOp(
                              Undecided, Div,
                              ValVar(Undecided, "cur"),
                              ValU8(2)
                            );
                            BinOp(
                              Undecided, Add,
                              ValVar(Undecided, "len"),
                              ValU8(1)
                            );
                          ]
                        )
                      );
                    ]
                  )
                )
              );
            ]
          )
        ];
      } in

      let tailcall_collatz_len_func_def = {
        f_name = "tailcall_collatz_len";
        f_ret_t = U8;
        f_params = ["start", def_var_qual, U8];
        f_stmts = [
          ReturnStmt(
            FuncCall(
              Undecided, "tailcall_collatz_len_internal", [
                ValVar(Undecided, "start");
                ValU8(1);
              ]
            )
          )
        ];
      } in

      let return_tuple_func_def = {
        f_name = "return_tuple";
        f_ret_t = Tuple([U8; U16; F32]);
        f_params = [];
        f_stmts = [
          ReturnStmt(
            TupleExpr(
              Undecided, [
                ValU8(13);
                ValU16(56);
                ValF32(66.77);
              ]
            )
          )
        ];
      } in

      let mod_decls = [
        FuncDecl(rec_func_def);
        FuncDecl(collatz_len_internal_func_def);
        FuncDecl(collatz_len_func_def);
        FuncDecl(tailcall_collatz_len_internal_func_def);
        FuncDecl(tailcall_collatz_len_func_def);
        FuncDecl(return_tuple_func_def);
        FuncDecl(main_func_def);
      ] in

      let mod_decls_typechecked = type_check_mod_decls mod_decls in
      let _ = List.iter (
        fun mod_decl_typechecked ->
          match mod_decl_typechecked with
          | FuncDecl(f_ast_typechecked) -> begin
            print_func_ast f_ast_typechecked ;
            print_func_ast ~print_typ:true f_ast_typechecked ;
          end
      ) mod_decls_typechecked in

      Printf.printf "%!";

      codegen_mod_decls
        llvm_ctxt
        the_module
        the_fpm
        builder
        mod_decls_typechecked
      ;

      ()
    end in

    let filename_ll = "output.ll" in
    dump_llvm_ir filename_ll the_module ;

    let filename_asm = "output.s" in
    let file_type = Llvm_target.CodeGenFileType.AssemblyFile in
    dump_to_file file_type filename_asm the_fpm the_module ;

    let filename_obj = "output.o" in
    let file_type = Llvm_target.CodeGenFileType.ObjectFile in
    dump_to_file file_type filename_obj the_fpm the_module ;

    let filename_exe = "output" in
    generate_executable filename_exe filename_obj ;

    ()
  end
end
;;

main;;
