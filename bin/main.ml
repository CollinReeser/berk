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
                    BlockExpr(Undecided, [], ValI64(9)),
                    ValI64(8)
                  )
                )
              );
              AssignStmt(
                "my_inner_var_2", ValVar(Undecided, "my_inner_var_3")
              );
            ],
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
          type_check_expr tc_ctxt_up Undecided expr_raw |> expr_type |> fmt_type
        );
        print_expr "" expr_raw;
        Printf.printf "\n";
        print_expr "" (type_check_expr tc_ctxt_up Undecided expr_raw);
        Printf.printf "\n";

      let collatz_seq_stmt_raw =
        ExprStmt(
          FuncCall(
            Undecided, "collatz_print_seq", [ValU64(9)]
          )
        )
      in

      let return_stmt_raw =
        ExprStmt(
          BlockExpr(
            Undecided,
            [
              DeclDeconStmt(
                [
                  ("collatz_max_seed", def_var_qual);
                  ("collatz_max_len", def_var_qual);
                ],
                Undecided,
                FuncCall(
                  (* Undecided, "collatz_highest_seed", [ValU64(120)] *)
                  Undecided, "collatz_highest_seed", [ValU64(1000000)]
                )
              );
              DeclStmt(
                "_", def_var_qual,
                Undecided,
                FuncCall(
                  Undecided, "printf", [
                    ValStr("Hello, world!\n");
                  ]
                )
              );
              DeclStmt(
                "_", def_var_qual,
                Undecided,
                FuncCall(
                  Undecided, "printf", [
                    ValStr("Hello, world!\n");
                  ]
                )
              );
              DeclStmt(
                "_", def_var_qual,
                Undecided,
                FuncCall(
                  Undecided, "printf", [
                    ValStr("Max Seed: [%d]\n");
                    ValVar(Undecided, "collatz_max_seed");
                  ]
                )
              );
              DeclStmt(
                "_", def_var_qual,
                Undecided,
                FuncCall(
                  Undecided, "printf", [
                    ValStr("Max Len: [%d]\n");
                    ValVar(Undecided, "collatz_max_len");
                  ]
                )
              );
              DeclStmt(
                "_", def_var_qual,
                Undecided,
                FuncCall(
                  Undecided, "printf", [
                    ValStr("Max Seed: [%d]\nMax Len: [%d]\n");
                    ValVar(Undecided, "collatz_max_seed");
                    ValVar(Undecided, "collatz_max_len");
                  ]
                )
              );
              ReturnStmt(
                (* BinOp(
                  Undecided, Add,
                  ValVar(Undecided, "my_array_idx_var"),
                  BinOp(
                    Undecided, Add,
                    ValCastTrunc(I8, expr_raw),
                    ValVar(Undecided, "my_recursive_dodge_var")
                  )
                ) *)

                (* ValCastBitwise(
                  I8,
                  FuncCall(
                    Undecided, "tailcall_collatz_len", [ValU8(12)]
                  )
                ) *)

                ValCastBitwise(
                  I8, ValCastTrunc(U8, ValVar(Undecided, "collatz_max_seed"))
                )
              );
            ],
            ValNil
          )
        )
      in

      let main_func_def = {
        f_decl = {
          f_name = "main";
          f_ret_t = I8;
          f_params = [];
        };
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
          collatz_seq_stmt_raw;
          return_stmt_raw;
        ];
      } in

      print_func_ast main_func_def ;

      let rec_func_def = {
        f_decl = {
          f_name = "rec_me";
          f_ret_t = I8;
          f_params = ["counter", def_var_qual, I8];
        };
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
        f_decl = {
          f_name = "collatz_len_internal";
          f_ret_t = U64;
          f_params = [("cur", def_var_qual, U64); ("len", def_var_qual, U64)];
        };
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
        f_decl = {
          f_name = "collatz_len";
          f_ret_t = Undecided;
          f_params = ["start", def_var_qual, U64];
        };
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
        f_decl = {
          f_name = "tailcall_collatz_len_internal";
          f_ret_t = U64;
          f_params = [("cur", def_var_qual, U64); ("len", def_var_qual, U64)];
        };
        f_stmts = [
          ExprStmt(
            IfThenElseExpr(
              Undecided,
              BinOp(Undecided, Eq, ValVar(Undecided, "cur"), ValU8(1)),
              BlockExpr(
                Undecided, [
                  ReturnStmt(ValVar(Undecided, "len"));
                ],
                ValNil
              ),
              IfThenElseExpr(
                Undecided,
                BinOp(
                  Undecided, Eq,
                  ValU8(1),
                  BinOp(Undecided, Mod, ValVar(Undecided, "cur"), ValU8(2))
                ),
                BlockExpr(
                  Undecided,
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
                  ],
                  ValNil
                ),
                BlockExpr(
                  Undecided,
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
                  ],
                  ValNil
                )
              )
            )
          );
        ];
      } in

      let tailcall_collatz_len_func_def = {
        f_decl = {
          f_name = "tailcall_collatz_len";
          f_ret_t = U64;
          f_params = ["start", def_var_qual, U64];
        };
        f_stmts = [
          ReturnStmt(
            FuncCall(
              Undecided, "tailcall_collatz_len_internal", [
                ValVar(Undecided, "start");
                ValU64(1);
              ]
            )
          )
        ];
      } in

      let collatz_highest_seed_internal_func_def = {
        f_decl = {
          f_name = "collatz_highest_seed_internal";
          f_ret_t = Tuple([U64; U64]);
          f_params = [
            ("max_seed", def_var_qual, U64);
            ("max_len",  def_var_qual, U64);
            ("cur_seed", def_var_qual, U64);
            ("ceiling",  def_var_qual, U64);
          ];
        };
        f_stmts = [
          ExprStmt(
            IfThenElseExpr(
              Undecided,
              BinOp(
                Undecided, Greater,
                ValVar(Undecided, "cur_seed"), ValVar(Undecided, "ceiling")
              ),
              BlockExpr(
                Undecided, [
                  ReturnStmt(
                    TupleExpr(
                      Undecided,
                      [
                        ValVar(Undecided, "max_seed");
                        ValVar(Undecided, "max_len");
                      ]
                    )
                  )
                ],
                ValNil
              ),
              BlockExpr(
                Undecided,
                [
                  DeclStmt(
                    "cur_len", def_var_qual, Undecided,
                    FuncCall(
                      Undecided, "tailcall_collatz_len", [
                        ValVar(Undecided, "cur_seed")
                      ]
                    )
                  );
                  ExprStmt(
                    IfThenElseExpr(
                      Undecided,
                      BinOp(
                        Undecided, Greater,
                        ValVar(Undecided, "cur_len"),
                        ValVar(Undecided, "max_len")
                      ),
                      BlockExpr(
                        Undecided, [
                          ReturnStmt(
                            FuncCall(
                              Undecided, "collatz_highest_seed_internal", [
                                ValVar(Undecided, "cur_seed");
                                ValVar(Undecided, "cur_len");
                                BinOp(
                                  Undecided, Add,
                                  ValU8(1), ValVar(Undecided, "cur_seed")
                                );
                                ValVar(Undecided, "ceiling");
                              ]
                            )
                          )
                        ],
                        ValNil
                      ),
                      BlockExpr(
                        Undecided, [
                          ReturnStmt(
                            FuncCall(
                              Undecided, "collatz_highest_seed_internal", [
                                ValVar(Undecided, "max_seed");
                                ValVar(Undecided, "max_len");
                                BinOp(
                                  Undecided, Add,
                                  ValU8(1), ValVar(Undecided, "cur_seed")
                                );
                                ValVar(Undecided, "ceiling");
                              ]
                            )
                          )
                        ],
                        ValNil
                      )
                    )
                  )
                ],
                ValNil
              )
            )
          )
        ];
      } in

      let collatz_highest_seed_func_def = {
        f_decl = {
          f_name = "collatz_highest_seed";
          f_ret_t = Tuple([U64; U64]);
          f_params = ["ceiling", def_var_qual, U64];
        };
        f_stmts = [
          ReturnStmt(
            FuncCall(
              Undecided, "collatz_highest_seed_internal", [
                ValU64(1);
                ValU64(1);
                ValU64(1);
                ValVar(Undecided, "ceiling");
              ]
            )
          )
        ];
      } in

      let collatz_print_seq_func_def = {
        f_decl = {
          f_name = "collatz_print_seq";
          f_ret_t = Nil;
          f_params = ["cur", {mut = true}, U64];
        };
        f_stmts = [
          ExprStmt(
            BlockExpr(
              Undecided, [
                ExprStmt(
                  WhileExpr(
                    Undecided,
                    BinOp(
                      Undecided, NotEq,
                      ValVar(Undecided, "cur"),
                      ValU64(1)
                    ),
                    [
                      ExprStmt(
                        FuncCall(
                          Undecided, "printf", [
                            ValStr("  [%d]\n");
                            ValVar(Undecided, "cur");
                          ]
                        )
                      );
                      ExprStmt(
                        IfThenElseExpr(
                          Undecided,
                          BinOp(
                            Undecided,
                            Eq,
                            BinOp(
                              Undecided, Mod,
                              ValVar(Undecided, "cur"),
                              ValU64(2)
                            ),
                            ValU64(0)
                          ),
                          BlockExpr(
                            Undecided, [
                              AssignStmt(
                                "cur",
                                BinOp(
                                  Undecided,
                                  Div,
                                  ValVar(Undecided, "cur"),
                                  ValU64(2)
                                )
                              );
                            ],
                            ValNil
                          ),
                          BlockExpr(
                            Undecided, [
                              AssignStmt(
                                "cur",
                                BinOp(
                                  Undecided,
                                  Add,
                                  BinOp(
                                    Undecided,
                                    Mul,
                                    ValVar(Undecided, "cur"),
                                    ValU64(3)
                                  ),
                                  ValU64(1)
                                )
                              );
                            ],
                            ValNil
                          )
                        )
                      );
                    ],
                    ValNil
                  )
                );
                ExprStmt(
                  FuncCall(
                    Undecided, "printf", [
                      ValStr("  [%d]\n");
                      ValVar(Undecided, "cur");
                    ]
                  )
                );
                ReturnStmt(ValNil);
              ],
              ValNil
            );
          )
        ];
      } in

      let return_tuple_func_def = {
        f_decl = {
          f_name = "return_tuple";
          f_ret_t = Tuple([U8; U16; F32]);
          f_params = [];
        };
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

      let return_some_func_def = {
        f_decl = {
          f_name = "return_some";
          f_ret_t = Variant("Option", [("Some", Bool); ("None", Nil)]);
          f_params = [];
        };
        f_stmts = [
          DeclStmt(
            "dummy_some", def_var_qual, Undecided,
            VariantCtorExpr(Undecided, "Some", ValBool(true))
          );
          DeclStmt(
            "dummy_none", def_var_qual,
            Variant("Option", [("Some", Bool); ("None", Nil)]),
            VariantCtorExpr(Undecided, "None", ValNil)
          );
          DeclStmt(
            "dummy_integral_none", def_var_qual,
            Variant("Option", [("Some", F128); ("None", Nil)]),
            VariantCtorExpr(Undecided, "None", ValNil)
          );
          ReturnStmt(
            VariantCtorExpr(Undecided, "Some", ValBool(true))
          )
        ];
      } in

      let mod_decls = [
        VariantDecl(
          {
            v_name = "LeftOrRight";
            v_ctors = [
              ("Left", Nil);
              ("Right", Nil);
            ];
            v_typ_vars = [];
          }
        );
        VariantDecl(
          {
            v_name = "BooleanResult";
            v_ctors = [
              ("Ok", Bool);
              ("Err", String);
            ];
            v_typ_vars = [];
          }
        );
        VariantDecl(
          {
            v_name = "PointOrNothing";
            v_ctors = [
              ("Point", Tuple([F64; F64; F64]));
              ("Nothing", Nil);
            ];
            v_typ_vars = [];
          }
        );
        VariantDecl(
          {
            v_name = "Option";
            v_ctors = [
              ("Some", Unbound("`a"));
              ("None", Nil);
            ];
            v_typ_vars = ["`a"];
          }
        );
        FuncExternDecl(
          {
            f_name = "printf";
            f_params = [
              ("fmt", def_var_qual, String);
              ("vargs", def_var_qual, VarArgSentinel);
            ];
            f_ret_t = I32;
          }
        );
        FuncDef(rec_func_def);
        FuncDef(collatz_len_internal_func_def);
        FuncDef(collatz_len_func_def);
        FuncDef(tailcall_collatz_len_internal_func_def);
        FuncDef(tailcall_collatz_len_func_def);
        FuncDef(collatz_highest_seed_internal_func_def);
        FuncDef(collatz_highest_seed_func_def);
        FuncDef(return_tuple_func_def);
        FuncDef(collatz_print_seq_func_def);
        FuncDef(return_some_func_def);
        FuncDef(main_func_def);
      ] in

      let mod_decls_typechecked = type_check_mod_decls mod_decls in
      let _ = List.iter (
        fun mod_decl_typechecked ->
          match mod_decl_typechecked with
          | FuncExternDecl(f_decl_typechecked) ->
            print_func_decl ~print_typ:true ~extern:true f_decl_typechecked ;

          | FuncDef(f_ast_typechecked) -> begin
            print_func_ast f_ast_typechecked ;
            print_func_ast ~print_typ:true f_ast_typechecked ;
          end

          | VariantDecl(v_ast_typechecked) ->
            begin
              print_variant_decl ~pretty_unbound:true v_ast_typechecked ;
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

    let _ = begin
      let rec tailcall_collatz_len_internal cur_len cur_val =
        if cur_val = 1
        then cur_len

        else if cur_val mod 2 == 0
        then tailcall_collatz_len_internal (cur_len + 1) (cur_val / 2)
        else tailcall_collatz_len_internal (cur_len + 1) (cur_val * 3 + 1)


      and collatz_len start_val =
        tailcall_collatz_len_internal 1 start_val


      and collatz_highest_seed_internal max_seed max_len cur_seed ceiling =
        if cur_seed > ceiling
        then (max_seed, max_len)
        else
          begin
            let cur_len = collatz_len cur_seed in
            if cur_len > max_len
            then collatz_highest_seed_internal cur_seed cur_len (cur_seed + 1) ceiling
            else collatz_highest_seed_internal max_seed max_len (cur_seed + 1) ceiling
          end


      and collatz_highest_seed ceiling =
        collatz_highest_seed_internal 1 1 1 ceiling

      in

      (* let (highest_seed, max_len) = collatz_highest_seed 120 in *)
      let (highest_seed, max_len) = collatz_highest_seed 1000000 in
      Printf.printf "Highest seed: [%d], max len: [%d]" highest_seed max_len
    end in

    ()
  end
end
;;

main;;
