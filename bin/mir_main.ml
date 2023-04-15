open Printexc

open Berk.Ast
open Berk.Codegen_mir
open Berk.Llvm_utility
open Berk.Mir
open Berk.Type_check
open Berk.Typing


let main = begin
  record_backtrace true;
  Llvm.enable_pretty_stacktrace ();

  begin
    let llvm_ctxt = Llvm.global_context () in
    let the_module = Llvm.create_module llvm_ctxt "main" in
    let the_fpm = Llvm.PassManager.create_function the_module in
    let the_mpm = Llvm.PassManager.create () in
    let builder = Llvm.builder llvm_ctxt in
    let _ = begin
      initialize_fpm the_fpm |> ignore ;
      initialize_mpm the_mpm |> ignore ;

      let trivial_func_def = {
        f_decl = {
          f_name = "trivial";
          f_ret_t = I8;
          f_params = [];
        };
        f_stmts = [ReturnStmt(ValInt(I8, 101))];
      } in

      let main_func_def = {
        f_decl = {
          f_name = "main";
          f_ret_t = I8;
          f_params = [];
        };
        f_stmts = [
          DeclStmt(
            "my_str", {mut=false}, Undecided, ValStr("Hello, world!")
          );
          ExprStmt(
            FuncCall(
              Undecided, "printf", [
                ValStr("%s\n");
                ValVar(Undecided, "my_str")
              ]
            )
          );
          DeclStmt(
            "iter", {mut=true}, Undecided,
            ValInt(Undecided, 0)
          );
          ExprStmt(
            WhileExpr(
              Undecided, [],
              BinOp(
                Undecided,
                Lt, ValVar(Undecided, "iter"), ValInt(Undecided, 10)
              ),
              [
                ExprStmt(
                  FuncCall(
                    Undecided, "printf", [
                      ValStr("iter: [%d]\n");
                      ValVar(Undecided, "iter")
                    ]
                  )
                );
                AssignStmt(
                  "iter", [],
                  BinOp(
                    Undecided,
                    Add, ValVar(Undecided, "iter"), ValInt(Undecided, 1)
                  )
                )
              ]
            )
          );
          ExprStmt(
            WhileExpr(
              Undecided,
              [
                DeclStmt(
                  "iter2", {mut=true}, Undecided,
                  ValInt(Undecided, 0)
                );
              ],
              BinOp(
                Undecided,
                Lt, ValVar(Undecided, "iter2"), ValInt(Undecided, 10)
              ),
              [
                ExprStmt(
                  FuncCall(
                    Undecided, "printf", [
                      ValStr("iter2: [%d]\n");
                      ValVar(Undecided, "iter2")
                    ]
                  )
                );
                AssignStmt(
                  "iter2", [],
                  BinOp(
                    Undecided,
                    Add, ValVar(Undecided, "iter2"), ValInt(Undecided, 1)
                  )
                )
              ]
            )
          );
          DeclStmt(
            "my_call", {mut=false}, Undecided,
            FuncCall(Undecided, "trivial", [])
          );
          ExprStmt(
            FuncCall(
              Undecided, "printf", [
                ValStr("trivial: %d\n");
                ValVar(Undecided, "my_call")
              ]
            )
          );
          (* "Generic variable names" that do not appear to resolve to anything
          in-scope are double-checked against the list of in-scope functions as
          well. If the "variable" is actually the name of a function, then the
          value resolves to the function pointer. *)
          DeclStmt(
            "my_func_var", {mut=false}, Undecided,
            ValName(Undecided, "trivial")
          );
          DeclStmt(
            "my_func_var_call", {mut=false}, Undecided,
            ExprInvoke(Undecided, ValVar(Undecided, "my_func_var"), [])
          );
          ExprStmt(
            FuncCall(
              Undecided, "printf", [
                ValStr("trivial (invoke): %d\n");
                ValVar(Undecided, "my_func_var_call")
              ]
            )
          );
          DeclStmt(
            "my_array", {mut=false}, Undecided,
            ArrayExpr(
              Undecided, [
                ValCast(U32, Truncate, ValInt(U64, 65));
                ValInt(U16, 66);
                ValCast(U8, Bitwise, ValInt(I8, 67));
              ]
            )
          );
          (* DeclDeconStmt(
            [("q", {mut=false}); ("r", {mut=false}); ("s", {mut=false})],
            Undecided,
            ValVar(Undecided, "my_array")
          );
          ExprStmt(
            FuncCall(
              Undecided, "printf", [
                ValStr("q: %d, r: %d, s: %d\n");
                ValVar(Undecided, "q");
                ValVar(Undecided, "r");
                ValVar(Undecided, "s");
              ]
            )
          ); *)
          DeclDeconStmt(
            [("a", {mut=false}); ("b", {mut=false}); ("c", {mut=false})],
            Undecided,
            TupleExpr(
              Undecided, [
                ValInt(U64, 64); ValStr("!"); ValInt(U16, 16)
              ]
            )
          );
          ExprStmt(
            FuncCall(
              Undecided, "printf", [
                ValStr("a: %d, b: %s, c: %d\n");
                ValVar(Undecided, "a");
                ValVar(Undecided, "b");
                ValVar(Undecided, "c");
              ]
            )
          );
          DeclStmt(
            "mut_tuple", {mut=true}, Undecided,
            TupleExpr(
              Undecided, [
                ValInt(U64, 12345); ValStr("?"); ValInt(U16, 321)
              ]
            )
          );
          AssignStmt("mut_tuple", [ALStaticIndex(0)], ValInt(U64, 23456));
          AssignStmt("mut_tuple", [ALStaticIndex(2)], ValInt(U16, 432));
          DeclDeconStmt(
            [("m", {mut=false}); ("n", {mut=false}); ("o", {mut=false})],
            Undecided,
            ValVar(Undecided, "mut_tuple")
          );
          ExprStmt(
            FuncCall(
              Undecided, "printf", [
                ValStr("m: %d, n: %s, o: %d\n");
                ValVar(Undecided, "m");
                ValVar(Undecided, "n");
                ValVar(Undecided, "o");
              ]
            )
          );
          DeclStmt(
            "my_block_expr_res", {mut=false}, Undecided,
            BlockExpr(
              Undecided, [
                DeclStmt(
                  "my_int32", {mut=false}, Undecided, ValInt(U32, 15)
                );
                DeclStmt(
                  "my_int64", {mut=false}, Undecided, ValInt(U64, 30)
                );
              ],
              BinOp(
                Undecided, Add,
                ValVar(Undecided, "my_int32"),
                ValVar(Undecided, "my_int64")
              )
            )
          );
          DeclStmt(
            "my_option_some", {mut=false}, Undecided,
            VariantCtorExpr(
              Undecided, "Some",
              TupleExpr(Undecided, [ValBool(true); ValBool(false)])
            )
          );
          DeclStmt(
            "my_matched_bool", {mut=false}, Undecided,
            MatchExpr(
              Undecided,
              ValBool(true),
              [
                (
                  PBool(false),
                  BlockExpr(
                    Undecided, [
                      ExprStmt(
                        FuncCall(Undecided, "printf", [ValStr("False arm!\n")])
                      )
                    ],
                    ValInt(U32, 1)
                  )
                );
                (
                  PBool(true),
                  BlockExpr(
                    Undecided, [
                      ExprStmt(
                        FuncCall(Undecided, "printf", [ValStr("True arm!\n")])
                      )
                    ],
                    ValInt(U32, 2)
                  )
                );
              ]
            )
          );
          DeclStmt(
            "my_matched_bool", {mut=false}, Undecided,
            MatchExpr(
              Undecided,
              ValBool(false),
              [
                (
                  PBool(false),
                  BlockExpr(
                    Undecided, [
                      ExprStmt(
                        FuncCall(Undecided, "printf", [ValStr("False arm!\n")])
                      )
                    ],
                    ValInt(U32, 1)
                  )
                );
                (
                  PBool(true),
                  BlockExpr(
                    Undecided, [
                      ExprStmt(
                        FuncCall(Undecided, "printf", [ValStr("True arm!\n")])
                      )
                    ],
                    ValInt(U32, 2)
                  )
                );
              ]
            )
          );
          DeclStmt(
            "my_matched_bool", {mut=false}, Undecided,
            let print_block str i =
              BlockExpr(
                Undecided, [
                  ExprStmt(
                    FuncCall(Undecided, "printf", [ValStr(str)])
                  )
                ],
                ValInt(U32, i)
              )
            in
            MatchExpr(
              Undecided,
              TupleExpr(Undecided, [ValBool(false); ValBool(true)]),
              [
                (
                  PTuple(Undecided, [PBool(true); PBool(true)]),
                  print_block "TT\n" 1
                );
                (
                  PTuple(Undecided, [PBool(true); PBool(false)]),
                  print_block "TF\n" 2
                );
                (
                  PTuple(Undecided, [PBool(false); PBool(true)]),
                  print_block "FT\n" 3
                );
                (
                  PTuple(Undecided, [PBool(false); PBool(false)]),
                  print_block "FF\n" 4
                )
              ]
            )
          );
          DeclStmt(
            "my_matched_bool", {mut=false}, Undecided,
            let print_block str i =
              BlockExpr(
                Undecided, [
                  ExprStmt(
                    FuncCall(Undecided, "printf", [ValStr(str)])
                  )
                ],
                ValInt(U32, i)
              )
            in
            let tuple_bools a b c =
              PTuple(
                Undecided, [
                  PTuple(Undecided, [PBool(a); PBool(b)]);
                  PBool(c)
                ]
              )
            in
            MatchExpr(
              Undecided,
              TupleExpr(
                Undecided, [
                  TupleExpr(Undecided, [ValBool(false); ValBool(true)]);
                  ValBool(false)
                ]
              ),
              [
                (tuple_bools true true true, print_block "TTT\n" 1);
                (tuple_bools true true false, print_block "TTF\n" 2);
                (tuple_bools true false true, print_block "TFT\n" 3);
                (tuple_bools true false false, print_block "TFF\n" 4);
                (tuple_bools false true true, print_block "FTT\n" 1);
                (tuple_bools false true false, print_block "FTF\n" 2);
                (tuple_bools false false true, print_block "FFT\n" 3);
                (tuple_bools false false false, print_block "FFF\n" 4);
              ]
            )
          );
          DeclStmt(
            "my_matched_bool", {mut=false}, Undecided,
            let print_block str var i =
              BlockExpr(
                Undecided, [
                  ExprStmt(
                    FuncCall(
                      Undecided, "printf",
                      [ValStr(str); ValVar(Undecided, var)]
                    )
                  )
                ],
                ValInt(U32, i)
              )
            in
            let tuple_bools a var c =
              PTuple(
                Undecided, [
                  PTuple(Undecided, [PBool(a); VarBind(Undecided, var)]);
                  PBool(c)
                ]
              )
            in
            MatchExpr(
              Undecided,
              TupleExpr(
                Undecided, [
                  TupleExpr(Undecided, [ValBool(true); ValBool(true)]);
                  ValBool(false)
                ]
              ),
              [
                (
                  tuple_bools true "tv" true,
                  print_block "T?T, tv: %d\n" "tv" 1
                );
                (
                  tuple_bools true "tv" false,
                  print_block "T?F, tv: %d\n" "tv" 2
                );
                (
                  tuple_bools false "tv" true,
                  print_block "F?T, tv: %d\n" "tv" 3
                );
                (
                  tuple_bools false "tv" false,
                  print_block "F?F, tv: %d\n" "tv" 4
                );
              ]
            )
          );
          DeclStmt(
            "my_unwrapped_some", {mut=false}, Undecided,
            let block_result str i =
              BlockExpr(
                Undecided, [
                  ExprStmt(
                    FuncCall(
                      Undecided, "printf", [ValStr(str)]
                    )
                  )
                ],
                ValInt(U32, i)
              )
            in
            MatchExpr(
              Undecided, ValVar(Undecided, "my_option_some"), [
                (
                  Ctor(Undecided, "Some", VarBind(Undecided, "x")),
                  MatchExpr(
                    Undecided, ValVar(Undecided, "x"), [
                      (
                        PTuple(Undecided, [PBool(false); PBool(false)]),
                        block_result "Unwrapped option (b, b): FF\n" 1
                      );
                      (
                        PTuple(Undecided, [PBool(false); PBool(true)]),
                        block_result "Unwrapped option (b, b): FT\n" 2
                      );
                      (
                        PTuple(Undecided, [PBool(true); PBool(false)]),
                        block_result "Unwrapped option (b, b): TF\n" 3
                      );
                      (
                        PTuple(Undecided, [PBool(true); PBool(true)]),
                        block_result "Unwrapped option (b, b): TT\n" 4
                      )
                    ]
                  )
                );
                (
                  Ctor(Undecided, "None", Wild(Undecided)),
                  ValInt(U32, 5)
                )
              ]
            )
          );
          ExprStmt(
            let block_result x y z q r s =
              BlockExpr(
                Undecided, [
                  ExprStmt(
                    FuncCall(
                      Undecided, "printf", [
                        ValStr(
                          "Individual vals: [%d, %d, %d]\n" ^
                          "As breakdown: [%d, %d, %d]\n"
                        );
                        ValVar(Undecided, x);
                        ValVar(Undecided, y);
                        ValVar(Undecided, z);
                        ValVar(Undecided, q);
                        ValVar(Undecided, r);
                        ValVar(Undecided, s)
                      ]
                    )
                  )
                ],
                ValNil
              )
            in
            MatchExpr(
              Undecided,
              TupleExpr(
                Undecided, [ValBool(true); ValBool(false); ValBool(true)]
              ), [
                (
                  PatternAs(
                    Undecided,
                    PTuple(
                      Undecided, [
                        VarBind(Undecided, "tup_a");
                        VarBind(Undecided, "tup_b");
                        VarBind(Undecided, "tup_c")
                      ]
                    ),
                    "as_tuple_val"
                  ),
                  MatchExpr(
                    Undecided,
                    ValVar(Undecided, "as_tuple_val"), [
                      (
                        PTuple(
                          Undecided, [
                            VarBind(Undecided, "as_tup_a");
                            VarBind(Undecided, "as_tup_b");
                            VarBind(Undecided, "as_tup_c")
                          ]
                        ),
                        block_result
                          "tup_a"
                          "tup_b"
                          "tup_c"
                          "as_tup_a"
                          "as_tup_b"
                          "as_tup_c"
                      )
                    ]
                  )
                );
              ]
            )
          );
          ReturnStmt(
            IfThenElseExpr(
              Undecided,
              BinOp(Undecided, Eq, ValInt(U32, 32), ValVar(Undecided, "c")),
              ValInt(I8, 40),
              ValInt(I8, 50)
            )
          );
        ];
      } in

      let variant_decls = [
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
      ] in

      let func_decls = [
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
      ] in

      let func_defs = [
        trivial_func_def;
        main_func_def;
      ] in

      let mod_decls =
        variant_decls @
        func_decls @
        (List.map (fun func_def -> FuncDef(func_def)) func_defs)
      in

      let _ =
        List.iter (
          fun func_def -> Printf.printf "%s" (fmt_func_ast func_def)
        ) func_defs
      in

      let mod_decls_typechecked = type_check_mod_decls mod_decls in

      let mod_decls_tc_rewritten =
        List.map (
          fun mod_decl ->
            match mod_decl with
            | FuncDef(func_def) ->
                let func_def_rewritten = rewrite_to_unique_varnames func_def in
                FuncDef(func_def_rewritten)

            | FuncExternDecl(_)
            | VariantDecl(_) -> mod_decl
        ) mod_decls_typechecked
      in

      let _ = List.iter (
        fun mod_decl_typechecked ->
          let fmted =
            fmt_mod_decl
              ~pretty_unbound:true ~print_typ:true mod_decl_typechecked
          in

          Printf.printf "%s" fmted
      ) mod_decls_tc_rewritten in

      let mir_ctxts =
        List.filter_map (
          fun mod_decl ->
            begin match mod_decl with
              | VariantDecl(_) -> None

              | FuncExternDecl(func_decl) ->
                  let mir_ctxt = func_decl_to_mir func_decl in
                  Some(mir_ctxt)
              | FuncDef(f_ast) ->
                  let mir_ctxt = func_to_mir f_ast in
                  Some(mir_ctxt)
            end
        ) mod_decls_tc_rewritten
      in

      let _ =
        List.iter (
          fun mir_ctxt -> Printf.printf "%s%!" (fmt_mir_ctxt mir_ctxt)
        ) mir_ctxts
      in

      let data_layout_str = Llvm.data_layout the_module in
      let data_layout_mod = Llvm_target.DataLayout.of_string data_layout_str in

      let llvm_sizeof typ =
        let llvm_sizeof_int64 =
          Llvm_target.DataLayout.store_size typ data_layout_mod
        in
        Int64.to_int llvm_sizeof_int64
      in

      let mod_gen_ctxt : module_gen_context = {
        func_sigs = StrMap.empty;
        llvm_mod = the_module;
        data_layout_mod = data_layout_mod;
        berk_t_to_llvm_t = berk_t_to_llvm_t llvm_sizeof llvm_ctxt;
        llvm_sizeof = llvm_sizeof;
      } in

      let _ =
        codegen_func_mirs
          llvm_ctxt
          the_fpm
          the_mpm
          builder
          mod_gen_ctxt
          mir_ctxts
      in

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
