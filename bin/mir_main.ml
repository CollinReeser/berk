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
    let builder = Llvm.builder llvm_ctxt in
    let _ = begin
      initialize_fpm the_fpm |> ignore ;

      let trivial_func_def = {
        f_decl = {
          f_name = "trivial";
          f_ret_t = I8;
          f_params = [];
        };
        f_stmts = [ReturnStmt(ValI8(101))];
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
          DeclStmt(
            "my_func_var", {mut=false}, Undecided,
            ValFunc(Undecided, "trivial")
          );
          DeclStmt(
            "my_func_var_call", {mut=false}, Undecided,
            VarInvoke(Undecided, "my_func_var", [])
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
                ValCastTrunc(U32, ValU64(65));
                ValU16(66);
                ValCastBitwise(U8, ValI8(67));
              ]
            )
          );
          DeclStmt(
            "my_array_elem", {mut=false}, Undecided,
            StaticIndexExpr(Undecided, 1, ValVar(Undecided, "my_array"))
          );
          ExprStmt(
            FuncCall(
              Undecided, "printf", [
                ValStr("my_array_elem: %d\n");
                ValVar(Undecided, "my_array_elem")
              ]
            )
          );
          DeclDeconStmt(
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
          );
          DeclDeconStmt(
            [("a", {mut=false}); ("b", {mut=false}); ("c", {mut=false})],
            Undecided,
            TupleExpr(Undecided, [ValU64(64); ValStr("!"); ValU16(16);])
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
            "my_block_expr_res", {mut=false}, Undecided,
            BlockExpr(
              Undecided, [
                DeclStmt(
                  "my_int32", {mut=false}, Undecided, ValU32(15)
                );
                DeclStmt(
                  "my_int64", {mut=false}, Undecided, ValU64(30)
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
            VariantCtorExpr(Undecided, "Some", ValU32(101))
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
                    ValU32(1)
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
                    ValU32(2)
                  )
                );
              ]
            )
          );
          DeclStmt(
            "my_matched_bool_2", {mut=false}, Undecided,
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
                    ValU32(1)
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
                    ValU32(2)
                  )
                );
              ]
            )
          );
          DeclStmt(
            "my_matched_bool_3", {mut=false}, Undecided,
            let print_block str i =
              BlockExpr(
                Undecided, [
                  ExprStmt(
                    FuncCall(Undecided, "printf", [ValStr(str)])
                  )
                ],
                ValU32(i)
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
            "my_matched_bool_4", {mut=false}, Undecided,
            let print_block str i =
              BlockExpr(
                Undecided, [
                  ExprStmt(
                    FuncCall(Undecided, "printf", [ValStr(str)])
                  )
                ],
                ValU32(i)
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
            "my_matched_bool_5", {mut=false}, Undecided,
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
                ValU32(i)
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
                  tuple_bools true "tv1" true,
                  print_block "T?T, tv1: %d\n" "tv1" 1
                );
                (
                  tuple_bools true "tv2" false,
                  print_block "T?F, tv2: %d\n" "tv2" 2
                );
                (
                  tuple_bools false "tv3" true,
                  print_block "F?T, tv3: %d\n" "tv3" 3
                );
                (
                  tuple_bools false "tv4" false,
                  print_block "F?F, tv4: %d\n" "tv4" 4
                );
              ]
            )
          );
          (* DeclStmt(
            "my_matched_tuple", {mut=false}, Undecided,
            MatchExpr(
              Undecided,
              TupleExpr(Undecided, [ValBool(true); ValBool(false)]),
              [
                (PTuple(Undecided, [PBool(false); PBool(false)]), ValU32(1));
                (PTuple(Undecided, [PBool(false); PBool(true)]), ValU32(2));
                (PTuple(Undecided, [PBool(true); PBool(false)]), ValU32(3));
                (PTuple(Undecided, [PBool(true); PBool(true)]), ValU32(4))
              ]
            )
          ); *)
          (* DeclStmt(
            "my_unwrapped_some", {mut=false}, Undecided,
            MatchExpr(
              Undecided, ValVar(Undecided, "my_option_some"), [
                (
                  Ctor(Undecided, "Some", VarBind(Undecided, "x")),
                  ValVar(Undecided, "x")
                )
              ]
            )
          ); *)
          ReturnStmt(
            IfThenElseExpr(
              Undecided,
              BinOp(Undecided, Eq, ValU32(32), ValVar(Undecided, "c")),
              ValI8(40),
              ValI8(50)
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
      let _ = List.iter (
        fun mod_decl_typechecked ->
          match mod_decl_typechecked with
          | FuncExternDecl(f_decl_typechecked) ->
              Printf.printf "%s"
                (fmt_func_decl ~print_typ:true ~extern:true f_decl_typechecked)

          | FuncDef(f_ast_typechecked) ->
              Printf.printf "%s%s"
                (fmt_func_ast f_ast_typechecked)
                (fmt_func_ast ~print_typ:true f_ast_typechecked)

          | VariantDecl(v_ast_typechecked) ->
              Printf.printf "%s"
                (fmt_variant_decl ~pretty_unbound:true v_ast_typechecked)

      ) mod_decls_typechecked in

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
        ) mod_decls_typechecked
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
