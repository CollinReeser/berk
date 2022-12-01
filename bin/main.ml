open Printexc

open Ast
open Pretty_print
open Typing
open Type_check
open Codegen
open Test


let main = begin
  record_backtrace true;
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
              DeclStmt("my_inner_var_1", def_var_qual, Undecided, ValI64(51));
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
              AssignStmt("my_inner_var_2", ValVar(Undecided, "my_inner_var_3"));
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
      let decl_false_recursion_raw = (
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
      let return_stmt_raw = ReturnStmt(ValCastTrunc(I8, expr_raw)) in

      let func_def = {
        f_name = "main";
        f_ret_t = I8;
        f_params = [];
        f_stmts = [
          decl_stmt_raw;
          decl_stmt_float_raw;
          decl_stmt_bool_raw;
          decl_stmt_bitcast_raw;
          decl_false_recursion_raw;
          return_stmt_raw;
        ];
      } in

      print_func_ast func_def ;
      let mod_decl = FuncDecl(func_def) in
      let mod_decl_typechecked = type_check_mod_decl mod_decl in
      let _ = match mod_decl_typechecked with
      | FuncDecl(f_ast_typechecked) -> begin
        print_func_ast f_ast_typechecked ;
        print_func_ast ~print_typ:true f_ast_typechecked ;
      end in

      codegen_mod_decl llvm_ctxt the_module the_fpm builder mod_decl_typechecked ;

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
