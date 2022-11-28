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
          "my_var", Undecided,
          BinOp(
            Undecided, Add,
            ValI64(5),
            BinOp(
              Undecided, Mul,
              BinOp(
                Undecided, Sub,
                (* Note: Reversing these types -> LLVM type-mismatch crash *)
                ValI64(11),
                ValI32(7)
              ),
              ValI64 (8)
            )
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
      let tc_ctxt : typecheck_ctxt = {vars = StrMap.empty} in
      let (tc_ctxt_up, _) = type_check_stmt tc_ctxt decl_stmt_raw in
        test_typecheck ~tc_ctxt:tc_ctxt_up expr_raw;
        Printf.printf "Expr type: %s\n" (
          type_check_expr tc_ctxt_up expr_raw |> expr_type |> fmt_type
        );
        print_expr "" expr_raw;
        Printf.printf "\n";
        print_expr "" (type_check_expr tc_ctxt_up expr_raw);
        Printf.printf "\n";
      let return_stmt_raw = ReturnStmt(expr_raw) in

      let func_def = {
        f_name = "main";
        f_params = [];
        f_stmts = [
          decl_stmt_raw;
          return_stmt_raw;
        ];
      } in
      let func_def_typechecked = type_check_func func_def in

      codegen_func llvm_ctxt the_module the_fpm builder func_def_typechecked ;

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
