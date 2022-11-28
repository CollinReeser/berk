open Ast
open Pretty_print
open Typing
open Type_check
open Codegen
open Test


let main = begin
  test_suite;

  begin
    let llvm_ctxt = Llvm.global_context () in
    let the_module = Llvm.create_module llvm_ctxt "main" in
    let the_fpm = Llvm.PassManager.create_function the_module in
    let builder = Llvm.builder llvm_ctxt in
    let _ = begin
      initialize_fpm the_fpm |> ignore ;

      let i64_t = Llvm.i64_type llvm_ctxt in
      let doubles_empty = Array.make 0 i64_t in
      let func_sig_t = Llvm.function_type i64_t doubles_empty in
      let func_name = "main" in
      let new_func = Llvm.declare_function func_name func_sig_t the_module in
      let bb = Llvm.append_block llvm_ctxt "entry" new_func in
      Llvm.position_at_end bb builder ;

      let expr_raw = (
        BinOp(
          Undecided, Add,
          ValI64(5),
          BinOp(
            Undecided, Mul,
            BinOp(
              Undecided, Sub,
              ValI64(11),
              ValI64(7)
            ),
            ValI64 (8)
          )
        )
      )
      in
        test_typecheck expr_raw;
        Printf.printf "Expr type: %s\n" (
          type_check_expr expr_raw |> expr_type |> fmt_type
        );
        print_expr "" expr_raw;
        Printf.printf "\n";
        print_expr "" (type_check_expr expr_raw);
        Printf.printf "\n";

      let stmt_raw = ReturnStmt(expr_raw) in

      let stmt_typechecked = type_check_stmt stmt_raw in
      let _ = codegen_stmt llvm_ctxt builder stmt_typechecked in
      (* let return_val = codegen_expr llvm_ctxt builder expr_typechecked in *)

      (* let _ : Llvm.llvalue = Llvm.build_ret return_val builder in *)
      (* Validate the generated code, checking for consistency. *)
      let _ = begin
        match Llvm_analysis.verify_function new_func with
        | true -> ()
        | false ->
          begin
            Printf.printf "invalid function generated\n%s\n"
              (Llvm.string_of_llvalue new_func) ;
            Llvm_analysis.assert_valid_function new_func ;
            ()
          end
      end in
      (* Optimize the function. *)
      let _ : bool = Llvm.PassManager.run_function new_func the_fpm in
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
