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

      let main_func_def = {
        f_decl = {
          f_name = "main";
          f_ret_t = I8;
          f_params = [];
        };
        f_stmts = [
          DeclDeconStmt(
            [("a", {mut=false}); ("b", {mut=false}); ("c", {mut=false})],
            Undecided,
            TupleExpr(Undecided, [ValU64(64); ValU32(32); ValU16(16);])
          );
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

      let _ = Printf.printf "%s" (fmt_func_ast main_func_def) in

      let mod_decls = [
        FuncDef(main_func_def);
      ] in

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

      let mir_ctxt =
        func_to_mir (type_check_func default_mod_ctxt main_func_def)
      in

      let _ = Printf.printf "%s%!" (fmt_mir_ctxt mir_ctxt) in

      let _ =
        codegen_func_mirs
          the_module
          llvm_ctxt
          the_fpm
          builder
          [mir_ctxt]
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
