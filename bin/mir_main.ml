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
          DeclStmt(
            "my_call", {mut=false}, Undecided,
            FuncCall(Undecided, "trivial", [])
          );
          DeclStmt(
            "my_func_var", {mut=false}, Undecided, ValFunc(Undecided, "trivial")
          );
          DeclStmt(
            "my_func_var_call", {mut=false}, Undecided,
            VarInvoke(Undecided, "my_func_var", [])
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
          DeclDeconStmt(
            [("q", {mut=false}); ("r", {mut=false}); ("s", {mut=false})],
            Undecided,
            ValVar(Undecided, "my_array")
          );
          DeclDeconStmt(
            [("a", {mut=false}); ("b", {mut=false}); ("c", {mut=false})],
            Undecided,
            TupleExpr(Undecided, [ValU64(64); ValU32(32); ValU16(16);])
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

      let func_defs = [
        trivial_func_def;
        main_func_def;
      ] in

      let mod_decls =
        variant_decls @
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
              | FuncExternDecl(_)
              | VariantDecl(_) -> None

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
