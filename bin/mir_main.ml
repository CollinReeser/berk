open Printexc

open Berk.Ast
open Berk.Codegen_mir
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
          ReturnStmt(
            IfThenElseExpr(
              Undecided,
              BinOp(Undecided, Eq, ValU16(20), ValU16(30)),
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

      let data_layout_str = Llvm.data_layout the_module in
      let data_layout_mod = Llvm_target.DataLayout.of_string data_layout_str in

      let llvm_sizeof typ =
        let llvm_sizeof_int64 =
          Llvm_target.DataLayout.store_size typ data_layout_mod
        in
        Int64.to_int llvm_sizeof_int64
      in

      let mod_ctxt = {
        func_sigs = StrMap.empty;
        llvm_mod = the_module;
        data_layout_mod = data_layout_mod;
        berk_t_to_llvm_t = berk_t_to_llvm_t llvm_sizeof llvm_ctxt;
        llvm_sizeof = llvm_sizeof;
      } in

      let _ =
        codegen_func_mir
          llvm_ctxt
          the_fpm
          builder
          mod_ctxt
          mir_ctxt
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
