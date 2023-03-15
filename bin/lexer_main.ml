open Berk.Ast
open Berk.Codegen_mir
open Berk.Lexer
open Berk.Llvm_utility
open Berk.Mir
open Berk.Parser
open Berk.Type_check


let () =
  let source_text = {|
    extern fn printf(fmt: string, ...): i32

    fn fib_t(n: u64, s_last: u64, last: u64): u64 {
      if (n == 1) {
        return last;
      };
      return fib_t(n - 1, last, s_last + last);
    }

    fn fib(n: u64): u64 {
      return fib_t(n, 0, 1);
    }

    fn ret_int(): i32 {
      return 20;
    }

    fn main(): i8 {
      let my_str = "Hello, world! [%d] [%llu]\n";
      let var = 6 + 7 * 8 - ret_int();
      let var2: i32 = 6 + 7 * 8 - ret_int();
      let fib_res = fib(50);
      printf(my_str, var, fib_res);

      let mut tup = (1, 2, 3);
      tup.1 = 4;

      let left = tup.0;
      let middle = tup.1;
      let right = tup.2;

      printf("Tuple: left[%d], mid[%d], right[%d]\n", left, middle, right);

      let fn_ptr = ret_int;
      let fn_ptr_val = fn_ptr.();

      printf("fn ptr val: [%d] [%d]\n", fn_ptr_val, fn_ptr.());

      let fn_tup = (fib, fib);
      printf("Double-indirection fib: [%llu]\n", fn_tup.1.(50));

      while {let mut iter: u32 = 0;} iter < 16 {
        printf("iter: %d\n", iter);

        iter = iter + 1;
      }

      return 0;
    }
  |} in

  Printexc.record_backtrace true ;
  Llvm.enable_pretty_stacktrace () ;

  (* Lexing. *)
  let lexbuf = Sedlexing.Latin1.from_gen (Gen.of_string source_text) in
  let tokens = tokenize lexbuf in
  print_tokens tokens ;

  (* Parsing into module-declaration AST list. *)
  let mod_decls = parse_tokens ~trace:true tokens in

  (* Currently require declaration before use, but we build a list of module
  declarations in reverse order. *)
  let mod_decls = List.rev mod_decls in

  (* Typechecking. *)
  let mod_decls_tc = type_check_mod_decls mod_decls in

  (* Uniquify varnames for MIR generation. *)
  let mod_decls_tc_rewritten =
    List.map (
      fun mod_decl ->
        match mod_decl with
        | FuncDef(func_def) ->
            let func_def_rewritten = rewrite_to_unique_varnames func_def in
            FuncDef(func_def_rewritten)

        | FuncExternDecl(_)
        | VariantDecl(_) -> mod_decl
    ) mod_decls_tc
  in

  (* Print typechecked source. *)
  let asts_fmted =
    List.map
      (fmt_mod_decl ~pretty_unbound:true ~print_typ:true)
      mod_decls_tc_rewritten
  in
  let _ = List.iter (Printf.printf "%s") asts_fmted in

  (* Generate MIR. *)
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

  (* Print MIR. *)
  let _ =
    List.iter (
      fun mir_ctxt -> Printf.printf "%s%!" (fmt_mir_ctxt mir_ctxt)
    ) mir_ctxts
  in

  (* Setup LLVM context. *)
  Llvm.enable_pretty_stacktrace ();
  let llvm_ctxt = Llvm.global_context () in
  let the_module = Llvm.create_module llvm_ctxt "main" in
  let the_fpm = Llvm.PassManager.create_function the_module in
  let the_mpm = Llvm.PassManager.create () in
  let builder = Llvm.builder llvm_ctxt in
  let _ = initialize_fpm the_fpm |> ignore in
  let _ = initialize_mpm the_mpm |> ignore in

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

  (* MIR -> LLVM codegen. *)
  let _ =
    codegen_func_mirs
      llvm_ctxt
      the_fpm
      the_mpm
      builder
      mod_gen_ctxt
      mir_ctxts
  in

  (* Dump various output files from populated LLVM context. *)
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
;;

