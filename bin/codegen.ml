open Ast
open Pretty_print


let rec codegen_expr llvm_ctxt builder expr =
  let i64_t = Llvm.i64_type llvm_ctxt in
  let i32_t = Llvm.i32_type llvm_ctxt in
  let f32_t = Llvm.float_type llvm_ctxt in
  let bool_t = Llvm.i8_type llvm_ctxt in
  let _codegen_expr = codegen_expr llvm_ctxt builder in

  match expr with
  | ValI64(n) -> Llvm.const_int i64_t n
  | ValI32(n) -> Llvm.const_int i32_t n
  | ValF32(n) -> Llvm.const_float f32_t n
  | ValBool(false) -> Llvm.const_int bool_t 0
  | ValBool(true)  -> Llvm.const_int bool_t 1
  | BinOp(typ, op, lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      begin match typ with
      | I64 | I32 ->
          begin match op with
          | Add -> Llvm.build_add lhs_val rhs_val "addtmp" builder
          | Sub -> Llvm.build_sub lhs_val rhs_val "addtmp" builder
          | Mul -> Llvm.build_mul lhs_val rhs_val "addtmp" builder
          end
      | F32 ->
          begin match op with
          | Add -> Llvm.build_fadd lhs_val rhs_val "addtmp" builder
          | Sub -> Llvm.build_fsub lhs_val rhs_val "addtmp" builder
          | Mul -> Llvm.build_fmul lhs_val rhs_val "addtmp" builder
          end
      | typ ->
        failwith (
          Printf.sprintf
            "Unexpected expression type in BinOp: %s" (fmt_type typ)
        )
      end
  | BlockExpr(_) -> failwith "not implemented"
  | IfThenElseExpr(_) -> failwith "not implemented"
;;


let initialize_fpm the_fpm =
  (* Promote allocas to registers. *)
  Llvm_scalar_opts.add_memory_to_register_promotion the_fpm ;
  (* Do simple "peephole" optimizations and bit-twiddling optzn. *)
  Llvm_scalar_opts.add_instruction_combination the_fpm ;
  (* reassociate expressions. *)
  Llvm_scalar_opts.add_reassociation the_fpm ;
  (* Eliminate Common SubExpressions. *)
  Llvm_scalar_opts.add_gvn the_fpm ;
  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  Llvm_scalar_opts.add_cfg_simplification the_fpm ;
  (* Return value here only indicates whether internal state was modified *)
  Llvm.PassManager.initialize the_fpm
;;


let dump_to_file file_type filename the_fpm the_module =
  Llvm_all_backends.initialize ();
  (* "x86_64-pc-linux-gnu" *)
  let target_triple = Llvm_target.Target.default_triple () in
  let target = Llvm_target.Target.by_triple target_triple in
  let cpu = "generic" in
  let reloc_mode = Llvm_target.RelocMode.Default in
  let machine = Llvm_target.TargetMachine.create ~triple:target_triple ~cpu ~reloc_mode target in
  let data_layout = Llvm_target.TargetMachine.data_layout machine |> Llvm_target.DataLayout.as_string in
  Llvm.set_target_triple target_triple the_module;
  Llvm.set_data_layout data_layout the_module;
  Llvm_target.TargetMachine.add_analysis_passes the_fpm machine;
  Llvm_target.TargetMachine.emit_to_file the_module file_type filename machine;
  Printf.printf "Wrote %s\n" filename;
  ()
;;


let dump_llvm_ir filename the_module =
  Llvm.print_module filename the_module ;
  Printf.printf "Wrote %s\n" filename;
  ()
;;


let generate_executable filename_exe filename_obj =
  let cmd = Printf.sprintf "clang -o %s %s" filename_exe filename_obj in
  begin match Sys.command cmd with
    | 0 -> Printf.printf "Wrote %s\n" filename_exe
    | n -> Printf.printf "clang failed with %d\n" n
  end
;;
