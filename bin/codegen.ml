open Ast
open Typing

module StrMap = Map.Make(String)

type codegen_ctxt = {
  cur_func: Llvm.llvalue;
  vars: Llvm.llvalue StrMap.t;
}

let berk_t_to_llvm_t llvm_ctxt typ =
  match typ with
  | U64 | I64 -> Llvm.i64_type llvm_ctxt
  | U32 | I32 -> Llvm.i32_type llvm_ctxt
  | U16 | I16 -> Llvm.i16_type llvm_ctxt
  | U8  | I8  -> Llvm.i8_type  llvm_ctxt

  | F128 -> Llvm.fp128_type  llvm_ctxt
  | F64  -> Llvm.double_type llvm_ctxt
  | F32  -> Llvm.float_type  llvm_ctxt

  | Bool -> Llvm.i1_type llvm_ctxt

  | Nil -> failwith "Should not need to determine type for nil"
  | Undecided -> failwith "Cannot determine llvm type for undecided type"


let resolve_alloca_name = "___RESOLVE_ALLOCA"
let if_expr_alloca_name = "___IF_THEN_ELSE_ALLOCA"
;;


let rec codegen_func llvm_ctxt the_mod the_fpm builder {f_name; f_stmts; _} =
  let i64_t = Llvm.i64_type llvm_ctxt in
  let ints_empty = Array.make 0 i64_t in
  let func_sig_t = Llvm.function_type i64_t ints_empty in
  let new_func = Llvm.declare_function f_name func_sig_t the_mod in
  let bb = Llvm.append_block llvm_ctxt "entry" new_func in
  let gen_ctxt = {cur_func = new_func; vars = StrMap.empty} in
  Llvm.position_at_end bb builder ;
  codegen_stmts llvm_ctxt builder gen_ctxt f_stmts |> ignore ;

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

and codegen_stmts llvm_ctxt builder gen_ctxt stmts =
  match stmts with
  | [] -> gen_ctxt
  | x::xs ->
      let gen_ctxt_updated = codegen_stmt llvm_ctxt builder gen_ctxt x in
      codegen_stmts llvm_ctxt builder gen_ctxt_updated xs


and codegen_stmt (llvm_ctxt) (builder) (gen_ctxt) (stmt) : codegen_ctxt =
  match stmt with
  | DeclStmt (ident, _, typ, expr) ->
      let alloca_typ = berk_t_to_llvm_t llvm_ctxt typ in
      let alloca = Llvm.build_alloca alloca_typ ident builder in
      let expr_val = codegen_expr llvm_ctxt builder gen_ctxt expr in
      let _ : Llvm.llvalue = Llvm.build_store expr_val alloca builder in

      let updated_vars = StrMap.add ident alloca gen_ctxt.vars in
      let gen_ctxt_up = {gen_ctxt with vars = updated_vars} in

      gen_ctxt_up

  | AssignStmt (ident, expr) ->
      let alloca = StrMap.find ident gen_ctxt.vars in
      let expr_val = codegen_expr llvm_ctxt builder gen_ctxt expr in
      let _ : Llvm.llvalue = Llvm.build_store expr_val alloca builder in

      gen_ctxt

  | ReturnStmt(expr) ->
      let return_val = codegen_expr llvm_ctxt builder gen_ctxt expr in
      let _ : Llvm.llvalue = Llvm.build_ret return_val builder in

      gen_ctxt

  | ExprStmt (expr) ->
      let _ = codegen_expr llvm_ctxt builder gen_ctxt expr in

      gen_ctxt

  | ResolveStmt (expr) ->
      let expr_val = codegen_expr llvm_ctxt builder gen_ctxt expr in
      let resolve_alloca = StrMap.find resolve_alloca_name gen_ctxt.vars in
      let _ : Llvm.llvalue = Llvm.build_store expr_val resolve_alloca builder in

      gen_ctxt


and codegen_expr llvm_ctxt builder gen_ctxt expr =
  let i64_t = Llvm.i64_type llvm_ctxt in
  let i32_t = Llvm.i32_type llvm_ctxt in
  let i16_t = Llvm.i16_type llvm_ctxt in
  let i8_t  = Llvm.i8_type  llvm_ctxt in

  let f128_t = Llvm.fp128_type  llvm_ctxt in
  let f64_t  = Llvm.double_type llvm_ctxt in
  let f32_t  = Llvm.float_type  llvm_ctxt in

  let bool_t = Llvm.i1_type llvm_ctxt in

  let _codegen_expr = codegen_expr llvm_ctxt builder gen_ctxt in

  match expr with
  | ValU64(n) | ValI64(n) -> Llvm.const_int i64_t n
  | ValU32(n) | ValI32(n) -> Llvm.const_int i32_t n
  | ValU16(n) | ValI16(n) -> Llvm.const_int i16_t n
  | ValU8(n)  | ValI8(n)  -> Llvm.const_int  i8_t n
  | ValBool(false) -> Llvm.const_int bool_t 0
  | ValBool(true)  -> Llvm.const_int bool_t 1
  | ValF128(str) -> Llvm.const_float_of_string f128_t str
  | ValF64(n)  -> Llvm.const_float f64_t  n
  | ValF32(n)  -> Llvm.const_float f32_t  n
  | ValVar(_, ident) ->
      let alloca = StrMap.find ident gen_ctxt.vars in
      let loaded : Llvm.llvalue = Llvm.build_load alloca ident builder in
      loaded
  | BinOp(typ, op, lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      let llvm_t = berk_t_to_llvm_t llvm_ctxt typ in
      begin match typ with
      | U64 | U32 | U16 | U8 ->
          let lhs_comm = Llvm.build_intcast lhs_val llvm_t "ucasttmp" builder in
          let rhs_comm = Llvm.build_intcast rhs_val llvm_t "ucasttmp" builder in
          begin match op with
          | Add -> Llvm.build_add lhs_comm rhs_comm "uaddtmp" builder
          | Sub -> Llvm.build_sub lhs_comm rhs_comm "usubtmp" builder
          | Mul -> Llvm.build_mul lhs_comm rhs_comm "umultmp" builder
          | Less ->
              Llvm.build_icmp Llvm.Icmp.Ult lhs_comm rhs_comm "uicmptmp" builder
          | LessEq ->
              Llvm.build_icmp Llvm.Icmp.Ule lhs_comm rhs_comm "uicmptmp" builder
          end
      | I64 | I32 | I16 | I8 ->
          let lhs_comm = Llvm.build_intcast lhs_val llvm_t "icasttmp" builder in
          let rhs_comm = Llvm.build_intcast rhs_val llvm_t "icasttmp" builder in
          begin match op with
          | Add -> Llvm.build_add lhs_comm rhs_comm "iaddtmp" builder
          | Sub -> Llvm.build_sub lhs_comm rhs_comm "isubtmp" builder
          | Mul -> Llvm.build_mul lhs_comm rhs_comm "imultmp" builder
          | Less ->
              Llvm.build_icmp Llvm.Icmp.Slt lhs_comm rhs_comm "iicmptmp" builder
          | LessEq ->
              Llvm.build_icmp Llvm.Icmp.Sle lhs_comm rhs_comm "iicmptmp" builder
          end
      | F128 | F64 | F32 ->
          let lhs_comm = Llvm.build_fpcast lhs_val llvm_t "fcasttmp" builder in
          let rhs_comm = Llvm.build_fpcast rhs_val llvm_t "fcasttmp" builder in
          begin match op with
          | Add -> Llvm.build_fadd lhs_comm rhs_comm "faddtmp" builder
          | Sub -> Llvm.build_fsub lhs_comm rhs_comm "fsubtmp" builder
          | Mul -> Llvm.build_fmul lhs_comm rhs_comm "fmultmp" builder
          | Less ->
              Llvm.build_fcmp Llvm.Fcmp.Ult lhs_comm rhs_comm "fcmptmp" builder
          | LessEq ->
              Llvm.build_fcmp Llvm.Fcmp.Ule lhs_comm rhs_comm "fcmptmp" builder
          end
      | typ ->
        failwith (
          Printf.sprintf
            "Unexpected expression type in BinOp: %s" (fmt_type typ)
        )
      end
  | BlockExpr(typ, stmts) ->
      let alloca_typ = berk_t_to_llvm_t llvm_ctxt typ in
      let alloca = Llvm.build_alloca alloca_typ resolve_alloca_name builder in
      let updated_vars = StrMap.add resolve_alloca_name alloca gen_ctxt.vars in
      let gen_ctxt_up = {gen_ctxt with vars = updated_vars} in

      let _ = codegen_stmts llvm_ctxt builder gen_ctxt_up stmts in

      let loaded = Llvm.build_load alloca resolve_alloca_name builder in

      loaded

  | IfThenElseExpr(typ, cond_expr, then_expr, else_expr) ->
      let bb_then = Llvm.append_block llvm_ctxt "if_then" gen_ctxt.cur_func in
      let bb_else = Llvm.append_block llvm_ctxt "if_else" gen_ctxt.cur_func in
      let bb_if_end = Llvm.append_block llvm_ctxt "if_end" gen_ctxt.cur_func in

      let alloca_typ = berk_t_to_llvm_t llvm_ctxt typ in
      let alloca = Llvm.build_alloca alloca_typ if_expr_alloca_name builder in

      let cond_val = _codegen_expr cond_expr in

      let _ = Llvm.build_cond_br cond_val bb_then bb_else builder in

      let _ = Llvm.position_at_end bb_then builder in
      let then_val = _codegen_expr then_expr in
      let _ : Llvm.llvalue = Llvm.build_store then_val alloca builder in
      let _ = Llvm.build_br bb_if_end builder in

      let _ = Llvm.position_at_end bb_else builder in
      let else_val = _codegen_expr else_expr in
      let _ : Llvm.llvalue = Llvm.build_store else_val alloca builder in
      let _ = Llvm.build_br bb_if_end builder in

      let _ = Llvm.position_at_end bb_if_end builder in

      let loaded = Llvm.build_load alloca if_expr_alloca_name builder in

      loaded
;;


let initialize_fpm the_fpm =
  (*
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
  (* Promote allocas to registers again; this second round can remove more
  redundant code. *)
  Llvm_scalar_opts.add_memory_to_register_promotion the_fpm ;
  *)

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
