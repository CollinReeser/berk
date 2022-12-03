open Ast
open Typing

module StrMap = Map.Make(String)

type module_gen_context = {
  func_sigs: Llvm.llvalue StrMap.t;
}

let default_mod_gen_ctxt = {func_sigs = StrMap.empty}

type func_gen_context = {
  cur_func: Llvm.llvalue;
  cur_vars: Llvm.llvalue StrMap.t;
  mod_ctxt: module_gen_context
}


let rec berk_t_to_llvm_t llvm_ctxt typ =
  match typ with
  | U64 | I64 -> Llvm.i64_type llvm_ctxt
  | U32 | I32 -> Llvm.i32_type llvm_ctxt
  | U16 | I16 -> Llvm.i16_type llvm_ctxt
  | U8  | I8  -> Llvm.i8_type  llvm_ctxt

  | F128 -> Llvm.fp128_type  llvm_ctxt
  | F64  -> Llvm.double_type llvm_ctxt
  | F32  -> Llvm.float_type  llvm_ctxt

  | Bool -> Llvm.i1_type llvm_ctxt

  | Array(elem_typ, sz) ->
      let llvm_elem_t = berk_t_to_llvm_t llvm_ctxt elem_typ in
      let llvm_arr_t = Llvm.array_type llvm_elem_t sz in
      Llvm.pointer_type llvm_arr_t

  | Tuple(types) ->
      let llvm_t_lst = List.map (berk_t_to_llvm_t llvm_ctxt) types in
      let llvm_t_arr = Array.of_list llvm_t_lst in
      let llvm_tuple_t = Llvm.struct_type llvm_ctxt llvm_t_arr in
      Llvm.pointer_type llvm_tuple_t

  | Nil -> failwith "Should not need to determine type for nil"
  | Undecided -> failwith "Cannot determine llvm type for undecided type"


let resolve_alloca_name = "___RESOLVE_ALLOCA"
let if_expr_alloca_name = "___IF_THEN_ELSE_ALLOCA"
;;


let rec codegen_mod_decls llvm_ctxt the_mod the_fpm builder mod_decls =
  let mod_ctxt = default_mod_gen_ctxt in
  let _codegen_mod_decl =
    fun ctxt decl ->
      codegen_mod_decl llvm_ctxt the_mod the_fpm builder ctxt decl
  in
  let _ = List.fold_left _codegen_mod_decl mod_ctxt mod_decls in
  ()


and codegen_mod_decl llvm_ctxt the_mod the_fpm builder mod_ctxt mod_decl =
  match mod_decl with
  | FuncDecl(f_ast) ->
      codegen_func llvm_ctxt the_mod the_fpm builder mod_ctxt f_ast


and codegen_func llvm_ctxt the_mod the_fpm builder mod_ctxt f_ast =
  let {f_name; f_stmts; f_ret_t; f_params} = f_ast in

  let llvm_ret_t = berk_t_to_llvm_t llvm_ctxt f_ret_t in
  let llvm_param_t_lst = List.map (
    fun (_, _, typ) -> berk_t_to_llvm_t llvm_ctxt typ
  ) f_params
  in
  let llvm_param_t_arr = Array.of_list llvm_param_t_lst in
  let func_sig_t = Llvm.function_type llvm_ret_t llvm_param_t_arr in
  let new_func = Llvm.declare_function f_name func_sig_t the_mod in

  let bb = Llvm.append_block llvm_ctxt "entry" new_func in
  let _ = Llvm.position_at_end bb builder in

  let func_sigs_up = StrMap.add f_name new_func mod_ctxt.func_sigs in
  let mod_ctxt_up = {func_sigs = func_sigs_up} in

  let llvm_params = Array.to_list (Llvm.params new_func) in

  let arg_to_param_lst = List.combine f_params llvm_params in

  let llvm_param_allocas = List.map (
    fun ((id, _, typ), llvm_param) ->
      let alloca_typ = berk_t_to_llvm_t llvm_ctxt typ in
      let alloca = Llvm.build_alloca alloca_typ id builder in
      let _ : Llvm.llvalue = Llvm.build_store llvm_param alloca builder in

      alloca
  ) arg_to_param_lst in

  let arg_to_alloca_lst = List.combine f_params llvm_param_allocas in

  let init_vars = List.fold_left (
    fun vars ((id, _, _), param) -> StrMap.add id param vars
  ) StrMap.empty arg_to_alloca_lst
  in

  let func_ctxt = {
    cur_func = new_func;
    cur_vars = init_vars;
    mod_ctxt = mod_ctxt_up
  } in

  codegen_stmts llvm_ctxt builder func_ctxt f_stmts |> ignore ;

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

  mod_ctxt_up


and codegen_stmts llvm_ctxt builder func_ctxt stmts =
  match stmts with
  | [] -> func_ctxt
  | x::xs ->
      let func_ctxt_updated = codegen_stmt llvm_ctxt builder func_ctxt x in
      codegen_stmts llvm_ctxt builder func_ctxt_updated xs


and codegen_stmt (llvm_ctxt) (builder) (func_ctxt) (stmt) : func_gen_context =
  match stmt with
  | DeclStmt (ident, _, typ, expr) ->
      let alloca_typ = berk_t_to_llvm_t llvm_ctxt typ in
      let alloca = Llvm.build_alloca alloca_typ ident builder in
      let expr_val = codegen_expr llvm_ctxt builder func_ctxt expr in
      let _ : Llvm.llvalue = Llvm.build_store expr_val alloca builder in

      let updated_vars = StrMap.add ident alloca func_ctxt.cur_vars in
      let func_ctxt_up = {func_ctxt with cur_vars = updated_vars} in

      func_ctxt_up

  | AssignStmt (ident, expr) ->
      let alloca = StrMap.find ident func_ctxt.cur_vars in
      let expr_val = codegen_expr llvm_ctxt builder func_ctxt expr in
      let _ : Llvm.llvalue = Llvm.build_store expr_val alloca builder in

      func_ctxt

  | ReturnStmt(expr) ->
      let return_val = codegen_expr llvm_ctxt builder func_ctxt expr in
      let _ : Llvm.llvalue = Llvm.build_ret return_val builder in

      func_ctxt

  | ExprStmt (expr) ->
      let _ = codegen_expr llvm_ctxt builder func_ctxt expr in

      func_ctxt

  | ResolveStmt (expr) ->
      let expr_val = codegen_expr llvm_ctxt builder func_ctxt expr in
      let resolve_alloca = StrMap.find resolve_alloca_name func_ctxt.cur_vars in
      let _ : Llvm.llvalue = Llvm.build_store expr_val resolve_alloca builder in

      func_ctxt


and codegen_expr llvm_ctxt builder func_ctxt expr =
  let i64_t = Llvm.i64_type llvm_ctxt in
  let i32_t = Llvm.i32_type llvm_ctxt in
  let i16_t = Llvm.i16_type llvm_ctxt in
  let i8_t  = Llvm.i8_type  llvm_ctxt in

  let f128_t = Llvm.fp128_type  llvm_ctxt in
  let f64_t  = Llvm.double_type llvm_ctxt in
  let f32_t  = Llvm.float_type  llvm_ctxt in

  let bool_t = Llvm.i1_type llvm_ctxt in

  let _codegen_expr = codegen_expr llvm_ctxt builder func_ctxt in

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
      let alloca = StrMap.find ident func_ctxt.cur_vars in
      let loaded : Llvm.llvalue = Llvm.build_load alloca ident builder in
      loaded
  | ValCastTrunc(target_t, exp) ->
    begin
      let llvm_t = berk_t_to_llvm_t llvm_ctxt target_t in
      let exp_val = _codegen_expr exp in
      Llvm.build_trunc exp_val llvm_t "trunctmp" builder
    end
  | ValCastBitwise(target_t, exp) ->
    begin
      let llvm_t = berk_t_to_llvm_t llvm_ctxt target_t in
      let exp_val = _codegen_expr exp in
      Llvm.build_bitcast exp_val llvm_t "bitcasttmp" builder
    end
  | BinOp(_, op, lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      let lhs_t = expr_type lhs in
      let rhs_t = expr_type rhs in
      let comm_t = common_type_of_lr lhs_t rhs_t in
      let llvm_t = berk_t_to_llvm_t llvm_ctxt comm_t in
      begin match comm_t with
      | Bool ->
          begin match op with
          | Eq ->
              Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val "bicmptmp" builder
          | NotEq ->
              Llvm.build_icmp Llvm.Icmp.Ne lhs_val rhs_val "bicmptmp" builder

          | _ -> failwith "Non-equality binop not supported for bool"
          end
      | U64 | U32 | U16 | U8 ->
          let lhs_comm = Llvm.build_intcast lhs_val llvm_t "ucasttmp" builder in
          let rhs_comm = Llvm.build_intcast rhs_val llvm_t "ucasttmp" builder in
          begin match op with
          | Add -> Llvm.build_add lhs_comm rhs_comm "uaddtmp" builder
          | Sub -> Llvm.build_sub lhs_comm rhs_comm "usubtmp" builder
          | Mul -> Llvm.build_mul lhs_comm rhs_comm "umultmp" builder
          | Div -> Llvm.build_udiv lhs_comm rhs_comm "udivtmp" builder
          | Mod -> Llvm.build_urem lhs_comm rhs_comm "uremtmp" builder
          | Eq ->
              Llvm.build_icmp Llvm.Icmp.Eq lhs_comm rhs_comm "uicmptmp" builder
          | NotEq ->
              Llvm.build_icmp Llvm.Icmp.Ne lhs_comm rhs_comm "uicmptmp" builder
          | Less ->
              Llvm.build_icmp Llvm.Icmp.Ult lhs_comm rhs_comm "uicmptmp" builder
          | LessEq ->
              Llvm.build_icmp Llvm.Icmp.Ule lhs_comm rhs_comm "uicmptmp" builder
          | Greater ->
              Llvm.build_icmp Llvm.Icmp.Ugt lhs_comm rhs_comm "uicmptmp" builder
          | GreaterEq ->
              Llvm.build_icmp Llvm.Icmp.Uge lhs_comm rhs_comm "uicmptmp" builder
          end
      | I64 | I32 | I16 | I8 ->
          let signed_cast init_t init_llvm_val = begin
            (* comm_t must be the largest common type *)
            if init_t = comm_t
              then init_llvm_val
              else Llvm.build_sext init_llvm_val llvm_t "isexttmp" builder
          end in
          let lhs_comm = signed_cast lhs_t lhs_val in
          let rhs_comm = signed_cast rhs_t rhs_val in
          begin match op with
          | Add -> Llvm.build_add lhs_comm rhs_comm "iaddtmp" builder
          | Sub -> Llvm.build_sub lhs_comm rhs_comm "isubtmp" builder
          | Mul -> Llvm.build_mul lhs_comm rhs_comm "imultmp" builder
          | Div -> Llvm.build_sdiv lhs_comm rhs_comm "idivtmp" builder
          | Mod -> Llvm.build_srem lhs_comm rhs_comm "sremtmp" builder
          | Eq ->
              Llvm.build_icmp Llvm.Icmp.Eq lhs_comm rhs_comm "iicmptmp" builder
          | NotEq ->
              Llvm.build_icmp Llvm.Icmp.Ne lhs_comm rhs_comm "iicmptmp" builder
          | Less ->
              Llvm.build_icmp Llvm.Icmp.Slt lhs_comm rhs_comm "iicmptmp" builder
          | LessEq ->
              Llvm.build_icmp Llvm.Icmp.Sle lhs_comm rhs_comm "iicmptmp" builder
          | Greater ->
              Llvm.build_icmp Llvm.Icmp.Sgt lhs_comm rhs_comm "iicmptmp" builder
          | GreaterEq ->
              Llvm.build_icmp Llvm.Icmp.Sge lhs_comm rhs_comm "iicmptmp" builder
          end
      | F128 | F64 | F32 ->
          let lhs_comm = Llvm.build_fpcast lhs_val llvm_t "fcasttmp" builder in
          let rhs_comm = Llvm.build_fpcast rhs_val llvm_t "fcasttmp" builder in
          begin match op with
          | Add -> Llvm.build_fadd lhs_comm rhs_comm "faddtmp" builder
          | Sub -> Llvm.build_fsub lhs_comm rhs_comm "fsubtmp" builder
          | Mul -> Llvm.build_fmul lhs_comm rhs_comm "fmultmp" builder
          | Div -> Llvm.build_fdiv lhs_comm rhs_comm "fdivtmp" builder
          | Mod -> Llvm.build_frem lhs_comm rhs_comm "fremtmp" builder
          | Eq ->
              Llvm.build_fcmp Llvm.Fcmp.Ueq lhs_comm rhs_comm "fcmptmp" builder
          | NotEq ->
              Llvm.build_fcmp Llvm.Fcmp.Une lhs_comm rhs_comm "fcmptmp" builder
          | Less ->
              Llvm.build_fcmp Llvm.Fcmp.Ult lhs_comm rhs_comm "fcmptmp" builder
          | LessEq ->
              Llvm.build_fcmp Llvm.Fcmp.Ule lhs_comm rhs_comm "fcmptmp" builder
          | Greater ->
              Llvm.build_fcmp Llvm.Fcmp.Ugt lhs_comm rhs_comm "fcmptmp" builder
          | GreaterEq ->
              Llvm.build_fcmp Llvm.Fcmp.Uge lhs_comm rhs_comm "fcmptmp" builder
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
      let cur_vars = func_ctxt.cur_vars in
      let updated_vars = StrMap.add resolve_alloca_name alloca cur_vars in
      let func_ctxt_up = {func_ctxt with cur_vars = updated_vars} in

      let _ = codegen_stmts llvm_ctxt builder func_ctxt_up stmts in

      let loaded = Llvm.build_load alloca resolve_alloca_name builder in

      loaded

  | IfThenElseExpr(typ, cond_expr, then_expr, else_expr) ->
      let bb_then = Llvm.append_block llvm_ctxt "if_then" func_ctxt.cur_func in
      let bb_else = Llvm.append_block llvm_ctxt "if_else" func_ctxt.cur_func in
      let bb_if_end = Llvm.append_block llvm_ctxt "if_end" func_ctxt.cur_func in

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

    | FuncCall(_, ident, exprs) ->
        let llvm_func_val = StrMap.find ident func_ctxt.mod_ctxt.func_sigs in
        let llvm_args = Array.of_list (List.map _codegen_expr exprs) in

        Llvm.build_call llvm_func_val llvm_args "calltmp" builder

    | ArrayExpr(typ, exprs) ->
        let llvm_expr_vals = List.map _codegen_expr exprs in
        let llvm_ptr_t = berk_t_to_llvm_t llvm_ctxt typ in
        let llvm_arr_t = Llvm.element_type llvm_ptr_t in
        let alloca = Llvm.build_alloca llvm_arr_t "arraytmp" builder in
        let _ = List.iteri (
          fun idx expr_val ->
            let indices = Array.of_list [
              Llvm.const_int i32_t 0;
              Llvm.const_int i32_t idx;
            ] in
            let llvm_gep = Llvm.build_gep alloca indices "geptmp" builder in
            let _ = Llvm.build_store expr_val llvm_gep builder in
            ()
        ) llvm_expr_vals in

        alloca

    | IndexExpr(_, _, idx_expr, arr_expr) ->
        let idx_val = _codegen_expr idx_expr in
        let arr_val = _codegen_expr arr_expr in
        (* TODO: Add bounds check logic when relevant *)
        let indices = Array.of_list [
          Llvm.const_int i32_t 0;
          idx_val;
        ] in
        let llvm_gep = Llvm.build_gep arr_val indices "geptmp" builder in
        let loaded = Llvm.build_load llvm_gep "loadarraytmp" builder in

        loaded

    | TupleExpr(typ, exprs) ->
        let llvm_expr_vals = List.map _codegen_expr exprs in
        let llvm_ptr_t = berk_t_to_llvm_t llvm_ctxt typ in
        let llvm_tuple_t = Llvm.element_type llvm_ptr_t in
        let alloca = Llvm.build_alloca llvm_tuple_t "tupletmp" builder in
        let _ = List.iteri (
          fun idx expr_val ->
            let indices = Array.of_list [
              Llvm.const_int i32_t 0;
              Llvm.const_int i32_t idx;
            ] in
            let llvm_gep = Llvm.build_gep alloca indices "geptmp" builder in
            let _ = Llvm.build_store expr_val llvm_gep builder in
            ()
        ) llvm_expr_vals in

        alloca


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
