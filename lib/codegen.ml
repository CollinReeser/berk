open Ast
open Llvm_utility
open Typing

module StrMap = Map.Make(String)

type module_gen_context = {
  func_sigs: Llvm.llvalue StrMap.t;
  llvm_mod: Llvm.llmodule;
  data_layout_mod: Llvm_target.DataLayout.t;
  berk_t_to_llvm_t: berk_t -> Llvm.lltype;
  llvm_sizeof: Llvm.lltype -> int;
}

type func_gen_context = {
  cur_func: Llvm.llvalue;
  cur_vars: Llvm.llvalue StrMap.t;
  mod_ctxt: module_gen_context
}

(* Given an initial offset from a universally-aligned address, and a type,
return the resolved integer index from that universal initial address that the
type wants to be aligned to. *)
let get_aligned_offset_from mod_ctxt init_offset llvm_typ =
  let preferred_alignment =
    Llvm_target.DataLayout.stack_align llvm_typ mod_ctxt.data_layout_mod
  in

  (* The target offset is the first offset at or after the initial offset that
    is aligned to the target alignment.

    Ex: init_offset = 13, preferred_alignment = 8, target_offset = 16:
    -> 13 mod 8 = 5
    ->  8  -  5 = 3
    -> 13  +  3 = 16

    Ex: init_offset = 1, preferred_alignment = 4, target_offset = 4:
    -> 1 mod 4 = 1
    -> 4  -  1 = 3
    -> 1  +  3 = 4
  *)
  let init_offset_align_overrun = init_offset mod preferred_alignment in
  let alignment_padding = preferred_alignment - init_offset_align_overrun in
  let target_offset = init_offset + alignment_padding in

  target_offset
;;


let if_expr_alloc_name = "___IF_THEN_ELSE_ALLOCA"
let while_expr_alloc_name = "___WHILE_FINALLY_ALLOCA"
;;


(* Return the instructions of the given basic block in reverse order
(last -> first). *)
let get_rev_instruction_list bb =
  let init_pos = Llvm.instr_end bb in
  let rec _get_rev_instruction_list cur_pos =
    begin match cur_pos with
      | Llvm.At_start (_) -> []
      | Llvm.After (inst) ->
        let next_pos = Llvm.instr_pred inst in
        inst::(_get_rev_instruction_list next_pos)
    end
  in
  _get_rev_instruction_list init_pos
;;

(* Removes any instructions after a terminator in the given basic block. *)
let remove_dead_instructions bb =
  let instr_list = get_rev_instruction_list bb in
  let rec _remove_dead_instructions instr_head instr_tail =
    begin match instr_tail with
      | [] -> ()
      | x::xs ->
        let instr_head_up =
          begin
            if Llvm.is_terminator x
            then
              begin
                List.iter (Llvm.delete_instruction) instr_head ;
                [x]
              end
            else
              x::instr_head
          end
        in
        _remove_dead_instructions instr_head_up xs
    end
  in
  _remove_dead_instructions [] instr_list
;;


(*
Various cleanup operations on the basic blocks that were generated but result
in invalid IR.

TODO: Add a pass that removes unreachable basic blocks.
*)
let clean_up_basic_blocks_of_function llvm_func =
  let _ = Llvm.iter_blocks remove_dead_instructions llvm_func in
  ()
;;


let build_aggregate builder typ vals =
  let rec _build_aggregate vals cur_val idx =
    begin match vals with
    | [] -> cur_val
    | x::xs ->
        let next_val = (
          Llvm.build_insertvalue cur_val x idx "tupletmp" builder
        ) in
        let next_idx = idx + 1 in
        _build_aggregate xs next_val next_idx
    end
  in
  let undef_aggregate = Llvm.undef typ in
  _build_aggregate vals undef_aggregate 0
;;


let deconstruct_aggregate builder idents agg =
  let rec _deconstruct_aggregate idents idx decon_lst =
    begin match idents with
    | [] -> decon_lst
    | _::xs ->
        let next_val = Llvm.build_extractvalue agg idx "decontmp" builder in
        let next_idx = idx + 1 in
        let next_decon = decon_lst @ [next_val] in
        _deconstruct_aggregate xs next_idx next_decon
    end
  in
  _deconstruct_aggregate idents 0 []
;;


let deconstruct_aggregate_sz builder sz agg =
  let rec _deconstruct_aggregate_sz idx decon_lst =
    if idx < sz
    then
      begin
        let next_val = Llvm.build_extractvalue agg idx "decontmp" builder in
        let next_idx = idx + 1 in
        let next_decon = decon_lst @ [next_val] in
        _deconstruct_aggregate_sz next_idx next_decon
      end
    else
      decon_lst
  in
  _deconstruct_aggregate_sz 0 []
;;


let rec combine3 lhs mid rhs =
  match (lhs, mid, rhs) with
  | ([], [], []) -> []
  | (x::xs, y::ys, z::zs) -> (x, y, z) :: combine3 xs ys zs
  | _ -> failwith "combine3 expects three equal-length lists"
;;


let rec codegen_mod_decls llvm_ctxt the_mod the_fpm builder mod_decls =
  let data_layout_str = Llvm.data_layout the_mod in
  let data_layout_mod = Llvm_target.DataLayout.of_string data_layout_str in

  let llvm_sizeof typ =
    let llvm_sizeof_int64 =
      Llvm_target.DataLayout.store_size typ data_layout_mod
    in
    Int64.to_int llvm_sizeof_int64
  in

  let mod_ctxt = {
    func_sigs = StrMap.empty;
    llvm_mod = the_mod;
    data_layout_mod = data_layout_mod;
    berk_t_to_llvm_t = berk_t_to_llvm_t llvm_sizeof llvm_ctxt;
    llvm_sizeof = llvm_sizeof;
  } in
  let _codegen_mod_decl =
    fun ctxt decl ->
      codegen_mod_decl llvm_ctxt the_fpm builder ctxt decl
  in
  let _ = List.fold_left _codegen_mod_decl mod_ctxt mod_decls in
  ()


and codegen_mod_decl llvm_ctxt the_fpm builder mod_ctxt mod_decl =
  match mod_decl with
  | FuncExternDecl(f_decl_ast) ->
      let (mod_ctxt, _) = codegen_func_decl mod_ctxt f_decl_ast in
      mod_ctxt

  | FuncDef(f_ast) ->
      codegen_func llvm_ctxt the_fpm builder mod_ctxt f_ast

  | VariantDecl(_) ->
      (* There is nothing to do for explicit codegen for variant decls. *)
      mod_ctxt


and codegen_func_decl mod_ctxt {f_name; f_params; f_ret_t} =
  (* Generate the LLVM context for defining a new function. *)
  let llvm_ret_t = mod_ctxt.berk_t_to_llvm_t f_ret_t in
  let (f_params_non_variadic, is_var_arg) = get_static_f_params f_params in
  let llvm_param_t_lst =
    List.map (mod_ctxt.berk_t_to_llvm_t) f_params_non_variadic
  in
  let llvm_param_t_arr = Array.of_list llvm_param_t_lst in
  let func_sig_t =
    if is_var_arg
    then Llvm.var_arg_function_type llvm_ret_t llvm_param_t_arr
    else Llvm.function_type llvm_ret_t llvm_param_t_arr
  in
  let new_func = Llvm.declare_function f_name func_sig_t mod_ctxt.llvm_mod in

  (* Add this new function to our codegen context; doing this now, rather than
  at the _end_ of function codegen, is what permits self recursion. *)
  let func_sigs = StrMap.add f_name new_func mod_ctxt.func_sigs in
  let mod_ctxt = {mod_ctxt with func_sigs = func_sigs} in

  (mod_ctxt, new_func)


and codegen_func
  llvm_ctxt the_fpm builder mod_ctxt
  {f_decl = {f_params; _} as f_decl; f_stmts;}
=
  let (mod_ctxt, new_func) = codegen_func_decl mod_ctxt f_decl in

  let bb = Llvm.append_block llvm_ctxt "entry" new_func in
  let _ = Llvm.position_at_end bb builder in

  (* Push the function arguments into allocas so that they are easier to
  reference as variables within the function body. *)
  let llvm_params = Array.to_list (Llvm.params new_func) in
  let arg_to_param_lst = List.combine f_params llvm_params in
  let llvm_param_allocas = List.map (
    fun ((id, _, typ), llvm_param) ->
      let alloca_typ = mod_ctxt.berk_t_to_llvm_t typ in
      let alloca = Llvm.build_alloca alloca_typ id builder in
      let _ : Llvm.llvalue = Llvm.build_store llvm_param alloca builder in

      alloca
  ) arg_to_param_lst in
  let arg_to_alloca_lst = List.combine f_params llvm_param_allocas in
  let init_vars = List.fold_left (
    fun vars ((id, _, _), param) -> StrMap.add id param vars
  ) StrMap.empty arg_to_alloca_lst
  in

  (* Establish our function-specific codegen context given the above setup. *)
  let func_ctxt = {
    cur_func = new_func;
    cur_vars = init_vars;
    mod_ctxt = mod_ctxt
  } in

  (* Codegen the function body statements. *)
  codegen_stmts llvm_ctxt builder func_ctxt f_stmts |> ignore ;

  (* TODO: Do better here. Sometimes, generated code ends with an empty basic
  block. Basic blocks must have at least a terminator, so we add a "nonsense"
  one here. *)
  let _ = Llvm.build_unreachable builder in

  (* Various cleanup of codegen. eg, some codegen flows can generate basic
  blocks with multiple terminators, which is invalid LLVM IR. *)
  clean_up_basic_blocks_of_function new_func ;

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

  mod_ctxt


and codegen_stmts llvm_ctxt builder func_ctxt stmts =
  match stmts with
  | [] -> func_ctxt
  | x::xs ->
      let func_ctxt_updated = codegen_stmt llvm_ctxt builder func_ctxt x in
      codegen_stmts llvm_ctxt builder func_ctxt_updated xs


and codegen_stmt llvm_ctxt builder func_ctxt stmt : func_gen_context =
  match stmt with
  | DeclStmt (ident, _, typ, expr) ->
      let expr_val = codegen_expr llvm_ctxt builder func_ctxt expr in
      let alloca_typ = func_ctxt.mod_ctxt.berk_t_to_llvm_t typ in
      let alloca = Llvm.build_alloca alloca_typ ident builder in
      let _ : Llvm.llvalue = Llvm.build_store expr_val alloca builder in

      let updated_vars = StrMap.add ident alloca func_ctxt.cur_vars in
      let func_ctxt_up = {func_ctxt with cur_vars = updated_vars} in

      func_ctxt_up

  | DeclDeconStmt (idents_quals, typ, expr) ->
      let agg_expr = codegen_expr llvm_ctxt builder func_ctxt expr in
      let types = match typ with
        | Array(typ, sz) -> List.init sz (fun _ -> typ)
        | Tuple(types) -> types
        | _ -> failwith "Cannot gen destructuring for non-aggregate type"
      in

      let idents = List.map (fun (id, _) -> id) idents_quals in
      let decon_exprs = deconstruct_aggregate builder idents agg_expr in
      let types_idents_exprs = combine3 types idents decon_exprs in

      let updated_vars = List.fold_left (
        fun vars (typ, ident, exp) ->
          let alloca_typ = func_ctxt.mod_ctxt.berk_t_to_llvm_t typ in
          let alloca = Llvm.build_alloca alloca_typ ident builder in
          let _ : Llvm.llvalue = Llvm.build_store exp alloca builder in

          StrMap.add ident alloca vars
      ) func_ctxt.cur_vars types_idents_exprs in

      {func_ctxt with cur_vars = updated_vars}

  | AssignStmt (ident, expr) ->
      let alloca = StrMap.find ident func_ctxt.cur_vars in
      let expr_val = codegen_expr llvm_ctxt builder func_ctxt expr in
      let _ : Llvm.llvalue = Llvm.build_store expr_val alloca builder in

      func_ctxt

  | AssignDeconStmt (idents, expr) ->
      let agg_expr = codegen_expr llvm_ctxt builder func_ctxt expr in
      let decon_exprs = deconstruct_aggregate builder idents agg_expr in

      let _ = List.iter2 (
        fun ident exp ->
          let var_alloca = StrMap.find ident func_ctxt.cur_vars in
          let _ : Llvm.llvalue = Llvm.build_store exp var_alloca builder in

          ()
      ) idents decon_exprs in

      func_ctxt

  | ReturnStmt(expr) ->
      let return_val = codegen_expr llvm_ctxt builder func_ctxt expr in
      let _ = begin match (expr_type expr) with
        | Nil -> Llvm.build_ret_void builder
        | _   -> Llvm.build_ret return_val builder
      end in

      func_ctxt

  | ExprStmt (expr) ->
      let _ = codegen_expr llvm_ctxt builder func_ctxt expr in

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
  | ValNil ->
      let llvm_nil_typ = func_ctxt.mod_ctxt.berk_t_to_llvm_t Nil in
      Llvm.undef llvm_nil_typ

  | ValU64(n) | ValI64(n) -> Llvm.const_int i64_t n
  | ValU32(n) | ValI32(n) -> Llvm.const_int i32_t n
  | ValU16(n) | ValI16(n) -> Llvm.const_int i16_t n
  | ValU8(n)  | ValI8(n)  -> Llvm.const_int  i8_t n

  | ValInt(U8, n)  | ValInt(I8, n)  -> Llvm.const_int i8_t n
  | ValInt(U16, n) | ValInt(I16, n) -> Llvm.const_int i16_t n
  | ValInt(U32, n) | ValInt(I32, n) -> Llvm.const_int i32_t n
  | ValInt(U64, n) | ValInt(I64, n) -> Llvm.const_int i64_t n

  | ValInt(t, n) ->
      failwith (
        Printf.sprintf
          "Cannot codegen int [%d] with nonsense type [%s]" n (fmt_type t)
      )

  | ValBool(false) -> Llvm.const_int bool_t 0
  | ValBool(true)  -> Llvm.const_int bool_t 1
  | ValF128(str) -> Llvm.const_float_of_string f128_t str
  | ValF64(n)  -> Llvm.const_float f64_t  n
  | ValF32(n)  -> Llvm.const_float f32_t  n
  | ValStr(str) ->
      let llvm_str = Llvm.const_stringz llvm_ctxt str in
      let global_str =
        Llvm.define_global "str" llvm_str func_ctxt.mod_ctxt.llvm_mod
      in
      let indices = Array.of_list [
        Llvm.const_int i32_t 0;
        Llvm.const_int i32_t 0;
      ] in
      (* We don't want the pointer to the statically sized array, but rather a
      more "raw" pointer to the first element, as the LLVM-side type of our
      string values is a "raw" pointer to some bytes (as opposed to a pointer
      to a structure or statically-sized array). *)
      let llvm_gep = Llvm.build_gep global_str indices "strgeptmp" builder in
      llvm_gep

  | ValVar(_, ident) ->
      let alloca = StrMap.find ident func_ctxt.cur_vars in
      let loaded : Llvm.llvalue = Llvm.build_load alloca ident builder in
      loaded

  | ValFunc(_, _) -> failwith "Unimplemented"

  | ValCastTrunc(target_t, exp) ->
    begin
      let llvm_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t target_t in
      let exp_val = _codegen_expr exp in
      Llvm.build_trunc exp_val llvm_t "trunctmp" builder
    end
  | ValCastBitwise(target_t, exp) ->
    begin
      let llvm_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t target_t in
      let exp_val = _codegen_expr exp in
      Llvm.build_bitcast exp_val llvm_t "bitcasttmp" builder
    end
  | ValCastExtend(target_t, exp) ->
    begin
      let llvm_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t target_t in
      let exp_val = _codegen_expr exp in
      begin match target_t with
      | U8 | U16 | U32 | U64 ->
          Llvm.build_zext exp_val llvm_t "extendtmp" builder
      | I8 | I16 | I32 | I64 ->
          Llvm.build_sext exp_val llvm_t "extendtmp" builder
      | F32 | F64 | F128 ->
          Llvm.build_fpext exp_val llvm_t "extendtmp" builder
      | _ -> failwith "Cannot extend non-numeric types"
      end
    end
  | BinOp(_, op, lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      let lhs_t = expr_type lhs in
      let rhs_t = expr_type rhs in
      let comm_t = common_type_of_lr lhs_t rhs_t in
      let llvm_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t comm_t in
      begin match comm_t with
      | Bool ->
          begin match op with
          | Eq ->
              Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val "bicmptmp" builder
          | Ne ->
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
          | Ne ->
              Llvm.build_icmp Llvm.Icmp.Ne lhs_comm rhs_comm "uicmptmp" builder
          | Lt ->
              Llvm.build_icmp Llvm.Icmp.Ult lhs_comm rhs_comm "uicmptmp" builder
          | Le ->
              Llvm.build_icmp Llvm.Icmp.Ule lhs_comm rhs_comm "uicmptmp" builder
          | Gt ->
              Llvm.build_icmp Llvm.Icmp.Ugt lhs_comm rhs_comm "uicmptmp" builder
          | Ge ->
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
          | Ne ->
              Llvm.build_icmp Llvm.Icmp.Ne lhs_comm rhs_comm "iicmptmp" builder
          | Lt ->
              Llvm.build_icmp Llvm.Icmp.Slt lhs_comm rhs_comm "iicmptmp" builder
          | Le ->
              Llvm.build_icmp Llvm.Icmp.Sle lhs_comm rhs_comm "iicmptmp" builder
          | Gt ->
              Llvm.build_icmp Llvm.Icmp.Sgt lhs_comm rhs_comm "iicmptmp" builder
          | Ge ->
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
          | Ne ->
              Llvm.build_fcmp Llvm.Fcmp.Une lhs_comm rhs_comm "fcmptmp" builder
          | Lt ->
              Llvm.build_fcmp Llvm.Fcmp.Ult lhs_comm rhs_comm "fcmptmp" builder
          | Le ->
              Llvm.build_fcmp Llvm.Fcmp.Ule lhs_comm rhs_comm "fcmptmp" builder
          | Gt ->
              Llvm.build_fcmp Llvm.Fcmp.Ugt lhs_comm rhs_comm "fcmptmp" builder
          | Ge ->
              Llvm.build_fcmp Llvm.Fcmp.Uge lhs_comm rhs_comm "fcmptmp" builder
          end
      | typ ->
        failwith (
          Printf.sprintf
            "Unexpected expression type in BinOp: %s" (fmt_type typ)
        )
      end
  | BlockExpr(_, stmts, exp) ->
      let func_ctxt_up = codegen_stmts llvm_ctxt builder func_ctxt stmts in
      let block_expr_val = codegen_expr llvm_ctxt builder func_ctxt_up exp in

      block_expr_val

  | IfThenElseExpr(typ, cond_expr, then_expr, else_expr) ->
      (* Generate the core if-then-else logic, conditionally storing the
      resultant then/else branch values into the if-expr alloca. *)
      let core_if_then_else_gen maybe_do_store = begin
        let cond_val = _codegen_expr cond_expr in

        let cur_func = func_ctxt.cur_func in
        let bb_then = Llvm.append_block llvm_ctxt "if_then" cur_func in
        let bb_else = Llvm.append_block llvm_ctxt "if_else" cur_func in
        let bb_if_end = Llvm.append_block llvm_ctxt "if_end" cur_func in

        let _ = Llvm.build_cond_br cond_val bb_then bb_else builder in

        let _ = Llvm.position_at_end bb_then builder in
        let then_val = _codegen_expr then_expr in
        let _ = maybe_do_store then_val in
        let _ = Llvm.build_br bb_if_end builder in

        let _ = Llvm.position_at_end bb_else builder in
        let else_val = _codegen_expr else_expr in
        let _ = maybe_do_store else_val in
        let _ = Llvm.build_br bb_if_end builder in

        let _ = Llvm.position_at_end bb_if_end builder in

        ()
      end in

      (* If this if-expr yields a non-nil value, we want to ensure we yield that
      value. Otherwise, if this if-expr is ultimately nil, we want to avoid
      attempting to store an undef value into any alloca. *)
      let resolved_val = begin match typ with
        | Nil ->
            let no_store _ = () in

            let () = core_if_then_else_gen no_store in
            let nil_val = _codegen_expr ValNil in

            nil_val

        | _ ->
            let alloca_typ = func_ctxt.mod_ctxt.berk_t_to_llvm_t typ in
            let alloca =
              Llvm.build_alloca alloca_typ if_expr_alloc_name builder
            in

            let do_store llvm_val = begin
              let _ : Llvm.llvalue = Llvm.build_store llvm_val alloca builder in
              ()
            end in

            let _ = core_if_then_else_gen do_store in
            let loaded = Llvm.build_load alloca if_expr_alloc_name builder in

            loaded
      end in

      resolved_val

  | WhileExpr(_, cond_expr, then_stmts) ->
      let cur_func = func_ctxt.cur_func in
      let bb_cond = Llvm.append_block llvm_ctxt "while_cond" cur_func in
      let bb_then = Llvm.append_block llvm_ctxt "while_then" cur_func in
      let bb_end = Llvm.append_block llvm_ctxt "while_end" cur_func in

      let _ = Llvm.build_br bb_cond builder in

      let _ = Llvm.position_at_end bb_cond builder in
      let cond_val = _codegen_expr cond_expr in
      let _ = Llvm.build_cond_br cond_val bb_then bb_end builder in

      let _ = Llvm.position_at_end bb_then builder in
      let _ = codegen_stmts llvm_ctxt builder func_ctxt then_stmts in
      let _ = Llvm.build_br bb_cond builder in

      let _ = Llvm.position_at_end bb_end builder in

      let nil_val = _codegen_expr ValNil in
      nil_val

  | FuncCall(typ, ident, exprs) ->
      let llvm_func_val = StrMap.find ident func_ctxt.mod_ctxt.func_sigs in
      let llvm_args = Array.of_list (List.map _codegen_expr exprs) in

      (* Calls to void functions must not "assign" to a named result. *)
      let res_name = begin match typ with
        | Nil -> ""
        | _ -> "calltmp"
      end in

      let call = Llvm.build_call llvm_func_val llvm_args res_name builder in
      Llvm.set_tail_call true call ;

      call

  | VarInvoke(_, _, _) -> failwith "Unimplemented"

  | ArrayExpr(typ, exprs) ->
      let llvm_expr_vals = List.map _codegen_expr exprs in
      let llvm_arr_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t typ in

      let arr_aggregate = (
        build_aggregate builder llvm_arr_t llvm_expr_vals
      ) in

      arr_aggregate

  | IndexExpr(_, idx_expr, arr_expr) ->
      let arr_typ = expr_type arr_expr in
      let (arr_typ, arr_sz) = begin match arr_typ with
        | Array(typ, sz) -> (typ, sz)
        | _ ->
          begin
            let pretty_typ = fmt_type arr_typ in
            let err_msg = (
              Printf.sprintf
                "Indexing into other than static array: %s"
                pretty_typ
            ) in
            failwith err_msg
          end
      end in

      let idx_val = _codegen_expr idx_expr in

      (* TODO: Add an out-of-bounds check based in the index val and the
      static size of the array. *)

      let arr_val = _codegen_expr arr_expr in

      (* Store the static array into an alloca so we can dynamically index
      into it. *)

      let deconstructed_lst = (
        deconstruct_aggregate_sz builder arr_sz arr_val
      ) in

      let llvm_alloca_typ = func_ctxt.mod_ctxt.berk_t_to_llvm_t arr_typ in
      let llvm_arr_sz = Llvm.const_int i32_t arr_sz in

      let alloca_arr = (
        Llvm.build_array_alloca
          llvm_alloca_typ llvm_arr_sz "allocaarrtmp" builder
      ) in

      let _ = List.iteri (
        fun idx elem_val ->
          let indices = Array.of_list [
            Llvm.const_int i32_t idx;
          ] in
          let llvm_gep = Llvm.build_gep alloca_arr indices "geptmp" builder in
          let _ = Llvm.build_store elem_val llvm_gep builder in
          ()
      ) deconstructed_lst in

      (* Load from the alloca our specific dynamic index. *)

      let indices = Array.of_list [idx_val] in
      let idx_gep = Llvm.build_gep alloca_arr indices "geptmp" builder in
      let loaded = Llvm.build_load idx_gep "loadarraytmp" builder in

      loaded

  | StaticIndexExpr(_, idx, arr_expr) ->
      let arr_typ = expr_type arr_expr in
      let arr_sz = begin match arr_typ with
        | Array(_, sz) -> sz
        | _ ->
          begin
            let pretty_typ = fmt_type arr_typ in
            let err_msg = (
              Printf.sprintf
                "Indexing into other than static array: %s"
                pretty_typ
            ) in
            failwith err_msg
          end
      end in

      let _ = begin
        if idx >= 0 && idx < arr_sz
        then ()
        else failwith (Printf.sprintf "idx %d OoB for %d" idx arr_sz)
      end in

      let llvm_arr_val = _codegen_expr arr_expr in

      let extracted = (
        Llvm.build_extractvalue llvm_arr_val idx "idxtmp" builder
      ) in

      extracted

  | TupleExpr(typ, exprs) ->
      let llvm_expr_vals = List.map _codegen_expr exprs in
      let llvm_tuple_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t typ in

      let tuple_aggregate = (
        build_aggregate builder llvm_tuple_t llvm_expr_vals
      ) in

      tuple_aggregate

  | VariantCtorExpr(variant_t, ctor_name, exp) ->
      (* See also:
        https://mapping-high-level-constructs-to-llvm-ir.readthedocs.io/en/latest/basic-constructs/unions.html
      *)

      (* Sanity check we're working with a variant, and extract some info while
      we're at it. *)
      let (v_name, v_ctors) = begin match variant_t with
      | Variant(v_name, v_ctors) -> (v_name, v_ctors)
      | _ -> failwith "Unexpected non-variant type in variant-ctor-expr"
      end in

      (* Convert the berk variant to an LLVM struct type. *)
      let llvm_variant_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t variant_t in

      let variant_ssa_alloca_name = "variant_" ^ v_name ^ "_allocatmp" in
      let variant_ssa_gep_name = "variant_" ^ v_name ^ "_geptmp" in
      let variant_ssa_load_name = "variant_" ^ v_name ^ "_loadtmp" in
      let ctor_ssa_gep_name = "variant_ctor_" ^ ctor_name ^ "_geptmp" in
      let ctor_ssa_bitcast_name = "variant_ctor_" ^ ctor_name ^ "_bitcasttmp" in

      let alloca =
        Llvm.build_alloca llvm_variant_t variant_ssa_alloca_name builder
      in

      (* Which "tag" is this variant constructor supposed to be? Find it, then
      assign it to the tag field in the LLVM variant struct. *)
      let ctor_tag_index = get_tag_index_by_variant_ctor v_ctors ctor_name in
      let llvm_ctor_tag_index = Llvm.const_int i8_t ctor_tag_index in

      let indices = Array.of_list [
        Llvm.const_int i32_t 0;
        Llvm.const_int i32_t 0;
      ] in
      let llvm_gep =
        Llvm.build_gep alloca indices ctor_ssa_gep_name builder
      in
      let _ = Llvm.build_store llvm_ctor_tag_index llvm_gep builder in

      (* Determine an "alias" type for this particular variant constructor, so
      we can bitcast our toplevel variant to this constructor type and
      manipulate the constructor fields. *)
      let get_ctor_llvm_type llvm_ctor_expr_t =
        let llvm_ctor_tag = Llvm.i8_type llvm_ctxt in
        let llvm_t_arr = Array.of_list [llvm_ctor_tag; llvm_ctor_expr_t] in
        let llvm_ctor_t = Llvm.struct_type llvm_ctxt llvm_t_arr in

        llvm_ctor_t
      in

      (* Only if this constructor actually has non-nil data do we generate code
      for that expression and store that result into the LLVM variant struct. *)
      let expr_t = expr_type exp in
      let _ = begin match expr_t with
        | Nil -> ()
        | _ ->
          begin
            let llvm_expr_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t expr_t in
            let llvm_ctor_t = get_ctor_llvm_type llvm_expr_t in
            let llvm_ctor_t_ptr = Llvm.pointer_type llvm_ctor_t in

            let llvm_expr_val = _codegen_expr exp in

            (* We'll need to treat the LLVM variant struct as though it were
            instead of the constructor type, so we can manipulate fields. *)
            let bitcast_alloca =
              Llvm.build_bitcast
                alloca
                llvm_ctor_t_ptr
                ctor_ssa_bitcast_name
                builder
            in

            (* Since the arbitrarily-complex constructor expression is still
            just "one type", its offset is simply index 1, right after the
            variant constructor tag that we assigned above. *)
            let indices = Array.of_list [
              Llvm.const_int i32_t 0;
              Llvm.const_int i32_t 1;
            ] in

            let llvm_gep =
              Llvm.build_gep bitcast_alloca indices ctor_ssa_gep_name builder
            in
            let _ = Llvm.build_store llvm_expr_val llvm_gep builder in

            ()
          end
      end in

      (* The actual type of this variant constructor is "direct data", not a
      pointer, so we need to load the totality of the variant.*)
      let indices = Array.of_list [
        Llvm.const_int i32_t 0;
      ] in
      let variant_gep =
        Llvm.build_gep alloca indices variant_ssa_gep_name builder
      in
      let loaded = Llvm.build_load variant_gep variant_ssa_load_name builder in

      loaded

  | MatchExpr(_, _, _) -> failwith "Unimplemented"
;;

