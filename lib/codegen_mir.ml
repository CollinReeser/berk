open Ir
open Llvm_utility
open Mir
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
  bbs: Llvm.llbasicblock StrMap.t;
  mod_ctxt: module_gen_context
}

let codegen_constant
  llvm_ctxt func_ctxt builder constant : Llvm.llvalue
=
  let i64_t = Llvm.i64_type llvm_ctxt in
  let i32_t = Llvm.i32_type llvm_ctxt in
  let i16_t = Llvm.i16_type llvm_ctxt in
  let i8_t  = Llvm.i8_type  llvm_ctxt in
  let f128_t = Llvm.fp128_type  llvm_ctxt in
  let f64_t  = Llvm.double_type llvm_ctxt in
  let f32_t  = Llvm.float_type  llvm_ctxt in
  let bool_t = Llvm.i1_type llvm_ctxt in

  begin match constant with
  | ValNil ->
      let llvm_nil_typ = func_ctxt.mod_ctxt.berk_t_to_llvm_t Nil in
      Llvm.undef llvm_nil_typ

  | ValU64(n) | ValI64(n) -> Llvm.const_int i64_t n
  | ValU32(n) | ValI32(n) -> Llvm.const_int i32_t n
  | ValU16(n) | ValI16(n) -> Llvm.const_int i16_t n
  | ValU8(n)  | ValI8(n)  -> Llvm.const_int  i8_t n

  | ValF64(n) -> Llvm.const_float f64_t n
  | ValF32(n) -> Llvm.const_float f32_t n

  | ValF128(str) -> Llvm.const_float_of_string f128_t str

  | ValBool(false) -> Llvm.const_int bool_t 0
  | ValBool(true)  -> Llvm.const_int bool_t 1

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
  end
;;

let codegen_aggregate builder t vals =
  let rec _codegen_aggregate vals cur_val idx =
    begin match vals with
    | [] -> cur_val
    | x::xs ->
        let next_val = (
          Llvm.build_insertvalue cur_val x idx "tupletmp" builder
        ) in
        let next_idx = idx + 1 in
        _codegen_aggregate xs next_val next_idx
    end
  in
  let undef_aggregate = Llvm.undef t in
  _codegen_aggregate vals undef_aggregate 0
;;

let codegen_bb_instr llvm_ctxt builder func_ctxt instr =
  begin match instr with
  | Alloca({lname; _}, t) ->
      let alloca_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t t in
      let alloca = Llvm.build_alloca alloca_t lname builder in
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname alloca func_ctxt.cur_vars
      } in

      func_ctxt
  | Store({lname=name_alloca; _}, {lname=name_value; _}) ->
      let alloca = StrMap.find name_alloca func_ctxt.cur_vars in
      let value = StrMap.find name_value func_ctxt.cur_vars in
      let _ : Llvm.llvalue = Llvm.build_store value alloca builder in

      func_ctxt

  | Load({lname=name_value; _}, {lname=name_alloca; _}) ->
      let alloca = StrMap.find name_alloca func_ctxt.cur_vars in
      let value = Llvm.build_load alloca name_alloca builder in
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add name_value value func_ctxt.cur_vars
      } in

      func_ctxt

  | Assign({lname; _}, RVar({lname=name_value; _})) ->
      (* Essentially, just alias the declared name to the existing value. *)
      let value = StrMap.find name_value func_ctxt.cur_vars in
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname value func_ctxt.cur_vars
      } in

      func_ctxt

  | Assign({lname; _}, Constant(constant)) ->
      let value = codegen_constant llvm_ctxt func_ctxt builder constant in
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname value func_ctxt.cur_vars
      } in

      func_ctxt

  | IntoAggregate({lname; t; _}, elems) ->
      let llvm_aggregate_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t t in
      let llvm_elems =
        List.map (
          fun {lname=elem_name; _} -> StrMap.find elem_name func_ctxt.cur_vars
        ) elems
      in

      let aggr_val = codegen_aggregate builder llvm_aggregate_t llvm_elems in
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname aggr_val func_ctxt.cur_vars
      } in

      func_ctxt

  | FromAggregate({lname; _}, elem_idx, {lname=name_aggregate; _}) ->
      let agg_value = StrMap.find name_aggregate func_ctxt.cur_vars in
      let elem_val =
        Llvm.build_extractvalue agg_value elem_idx "decontmp" builder
      in

      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname elem_val func_ctxt.cur_vars
      } in

      func_ctxt

  | RetVoid ->
      let _ = Llvm.build_ret_void builder in

      func_ctxt

  | Ret({lname; _}) ->
      let value = StrMap.find lname func_ctxt.cur_vars in
      let _ = Llvm.build_ret value builder in

      func_ctxt

  | Br({name=target_bb_name; _}) ->
      let llvm_target_bb = StrMap.find target_bb_name func_ctxt.bbs in
      let _ = Llvm.build_br llvm_target_bb builder in

      func_ctxt

  | CondBr({lname; _}, {name=if_bb_name; _}, {name=else_bb_name; _}) ->
      let if_bb = StrMap.find if_bb_name func_ctxt.bbs in
      let else_bb = StrMap.find else_bb_name func_ctxt.bbs in

      let cond_value = StrMap.find lname func_ctxt.cur_vars in

      let _ = Llvm.build_cond_br cond_value if_bb else_bb builder in

      func_ctxt

  | UnOp({lname; t; _}, op, {lname=rhs_name; _}) ->
      let llvm_t = func_ctxt.mod_ctxt.berk_t_to_llvm_t t in
      let op_val = StrMap.find rhs_name func_ctxt.cur_vars in

      let trunc_val = begin match op with
        | Truncate -> Llvm.build_trunc op_val llvm_t "trunctmp" builder
        | Bitwise -> Llvm.build_bitcast op_val llvm_t "bitcasttmp" builder
        | Extend ->
            begin match t with
            | U8 | U16 | U32 | U64 ->
              Llvm.build_zext op_val llvm_t "zexttmp" builder
            | I8 | I16 | I32 | I64 ->
              Llvm.build_sext op_val llvm_t "sexttmp" builder
            | F32 | F64 | F128 ->
              Llvm.build_fpext op_val llvm_t "fpexttmp" builder
            | _ -> failwith "Cannot extend non-numeric type"
            end
      end in
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname trunc_val func_ctxt.cur_vars
      } in

      func_ctxt

  | BinOp({lname; t; _}, op, {lname=lhs_name; _}, {lname=rhs_name; _}) ->
      let lhs_val = StrMap.find lhs_name func_ctxt.cur_vars in
      let rhs_val = StrMap.find rhs_name func_ctxt.cur_vars in

      let bin_op_val = begin match t with
      | Bool ->
        begin match op with
        | Eq -> Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val "bicmptmp" builder
        | Ne -> Llvm.build_icmp Llvm.Icmp.Ne lhs_val rhs_val "bicmptmp" builder
        | _ -> failwith "Non-equality binop not supported for bool"
        end

      | U8 | U16 | U32 | U64 ->
        begin match op with
        | Add -> Llvm.build_add lhs_val rhs_val "uaddtmp" builder
        | Sub -> Llvm.build_sub lhs_val rhs_val "usubtmp" builder
        | Mul -> Llvm.build_mul lhs_val rhs_val "umultmp" builder
        | Div -> Llvm.build_udiv lhs_val rhs_val "udivtmp" builder
        | Mod -> Llvm.build_urem lhs_val rhs_val "uremtmp" builder
        | Eq -> Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val "bicmptmp" builder
        | Ne -> Llvm.build_icmp Llvm.Icmp.Ne lhs_val rhs_val "bicmptmp" builder
        | Lt -> Llvm.build_icmp Llvm.Icmp.Ult lhs_val rhs_val "uicmptmp" builder
        | Le -> Llvm.build_icmp Llvm.Icmp.Ule lhs_val rhs_val "uicmptmp" builder
        | Gt -> Llvm.build_icmp Llvm.Icmp.Ugt lhs_val rhs_val "uicmptmp" builder
        | Ge -> Llvm.build_icmp Llvm.Icmp.Uge lhs_val rhs_val "uicmptmp" builder
        end

      | I8 | I16 | I32 | I64 ->
        begin match op with
        | Add -> Llvm.build_add lhs_val rhs_val "iaddtmp" builder
        | Sub -> Llvm.build_sub lhs_val rhs_val "isubtmp" builder
        | Mul -> Llvm.build_mul lhs_val rhs_val "imultmp" builder
        | Div -> Llvm.build_sdiv lhs_val rhs_val "idivtmp" builder
        | Mod -> Llvm.build_srem lhs_val rhs_val "sremtmp" builder
        | Eq -> Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val "iicmptmp" builder
        | Ne -> Llvm.build_icmp Llvm.Icmp.Ne lhs_val rhs_val "iicmptmp" builder
        | Lt -> Llvm.build_icmp Llvm.Icmp.Slt lhs_val rhs_val "iicmptmp" builder
        | Le -> Llvm.build_icmp Llvm.Icmp.Sle lhs_val rhs_val "iicmptmp" builder
        | Gt -> Llvm.build_icmp Llvm.Icmp.Sgt lhs_val rhs_val "iicmptmp" builder
        | Ge -> Llvm.build_icmp Llvm.Icmp.Sge lhs_val rhs_val "iicmptmp" builder
        end

      | F128 | F64 | F32 ->
        begin match op with
        | Add -> Llvm.build_fadd lhs_val rhs_val "faddtmp" builder
        | Sub -> Llvm.build_fsub lhs_val rhs_val "fsubtmp" builder
        | Mul -> Llvm.build_fmul lhs_val rhs_val "fmultmp" builder
        | Div -> Llvm.build_fdiv lhs_val rhs_val "fdivtmp" builder
        | Mod -> Llvm.build_frem lhs_val rhs_val "fremtmp" builder
        | Eq -> Llvm.build_fcmp Llvm.Fcmp.Ueq lhs_val rhs_val "fcmptmp" builder
        | Ne -> Llvm.build_fcmp Llvm.Fcmp.Une lhs_val rhs_val "fcmptmp" builder
        | Lt -> Llvm.build_fcmp Llvm.Fcmp.Ult lhs_val rhs_val "fcmptmp" builder
        | Le -> Llvm.build_fcmp Llvm.Fcmp.Ule lhs_val rhs_val "fcmptmp" builder
        | Gt -> Llvm.build_fcmp Llvm.Fcmp.Ugt lhs_val rhs_val "fcmptmp" builder
        | Ge -> Llvm.build_fcmp Llvm.Fcmp.Uge lhs_val rhs_val "fcmptmp" builder
        end
      | typ ->
        failwith (
          Printf.sprintf
            "Unexpected expression type in BinOp: %s" (fmt_type typ)
        )
      end in

      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname bin_op_val func_ctxt.cur_vars
      } in

      func_ctxt

  end
;;

let codegen_bb_instrs llvm_ctxt builder func_ctxt instrs =
  let (func_ctxt, _) =
    List.fold_left_map (
      fun func_ctxt instr ->
        let func_ctxt = codegen_bb_instr llvm_ctxt builder func_ctxt instr in
        (func_ctxt, ())
    ) func_ctxt instrs
  in

  func_ctxt
;;

let codegen_func_bb llvm_ctxt builder func_ctxt ({name; instrs} : bb) =
  let bb = StrMap.find name func_ctxt.bbs in
  let _ = Llvm.position_at_end bb builder in

  codegen_bb_instrs llvm_ctxt builder func_ctxt instrs
;;

let codegen_func_bbs llvm_ctxt builder func_ctxt (mir_ctxt : mir_ctxt) =
  let bbs = StrMap.bindings mir_ctxt.bbs in
  let entry_bb = List.find (fun (k, _) -> k = "entry") bbs in
  let ordered_bbs : (string * bb) list = begin
    let others = List.filter (fun (k, _) -> k <> "entry") bbs in
    entry_bb :: others
  end in

  let (llvm_bbs_map, _) =
    List.fold_left_map (
      fun map_so_far (k, _) ->
        let llvm_bb = Llvm.append_block llvm_ctxt k func_ctxt.cur_func in
        (StrMap.add k llvm_bb map_so_far, ())
    ) StrMap.empty ordered_bbs
  in

  let func_ctxt = {func_ctxt with bbs = llvm_bbs_map} in

  let (func_ctxt, _) =
    List.fold_left_map (
      fun func_ctxt (_, bb) ->
        let func_ctxt =
          codegen_func_bb llvm_ctxt builder func_ctxt bb
        in
        (func_ctxt, ())
    ) func_ctxt ordered_bbs
  in

  func_ctxt
;;

let codegen_func_mir
  llvm_ctxt the_fpm builder mod_ctxt
  ({f_name; f_params; f_ret_t; _} as mir_ctxt : mir_ctxt)
=
  (* Generate the LLVM context for defining a new function. *)
  let llvm_ret_t = mod_ctxt.berk_t_to_llvm_t f_ret_t in
  let llvm_param_t_lst =
    List.map (
      fun (_, t) -> mod_ctxt.berk_t_to_llvm_t t
    ) f_params
  in
  let llvm_param_t_arr = Array.of_list llvm_param_t_lst in
  let func_sig_t =
    if false (* is_var_arg *)
    then Llvm.var_arg_function_type llvm_ret_t llvm_param_t_arr
    else Llvm.function_type llvm_ret_t llvm_param_t_arr
  in
  let new_func = Llvm.declare_function f_name func_sig_t mod_ctxt.llvm_mod in

  (* Add this new function to our codegen context; doing this now, rather than
  at the _end_ of function codegen, is what permits self recursion. *)
  let func_sigs_up = StrMap.add f_name new_func mod_ctxt.func_sigs in
  let mod_ctxt_up = {mod_ctxt with func_sigs = func_sigs_up} in


  (* ??? *)


  let init_vars = if List.length f_params > 0 then
    (* Push the function arguments into allocas so that they are easier to
    reference as variables within the function body. *)
    let llvm_params = Array.to_list (Llvm.params new_func) in
    let arg_to_param_lst = List.combine f_params llvm_params in
    let llvm_param_allocas = List.map (
      fun ((id, typ), llvm_param) ->
        let alloca_typ = mod_ctxt.berk_t_to_llvm_t typ in
        let alloca = Llvm.build_alloca alloca_typ id builder in
        let _ : Llvm.llvalue = Llvm.build_store llvm_param alloca builder in

        alloca
    ) arg_to_param_lst in
    let arg_to_alloca_lst = List.combine f_params llvm_param_allocas in
    let init_vars = List.fold_left (
      fun vars ((id, _), param) -> StrMap.add id param vars
    ) StrMap.empty arg_to_alloca_lst
    in
    init_vars
  else
    StrMap.empty
  in

  (* Establish our function-specific codegen context given the above setup. *)
  let func_ctxt = {
    cur_func = new_func;
    cur_vars = init_vars;
    mod_ctxt = mod_ctxt_up;
    bbs = StrMap.empty;
  } in

  (* Codegen the function body statements. *)
  let _ = codegen_func_bbs llvm_ctxt builder func_ctxt mir_ctxt in

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
;;

let codegen_func_mirs llvm_mod llvm_ctxt the_fpm builder mir_ctxts =
  let data_layout_str = Llvm.data_layout llvm_mod in
  let data_layout_mod = Llvm_target.DataLayout.of_string data_layout_str in

  let llvm_sizeof typ =
    let llvm_sizeof_int64 =
      Llvm_target.DataLayout.store_size typ data_layout_mod
    in
    Int64.to_int llvm_sizeof_int64
  in

  let mod_ctxt = {
    func_sigs = StrMap.empty;
    llvm_mod = llvm_mod;
    data_layout_mod = data_layout_mod;
    berk_t_to_llvm_t = berk_t_to_llvm_t llvm_sizeof llvm_ctxt;
    llvm_sizeof = llvm_sizeof;
  } in

  (* TODO: This will need to change when we're generating multiple functions. *)

  let _ =
    List.map (codegen_func_mir llvm_ctxt the_fpm builder mod_ctxt) mir_ctxts
  in

  ()
