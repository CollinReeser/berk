open Ir
open Mir
open Rast

module StrMap = Map.Make(String)

type module_gen_context = {
  func_sigs: Llvm.llvalue StrMap.t;
  llvm_mod: Llvm.llmodule;
  data_layout_mod: Llvm_target.DataLayout.t;
  rast_t_to_llvm_t: rast_t -> Llvm.lltype;
  llvm_sizeof: Llvm.lltype -> int;
  (* Whether to validate generated LLVM IR for static correctness. *)
  validate: bool;
  (* Whether to apply optimizations on generated LLVM IR. *)
  optimize: bool;
}

type func_gen_context = {
  cur_func: Llvm.llvalue;
  cur_vars: Llvm.llvalue StrMap.t;
  bbs: Llvm.llbasicblock StrMap.t;
  mod_ctxt: module_gen_context
}

(* Assert that, where applicable, LLVM agreed to use exactly the name given to
it by the generated MIR for each LLVM value. LLVM producing a non-matching name
(likely appended with some digits) implies LLVM had to uniquify the value
because it was already used, which further implies the MIR is not fully
uniquified itself. *)
let enforce_mir_llvm_name_agreement mir_name llvm_val =
  let llvm_name = Llvm.value_name llvm_val in

  if mir_name = "" then
    failwith (
      Printf.sprintf
        "MIR lval names must be non-empty strings! LLVM: [%s]"
        llvm_name
    )

  else if llvm_name = "" then
    (* LLVM will constant-fold on the fly, which can yield unnamed values. We
    simply accept this. *)
    llvm_val

  else if mir_name <> llvm_name then
    failwith (
      Printf.sprintf
        "MIR lval name [%s] was not unique; LLVM forced to uniquify with [%s]"
        mir_name llvm_name
    )

  else
    llvm_val
;;

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
      let llvm_nil_typ = func_ctxt.mod_ctxt.rast_t_to_llvm_t Nil in
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
      let unescaped_str = Scanf.unescaped str in
      let llvm_str = Llvm.const_stringz llvm_ctxt unescaped_str in
      let global_str =
        Llvm.define_global
          "str" llvm_str func_ctxt.mod_ctxt.llvm_mod
      in
      (* These strings are immutable, and their address is insignificant, ie, we
      care only about their content, not their location.

      Note: Not only do we not want to change these later in the semantics of
      the language, but if they're marked as being const and having unnamed
      addresses in LLVM, then optimizations on globals can collapse duplicates
      into a single global value. *)

      (* FIXME: _Something_ is preventing const, unnamed_addr, identical global
      strings from being merged, despite module-level global const de-dup
      optimization being enabled. *)
      let _ = Llvm.set_global_constant true global_str in
      let _ = Llvm.set_unnamed_addr true global_str in

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

  | ValFunc(func_name) ->
      try StrMap.find func_name func_ctxt.mod_ctxt.func_sigs
      with Not_found ->
        failwith (
          Printf.sprintf "No func named [%s] for ValFunc codegen" func_name
        )

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

let codegen_call ?(result_name="") func_ctxt builder {lname=func_name; _} args =
  (* Note that this may either be a "direct" function, ie a direct call to
  a function signature, or it may be a call against a _pointer to_ a function.
  LLVM automatically unwraps function pointers, so we don't need to do any
  extra work here. Note that codegen for functions stored in variables turns
  into an alloca for a _pointer to a function pointer_, ie, a **func, so when
  we load a value out of that variable alloca, we get a function _pointer_
  and not a direct function signature (which, again, LLVM knows how to invoke).
  *)
  let llvm_func_val = StrMap.find func_name func_ctxt.cur_vars in

  let llvm_args =
    List.map (
      fun {lname=arg_name; _} -> StrMap.find arg_name func_ctxt.cur_vars
    ) args
  in
  let llvm_args = Array.of_list llvm_args in

  (* Generate the function call. If this function returns non-nil, we expect
  result_name to be a non-empty string, and we expect that result_name to be
  unique, such that LLVM does not need to further uniquify it. This is important
  as a sanity check against the MIR being well-formed, ie, the MIR must also
  have fully unique names everywhere, just like LLVM. *)
  let call_result =
    Llvm.build_call llvm_func_val llvm_args result_name builder |>
    if result_name = "" then
      Fun.id
    else
      enforce_mir_llvm_name_agreement result_name
  in

  (* Hint that this should be a tailcall if possible. *)
  let _ = Llvm.set_tail_call true call_result in

  (func_ctxt, call_result)
;;

let codegen_bb_instr llvm_ctxt builder func_ctxt instr =
  begin match instr with
  | GetArg({lname; _}, i) ->
      let value = Llvm.param func_ctxt.cur_func i in

      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname value func_ctxt.cur_vars
      } in

      func_ctxt

  | Alloca({lname; _}, t) ->
      let alloca_t = func_ctxt.mod_ctxt.rast_t_to_llvm_t t in

      let alloca =
        Llvm.build_alloca alloca_t lname builder |>
        enforce_mir_llvm_name_agreement lname
      in

      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname alloca func_ctxt.cur_vars
      } in

      func_ctxt

  | Store({lname=name_ptrto; _}, {lname=name_value; _}) ->
      let (ptrto, value) = try
        (
          StrMap.find name_ptrto func_ctxt.cur_vars,
          StrMap.find name_value func_ctxt.cur_vars
        )
      with Not_found ->
        failwith (
          Printf.sprintf "Could not find store ptrto/value via [%s] [%s]"
            name_ptrto name_value
        )
      in

      let _ : Llvm.llvalue = Llvm.build_store value ptrto builder in

      func_ctxt

  | Load({lname=name_value; _}, {lname=name_alloca; _}) ->
      let alloca = try
        StrMap.find name_alloca func_ctxt.cur_vars
      with Not_found ->
        failwith (
          Printf.sprintf "Could not find load alloca via %s" name_alloca
        )
      in

      let value =
        Llvm.build_load alloca name_value builder |>
        enforce_mir_llvm_name_agreement name_value
      in

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

  | ConstructAggregate({lname; t; _}, elems) ->
      let llvm_aggregate_t = func_ctxt.mod_ctxt.rast_t_to_llvm_t t in
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

  | IntoAggregate(
      {lname=new_agg_name; _}, idx, {lname=orig_agg_name; _},
      {lname=elem_name; _}
    ) ->
      let elem_val = StrMap.find elem_name func_ctxt.cur_vars in
      let orig_agg_val = StrMap.find orig_agg_name func_ctxt.cur_vars in

      let new_agg_val =
        Llvm.build_insertvalue orig_agg_val elem_val idx new_agg_name builder |>
        enforce_mir_llvm_name_agreement new_agg_name
      in

      let func_ctxt = {
        func_ctxt with
          cur_vars = StrMap.add new_agg_name new_agg_val func_ctxt.cur_vars
      } in

      func_ctxt

  | FromAggregate({lname; _}, elem_idx, {lname=agg_name; _}) ->
      let agg_value = StrMap.find agg_name func_ctxt.cur_vars in

      let elem_val =
        Llvm.build_extractvalue agg_value elem_idx lname builder |>
        enforce_mir_llvm_name_agreement lname
      in

      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname elem_val func_ctxt.cur_vars
      } in

      func_ctxt

  | PtrTo({lname; _}, indices, {lname=agg_name; _}) ->
      let index_to_llvm idx = begin match idx with
        | Static(i) ->
            ValU32(i) |> codegen_constant llvm_ctxt func_ctxt builder
        | Dynamic({lname; _}) ->
            StrMap.find lname func_ctxt.cur_vars
      end in

      let llvm_indices = Array.of_list (List.map index_to_llvm indices) in
      let agg_value = StrMap.find agg_name func_ctxt.cur_vars in

      let llvm_gep =
        Llvm.build_gep agg_value llvm_indices lname builder |>
        enforce_mir_llvm_name_agreement lname
      in

      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname llvm_gep func_ctxt.cur_vars
      } in

      func_ctxt

  | Call({lname; _}, func_lval, args) ->
      (* By passing in a ~result_name, we're saying this is a non-void call that
      will return an LLVM value. *)
      let (func_ctxt, call_value) =
        codegen_call ~result_name:lname func_ctxt builder func_lval args
      in

      (* Only when calls are non-void do they return a value that we might need
      later. *)
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname call_value func_ctxt.cur_vars
      } in

      func_ctxt

  | CallVoid(func_lval, args) ->
      let (func_ctxt, _) = codegen_call func_ctxt builder func_lval args in

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

  | Cast({lname; t; _}, op, {lname=rhs_name; _}) ->
      let llvm_t = func_ctxt.mod_ctxt.rast_t_to_llvm_t t in
      let op_val = StrMap.find rhs_name func_ctxt.cur_vars in

      let trunc_val =
        begin match op with
        | Truncate -> Llvm.build_trunc op_val llvm_t lname builder
        | Bitwise -> Llvm.build_bitcast op_val llvm_t lname builder
        | Extend ->
            begin match t with
            | U8 | U16 | U32 | U64 ->
              Llvm.build_zext op_val llvm_t lname builder
            | I8 | I16 | I32 | I64 ->
              Llvm.build_sext op_val llvm_t lname builder
            | F32 | F64 | F128 ->
              Llvm.build_fpext op_val llvm_t lname builder
            | _ -> failwith "Cannot extend non-numeric type"
            end
        end
        |> enforce_mir_llvm_name_agreement lname
      in
      let func_ctxt = {
        func_ctxt with cur_vars = StrMap.add lname trunc_val func_ctxt.cur_vars
      } in

      func_ctxt

  | UnOp({lname=out_name; _}, op, {lname=in_name; _}) ->
      let in_llvm_val = StrMap.find in_name func_ctxt.cur_vars in

      let out_llvm_val =
        begin match op with
        | LNot -> Llvm.build_not in_llvm_val out_name builder
        end
        |> enforce_mir_llvm_name_agreement out_name
      in
      let func_ctxt = {
        func_ctxt with
          cur_vars = StrMap.add out_name out_llvm_val func_ctxt.cur_vars
      } in

      func_ctxt

  | BinOp(
      {lname; t; _},
      op, {lname=lhs_name; t=lhs_t; _}, {lname=rhs_name; t=rhs_t; _}
    ) ->
      let lhs_val =
        begin match StrMap.find_opt lhs_name func_ctxt.cur_vars with
        | Some(lhs_val) -> lhs_val
        | None ->
            failwith (
              Printf.sprintf "Could not find bin-op lhs val %s" lhs_name
            )
        end
      in
      let rhs_val =
        begin match StrMap.find_opt rhs_name func_ctxt.cur_vars with
        | Some(rhs_val) -> rhs_val
        | None ->
            failwith (
              Printf.sprintf "Could not find bin-op rhs val %s" rhs_name
            )
        end
      in

      let bin_op_val = begin match (lhs_t, rhs_t) with
      | ((U8 | U16 | U32 | U64), (U8 | U16 | U32 | U64)) ->
        begin match op with
        | Add -> Llvm.build_add lhs_val rhs_val lname builder
        | Sub -> Llvm.build_sub lhs_val rhs_val lname builder
        | Mul -> Llvm.build_mul lhs_val rhs_val lname builder
        | Div -> Llvm.build_udiv lhs_val rhs_val lname builder
        | Mod -> Llvm.build_urem lhs_val rhs_val lname builder
        | Eq -> Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val lname builder
        | Ne -> Llvm.build_icmp Llvm.Icmp.Ne lhs_val rhs_val lname builder
        | Lt -> Llvm.build_icmp Llvm.Icmp.Ult lhs_val rhs_val lname builder
        | Le -> Llvm.build_icmp Llvm.Icmp.Ule lhs_val rhs_val lname builder
        | Gt -> Llvm.build_icmp Llvm.Icmp.Ugt lhs_val rhs_val lname builder
        | Ge -> Llvm.build_icmp Llvm.Icmp.Uge lhs_val rhs_val lname builder
        | LOr | LAnd -> failwith "Operation not supported for types."
        end

      | ((I8 | I16 | I32 | I64), (I8 | I16 | I32 | I64)) ->
        begin match op with
        | Add -> Llvm.build_add lhs_val rhs_val lname builder
        | Sub -> Llvm.build_sub lhs_val rhs_val lname builder
        | Mul -> Llvm.build_mul lhs_val rhs_val lname builder
        | Div -> Llvm.build_sdiv lhs_val rhs_val lname builder
        | Mod -> Llvm.build_srem lhs_val rhs_val lname builder
        | Eq -> Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val lname builder
        | Ne -> Llvm.build_icmp Llvm.Icmp.Ne lhs_val rhs_val lname builder
        | Lt -> Llvm.build_icmp Llvm.Icmp.Slt lhs_val rhs_val lname builder
        | Le -> Llvm.build_icmp Llvm.Icmp.Sle lhs_val rhs_val lname builder
        | Gt -> Llvm.build_icmp Llvm.Icmp.Sgt lhs_val rhs_val lname builder
        | Ge -> Llvm.build_icmp Llvm.Icmp.Sge lhs_val rhs_val lname builder
        | LOr | LAnd -> failwith "Operation not supported for types."
        end

      | ((F128 | F64 | F32), (F128 | F64 | F32)) ->
        begin match op with
        | Add -> Llvm.build_fadd lhs_val rhs_val lname builder
        | Sub -> Llvm.build_fsub lhs_val rhs_val lname builder
        | Mul -> Llvm.build_fmul lhs_val rhs_val lname builder
        | Div -> Llvm.build_fdiv lhs_val rhs_val lname builder
        | Mod -> Llvm.build_frem lhs_val rhs_val lname builder
        | Eq -> Llvm.build_fcmp Llvm.Fcmp.Ueq lhs_val rhs_val lname builder
        | Ne -> Llvm.build_fcmp Llvm.Fcmp.Une lhs_val rhs_val lname builder
        | Lt -> Llvm.build_fcmp Llvm.Fcmp.Ult lhs_val rhs_val lname builder
        | Le -> Llvm.build_fcmp Llvm.Fcmp.Ule lhs_val rhs_val lname builder
        | Gt -> Llvm.build_fcmp Llvm.Fcmp.Ugt lhs_val rhs_val lname builder
        | Ge -> Llvm.build_fcmp Llvm.Fcmp.Uge lhs_val rhs_val lname builder
        | LOr | LAnd -> failwith "Operation not supported for types."
        end


      | (Bool, Bool) ->
        begin match op with
        | Eq -> Llvm.build_icmp Llvm.Icmp.Eq lhs_val rhs_val lname builder
        | Ne -> Llvm.build_icmp Llvm.Icmp.Ne lhs_val rhs_val lname builder
        | LOr | LAnd -> Llvm.build_or lhs_val rhs_val lname builder
        | _ -> failwith "Non-equality binop not supported for bool"
        end

      | (_, _) ->
        failwith (
          Printf.sprintf
            "Unexpected expression type in BinOp: [%s]: [%s] op [%s]"
            (fmt_rtype t)
            (fmt_rtype lhs_t)
            (fmt_rtype rhs_t)
        )
      end
        |> enforce_mir_llvm_name_agreement lname
      in

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
  let bbs_control_flow_order = control_flow_list mir_ctxt in

  let (llvm_bbs_map, _) =
    List.fold_left_map (
      fun map_so_far ({name=bb_name; _} : bb) ->
        let llvm_bb = Llvm.append_block llvm_ctxt bb_name func_ctxt.cur_func in
        (StrMap.add bb_name llvm_bb map_so_far, ())
    ) StrMap.empty bbs_control_flow_order
  in

  let func_ctxt = {func_ctxt with bbs = llvm_bbs_map} in

  let (func_ctxt, _) =
    List.fold_left_map (
      fun func_ctxt bb ->
        let func_ctxt =
          codegen_func_bb llvm_ctxt builder func_ctxt bb
        in
        (func_ctxt, ())
    ) func_ctxt bbs_control_flow_order
  in

  func_ctxt
;;


let codegen_func_decl_mir mod_ctxt {f_name; f_params; f_ret_rt; _} =
  (* Return the pair of all the non-variadic function parameter types, and
  whether the parameter list ends with a variadic-args sentinel. Fails if
  ill-formed. *)
  (* TODO: This is a modified copy of what is in ast.ml, and we need to marry
  these two. *)
  let rec get_static_f_params f_params =
    begin match f_params with
    | [] -> ([], false)
    | [(_, VarArgSentinel)] -> ([], true)
    | (_, VarArgSentinel)::_ ->
        failwith "Variadic arguments may exist only once, at end of param list"
    | (_, x)::xs ->
        let (rest, is_vararg) = get_static_f_params xs in
        (x::rest, is_vararg)
    end
  in

  (* Generate the LLVM context for defining a new function. *)
  let llvm_ret_t = mod_ctxt.rast_t_to_llvm_t f_ret_rt in
  let (f_params_non_variadic, is_var_arg) = get_static_f_params f_params in
  let llvm_param_t_lst =
    List.map (mod_ctxt.rast_t_to_llvm_t) f_params_non_variadic
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


let codegen_func_mir
  llvm_ctxt the_fpm builder mod_ctxt (mir_ctxt : mir_ctxt)
=
  let (mod_ctxt, new_func) = codegen_func_decl_mir mod_ctxt mir_ctxt in

  (* Establish our function-specific codegen context given the above setup. *)
  let func_ctxt = {
    cur_func = new_func;
    cur_vars = StrMap.empty;
    mod_ctxt = mod_ctxt;
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

  let _ = begin
    if mod_ctxt.optimize then
      (* Optimize the function. *)
      let did_fpm_do = Llvm.PassManager.run_function new_func the_fpm in
      Printf.printf "Did the FPM do function-level opts on [%s]? [%B]\n"
        mir_ctxt.f_name did_fpm_do ;
      ()
    else
      ()
  end in

  mod_ctxt
;;

let codegen_func_mirs
  llvm_ctxt the_fpm the_mpm builder
  (mod_gen_ctxt : module_gen_context)
  (mir_ctxts : mir_ctxt list)
=
  let _ =
    List.fold_left (
      fun mod_gen_ctxt mir_ctxt ->
        let ({bbs; _} : mir_ctxt) = mir_ctxt in
        if StrMap.is_empty bbs then
          let (mod_gen_ctxt, _) =
            codegen_func_decl_mir mod_gen_ctxt mir_ctxt
          in
          mod_gen_ctxt
        else
          let mod_gen_ctxt =
            codegen_func_mir llvm_ctxt the_fpm builder mod_gen_ctxt mir_ctxt
          in
          mod_gen_ctxt
    ) mod_gen_ctxt mir_ctxts
  in

  let _ = begin
    if mod_gen_ctxt.validate then
      let _ = Llvm_analysis.assert_valid_module mod_gen_ctxt.llvm_mod in
      ()
    else
      ()
  end in

  let _ = begin
    if mod_gen_ctxt.optimize then
      let did_mpm_do =
        Llvm.PassManager.run_module mod_gen_ctxt.llvm_mod the_mpm
      in
      Printf.printf "Did the MPM do module-level opts? [%B]\n" did_mpm_do ;

      (* Re-apply function optimizations on all functions. Once module-level
      optimizations are performed, certain function-level optimizations can go
      further (eg, module-level opts can annotate functions with read-only
      attributes, allowing function-level opts to merge multiple calls to these
      "pure" functions). *)

      Llvm.iter_functions (
        fun f -> Llvm.PassManager.run_function f the_fpm |> ignore
      ) mod_gen_ctxt.llvm_mod ;

      ()
    else
      ()
  end in

  ()
