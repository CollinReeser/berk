open Typing

let berk_t_to_llvm_t llvm_sizeof llvm_ctxt =
  let rec _berk_t_to_llvm_t typ =
    begin match typ with
    | Nil -> Llvm.void_type llvm_ctxt

    | Ptr(pointed_t) -> Llvm.pointer_type (_berk_t_to_llvm_t pointed_t)

    | U64 | I64 -> Llvm.i64_type llvm_ctxt
    | U32 | I32 -> Llvm.i32_type llvm_ctxt
    | U16 | I16 -> Llvm.i16_type llvm_ctxt
    | U8  | I8  -> Llvm.i8_type  llvm_ctxt

    | F128 -> Llvm.fp128_type  llvm_ctxt
    | F64  -> Llvm.double_type llvm_ctxt
    | F32  -> Llvm.float_type  llvm_ctxt

    | Bool -> Llvm.i1_type llvm_ctxt

    | String ->
        let llvm_char_t = Llvm.i8_type llvm_ctxt in
        let llvm_str_t = Llvm.pointer_type llvm_char_t in
        llvm_str_t

    | Array(elem_typ, sz) ->
        let llvm_elem_t = _berk_t_to_llvm_t elem_typ in
        let llvm_arr_t = Llvm.array_type llvm_elem_t sz in
        llvm_arr_t

    | Tuple(types) ->
        let llvm_t_lst = List.map (_berk_t_to_llvm_t) types in
        let llvm_t_arr = Array.of_list llvm_t_lst in
        let llvm_tuple_t = Llvm.struct_type llvm_ctxt llvm_t_arr in
        llvm_tuple_t

    | Variant(_, ctors) ->
        let llvm_nonempty_typs = List.filter_map (
          fun (_, typ) ->
            match typ with
            | Nil -> None
            | _ -> Some(_berk_t_to_llvm_t typ)
        ) ctors in

        let typ_sizes = List.map llvm_sizeof llvm_nonempty_typs in

        let largest = List.fold_left max 0 typ_sizes in
        let llvm_variant_t = begin
          if largest = 0
          then
            let llvm_union_tag = Llvm.i8_type llvm_ctxt in
            let llvm_t_arr = Array.of_list [llvm_union_tag] in
            let llvm_union_t = Llvm.struct_type llvm_ctxt llvm_t_arr in

            llvm_union_t
          else
            let llvm_union_tag = Llvm.i8_type llvm_ctxt in
            let llvm_union_dummy = Llvm.i8_type llvm_ctxt in
            let llvm_union_vals = Llvm.array_type llvm_union_dummy largest in
            let llvm_t_arr = Array.of_list [llvm_union_tag; llvm_union_vals] in
            let llvm_union_t = Llvm.struct_type llvm_ctxt llvm_t_arr in

            llvm_union_t
        end in

        llvm_variant_t

    | Function(ret_t, args_t_lst) ->
        let llvm_ret_t = _berk_t_to_llvm_t ret_t in

        let args_to_llvm args_t_lst =
          let rec _args_to_rev_llvm llvm_t_lst_so_far args_t_lst =
            begin match args_t_lst with
            | [] -> (llvm_t_lst_so_far, false)
            | [VarArgSentinel] -> (llvm_t_lst_so_far, true)
            | VarArgSentinel::_ ->
                failwith "VarArgSentinel must be alone and last."
            | x::xs ->
                let llvm_t = _berk_t_to_llvm_t x in

                _args_to_rev_llvm (llvm_t::llvm_t_lst_so_far) xs
          end in
          let (rev_llvm_t_lst, is_var_arg) = _args_to_rev_llvm [] args_t_lst in

          (List.rev rev_llvm_t_lst, is_var_arg)
        in

        let (llvm_args_t_lst, is_var_arg) = args_to_llvm args_t_lst in
        let llvm_args_t_arr = Array.of_list llvm_args_t_lst in

        begin if is_var_arg then
          Llvm.var_arg_function_type llvm_ret_t llvm_args_t_arr
        else
          Llvm.function_type llvm_ret_t llvm_args_t_arr
        end

    | VarArgSentinel -> failwith "Should not need to determine type for var arg"
    | Unbound(template) ->
        failwith (
          "Cannot determine llvm type for unbound type template " ^
          template
        )
    | Undecided -> failwith "Cannot determine llvm type for undecided type"
  end in

  _berk_t_to_llvm_t
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

  (* Do some optimizations again, as these have demonstrably reduced more
  code when ran again after the above. *)

  Llvm_scalar_opts.add_memory_to_register_promotion the_fpm ;
  Llvm_scalar_opts.add_instruction_combination the_fpm ;

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
