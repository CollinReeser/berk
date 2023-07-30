open Rast_typing

let rast_t_to_llvm_t llvm_sizeof llvm_ctxt =
  let rec _rast_t_to_llvm_t (typ : rast_t) : Llvm.lltype =
    begin match typ with
    | RNil -> Llvm.void_type llvm_ctxt

    | RU64 | RI64 -> Llvm.i64_type llvm_ctxt
    | RU32 | RI32 -> Llvm.i32_type llvm_ctxt
    | RU16 | RI16 -> Llvm.i16_type llvm_ctxt
    | RU8  | RI8  -> Llvm.i8_type  llvm_ctxt

    | RF128 -> Llvm.fp128_type  llvm_ctxt
    | RF64  -> Llvm.double_type llvm_ctxt
    | RF32  -> Llvm.float_type  llvm_ctxt

    | RBool -> Llvm.i1_type llvm_ctxt

    | RString ->
        let llvm_char_t = Llvm.i8_type llvm_ctxt in
        let llvm_str_t = Llvm.pointer_type llvm_char_t in
        llvm_str_t

    | RArray(elem_typ, sz) ->
        let llvm_elem_t = _rast_t_to_llvm_t elem_typ in
        let llvm_arr_t = Llvm.array_type llvm_elem_t sz in
        llvm_arr_t

    | RTuple(types) ->
        let llvm_t_lst = List.map (_rast_t_to_llvm_t) types in
        let llvm_t_arr = Array.of_list llvm_t_lst in

        (* TODO: Note the use of `packed_struct_type` here. This ensures there
        is no padding injected into the data layout for the underlying struct
        for this tuple. This also applies to the member fields of individual
        variant constructors. This is important particularly for variants so
        that we can freely bitcast between the "generic" raw bytes and the
        expected fields of the particular target variant constructor. Without
        this, we'd need to take alignment into account, which can differ between
        target architectures, and without packing nor taking alignment into
        account, we'll end up with miscompilation where pieces of the padding
        are being accessed as real data.

        But, packing the struct is not a cure-all: this can have performance
        penalties, as the CPU doesn't like having to deal with misaligned data.

        We should _at least_ only use packed structs for variants, as we don't
        need it for regular tuples. This implies creating a special kind of
        "tuple" type just for variants, which is probably cleaner anyway.

        Better, we teach the MIR codegen about alignment, so that we can avoid
        having to use packed/misaligned data, to avoid potential perf issues. *)
        let llvm_tuple_t = Llvm.packed_struct_type llvm_ctxt llvm_t_arr in

        llvm_tuple_t

    | RSuperTuple(tss) ->
        (* The size/layout of a supertuple is the size/layout of the largest
        superimposed tuple.

        TODO: This should take alignment into consideration. For now, it assumes
        a packed aggregate type. *)

        let tuples = List.map (fun ts -> RTuple(ts)) tss in
        let size_to_tuple =
          List.map (
            fun tuple ->
              let llvm_t = _rast_t_to_llvm_t tuple in
              let llvm_sz = llvm_sizeof llvm_t in
              (llvm_sz, tuple)
          ) tuples
        in

        let (_, largest_tuple) =
          List.fold_left (
            fun (max_sz_so_far, max_tup_so_far) (cur_sz, cur_tup) ->
              begin
                if max_sz_so_far < cur_sz then
                  (cur_sz, cur_tup)
                else
                  (max_sz_so_far, max_tup_so_far)
              end
          ) (0, RTuple([])) size_to_tuple
        in

        _rast_t_to_llvm_t largest_tuple

    | RRef(pointed_t)
    | RPtr(pointed_t) -> Llvm.pointer_type (_rast_t_to_llvm_t pointed_t)

    | RByteArray(actual_t) ->
        let llvm_actual_t = _rast_t_to_llvm_t actual_t in
        let sizeof = llvm_sizeof llvm_actual_t in
        let byte_array_t = RArray(RU8, sizeof) in
        _rast_t_to_llvm_t byte_array_t

    | RFunction(ret_t, args_t_lst) ->
        let llvm_ret_t = _rast_t_to_llvm_t ret_t in

        let args_to_llvm args_t_lst =
          let rec _args_to_rev_llvm llvm_t_lst_so_far args_t_lst =
            begin match args_t_lst with
            | [] -> (llvm_t_lst_so_far, false)
            | [RVarArgSentinel] -> (llvm_t_lst_so_far, true)
            | RVarArgSentinel::_ ->
                failwith "VarArgSentinel must be alone and last."
            | x::xs ->
                let llvm_t = _rast_t_to_llvm_t x in

                _args_to_rev_llvm (llvm_t::llvm_t_lst_so_far) xs
          end in
          let (rev_llvm_t_lst, is_var_arg) = _args_to_rev_llvm [] args_t_lst in

          (List.rev rev_llvm_t_lst, is_var_arg)
        in

        let (llvm_args_t_lst, is_var_arg) = args_to_llvm args_t_lst in
        let llvm_args_t_arr = Array.of_list llvm_args_t_lst in

        let func_t = begin if is_var_arg then
          Llvm.var_arg_function_type llvm_ret_t llvm_args_t_arr
        else
          Llvm.function_type llvm_ret_t llvm_args_t_arr
        end in

        (* We always work with function _pointers_ as a layer of abstraction,
        as raw LLVM function types are sizeless and can't be allocated for. *)
        Llvm.pointer_type func_t

    | RVarArgSentinel ->
        failwith "Should not need to determine type for var arg"
  end in

  _rast_t_to_llvm_t
;;


let initialize_fpm the_fpm =
  (* Promote allocas to registers. *)
  Llvm_scalar_opts.add_memory_to_register_promotion the_fpm ;
  (* Do simple "peephole" optimizations and bit-twiddling optzn. *)
  Llvm_scalar_opts.add_instruction_combination the_fpm ;
  (* Try to move code out of body of loops, into pre/post loop code.  *)
  Llvm_scalar_opts.add_licm the_fpm ;
  (* Try to promote allocas to SSA/registers. *)
  Llvm_scalar_opts.add_scalar_repl_aggregation the_fpm ;
  Llvm_scalar_opts.add_scalar_repl_aggregation_ssa the_fpm ;

  (* Reassociate expressions. *)
  Llvm_scalar_opts.add_reassociation the_fpm ;

  (* Eliminate Common SubExpressions.

  NOTE: This is _disabled_ due to this optimization appearing to run into
  LLVM backend code generation bugs, RE "Cannot select", involving bitcasts
  between lowered variants (super-tuples) and their target constructor tuples.

  Example:

  LLVM ERROR: Cannot select: 0x5628a72cf220: ch = bitcast Constant:i8<0>
    0x5628a71dce30: i8 = Constant<0>
  In function: main
  PLEASE submit a bug report to https://github.com/llvm/llvm-project/issues/ and include the crash backtrace.
  Stack dump:
  0.  Running pass 'Function Pass Manager' on module 'main'.
  1.  Running pass 'X86 DAG->DAG Instruction Selection' on function '@main'
  zsh: IOT instruction (core dumped)  _build/default/bin/lexer_main.exe

  *)
  (* Llvm_scalar_opts.add_gvn the_fpm ; *)

  (* Constant propagation/merging. *)
  Llvm_scalar_opts.add_sccp the_fpm ;
  (* Trivial removal of redundant stores. *)
  Llvm_scalar_opts.add_dead_store_elimination the_fpm ;
  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  Llvm_scalar_opts.add_cfg_simplification the_fpm ;
  (* Dead-code elimination. *)
  Llvm_scalar_opts.add_aggressive_dce the_fpm ;

  (* Repeat this transform. This can transform allocas of aggregates into
  allocas of individual members, then further transforms into SSA form if
  possible. This optimization can collapse complex variant construction/matching
  logic into constants. This can also leave several basic blocks dead with no
  predecessors, but attempts to remove them seem to be unsuccessful. *)
  Llvm_scalar_opts.add_scalar_repl_aggregation_ssa the_fpm ;

  (* NOTE: The above can make several basic blocks dead, so it would be nice to
  be able to eliminate them. The following all don't seem to succeed: *)
  (*
  Llvm_scalar_opts.add_aggressive_dce the_fpm ;
  Llvm_scalar_opts.add_sccp the_fpm ;
  Llvm_scalar_opts.add_aggressive_dce the_fpm ;
  Llvm_scalar_opts.add_cfg_simplification the_fpm ;
  *)

  (* Note: We _don't_ apply tail-call elimination. Default tail-call behavior
  seems to produce better code, or approximately equivalent code that is easier
  to read (in simple cases, at least). *)
  (* Llvm_scalar_opts.add_tail_call_elimination the_fpm ; *)

  (* Do some optimizations again, as these have demonstrably reduced more
  code when ran again after the above. *)

  Llvm_scalar_opts.add_memory_to_register_promotion the_fpm ;
  Llvm_scalar_opts.add_instruction_combination the_fpm ;

  (* Return value here only indicates whether internal state was modified *)
  let _ = Llvm.PassManager.initialize the_fpm in
  ()
;;


let initialize_mpm the_mpm =
  (* Propagate constants from callsites into function bodies. *)
  Llvm_ipo.add_ipsccp the_mpm ;
  (* Merge duplicate global constants. *)
  Llvm_ipo.add_constant_merge the_mpm ;
  (* Optimize non-address-taken globals. *)
  Llvm_ipo.add_global_optimizer the_mpm ;
  (* Remove unused arguments to functions. *)
  Llvm_ipo.add_dead_arg_elimination the_mpm ;
  (* Pass instead by-value any small RO by-reference args. *)
  Llvm_ipo.add_argument_promotion the_mpm ;
  (* Annotate functions with attributes indicating various RO behavior. *)
  Llvm_ipo.add_function_attrs the_mpm ;
  (* Inline small functions. *)
  Llvm_ipo.add_function_inlining the_mpm ;
  (* Eliminate unreachable/unused globals and functions. *)
  Llvm_ipo.add_global_dce the_mpm ;

  ()
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
  let cmd = Printf.sprintf "clang -no-pie -o %s %s" filename_exe filename_obj in
  begin match Sys.command cmd with
    | 0 -> Printf.printf "Wrote %s\n" filename_exe
    | n -> Printf.printf "clang failed with %d\n" n
  end
;;
