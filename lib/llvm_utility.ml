open Typing

let berk_t_to_llvm_t llvm_sizeof llvm_ctxt =
  let rec _berk_t_to_llvm_t typ =
    begin match typ with
    | Nil -> Llvm.void_type llvm_ctxt

    | PtrTo(pointed_t) -> Llvm.pointer_type (_berk_t_to_llvm_t pointed_t)

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
