open Hir
open Mir

let hscope_decls_to_mir mir_ctxt decls =
  decls |> ignore;
  mir_ctxt
;;

let hscope_instrs_to_mir mir_ctxt instrs =
  instrs |> ignore;
  mir_ctxt
;;

let hfunc_decl_to_mir {hf_name; hf_params; hf_ret_t} =
  let mir_ctxt = {
    f_name = hf_name;
    f_params = hf_params;
    f_ret_rt = hf_ret_t;
    name_gen = 0;
    lvars = StrMap.empty;
    bbs = StrMap.empty
  } in

  mir_ctxt
;;

let hfunc_def_to_mir {hf_decl; hf_scope} =
  (* Setup declaration for the function. *)
  let mir_ctxt = hfunc_decl_to_mir hf_decl in

  (* Collect all internal declarations and move them to the top-level scope. *)
  let toplevel_decl_hfscope = rewrite_hscope_to_only_toplevel_decls hf_scope in

  (* Generate MIR for all variable declarations. *)
  let mir_ctxt =
    hscope_decls_to_mir
      mir_ctxt
      toplevel_decl_hfscope.declarations
  in

  (* Generate MIR for the tree of scoped instructions. *)
  let mir_ctxt =
    hscope_instrs_to_mir
      mir_ctxt
      toplevel_decl_hfscope.instructions
  in

  mir_ctxt
;;
