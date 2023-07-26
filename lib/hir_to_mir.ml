open Hir
open Mir

(* type hir_variable = rast_t * string
declarations = hir_variable list *)

(* Given a list of variable declarations, generate MIR for allocating stack
space for those variables in the given basic block.

TODO: This could be improved by attempting to group the declarations based on
their type, so that they may end up being more space-efficient on the stack.
It may be that the lower-level codegen (eg, LLVM) does this optimization for us,
but it could make sense to do it here to ensure the optimization is performed.
*)
let hscope_decls_to_mir mir_ctxt bb decls =
  let alloca_instrs_rev =
    List.fold_left (
      fun alloca_instrs_rev (t, name) ->
        let alloca_lval = {t=RPtr(t); kind=Tmp; lname=name} in
        let alloca_instr = Alloca(alloca_lval, t) in
        (alloca_instr :: alloca_instrs_rev)
    ) [] decls
  in

  (* Try to ensure the MIR allocas the variables in roughly their order of
  use. *)
  let alloca_instrs = List.rev alloca_instrs_rev in

  let bb = {bb with instrs = bb.instrs @ alloca_instrs} in
  let mir_ctxt = update_bb mir_ctxt bb in

  (mir_ctxt, bb)
;;

let hscope_instrs_to_mir mir_ctxt bb instrs =
  instrs |> ignore;

  let bb = {bb with instrs = bb.instrs @ [RetVoid]} in
  let mir_ctxt = update_bb mir_ctxt bb in

  (mir_ctxt, bb)
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

  let bb_entry = {name="entry"; instrs=[]} in

  (* Generate MIR for all variable declarations. We do this because:

  - This simplifies handling of generating the instructions themselves. Simply
  assume any relevant variables already exist, and use them accordingly.

  - This ensures we don't end up with non-optimal codegen like stack allocas
  within loops that can exhaust the stack despite not actually needing a
  separate stack allocation for each run through the loop. *)
  let (mir_ctxt, bb) =
    hscope_decls_to_mir
      mir_ctxt
      bb_entry
      toplevel_decl_hfscope.declarations
  in

  (* Generate MIR for the tree of scoped instructions. *)
  let (mir_ctxt, _) =
    hscope_instrs_to_mir
      mir_ctxt
      bb
      toplevel_decl_hfscope.instructions
  in

  mir_ctxt
;;
