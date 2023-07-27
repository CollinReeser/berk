open Ir
open Rast_typing
open Utility

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)

(* The MIR (mid-level intermediate representation) is a lowering of the
high-level AST (or HIR). This provides a reduced-complexity but computationally
equivalent version of the input program, which is easier to process. *)

type lval_kind =
| Var
| Arg
| Tmp

(* Lvalues, which can be assigned to and can be read in the RHS. *)
type lval = {
  t: rast_t;
  kind: lval_kind;
  lname: string;
}

type constant =
| ValNil
| ValU8 of int | ValU16 of int | ValU32 of int | ValU64 of int
| ValI8 of int | ValI16 of int | ValI32 of int | ValI64 of int
| ValF32 of float | ValF64 of float
| ValF128 of string
| ValBool of bool
| ValStr of string
| ValFunc of string

(* Components of an instruction RHS. *)
type rval =
| Constant of constant
| RVar of lval

type index =
| Static of int
| Dynamic of lval

(* Instruction *)
type instr =
(* The lval representation of the function argument at the given index. *)
| GetArg of lval * int
(* Create an alloca (stack-allocated space of some static size) *)
| Alloca of lval * rast_t
(* Store -> lhs is memory target, rhs is stored value *)
| Store of lval * lval
(* Load -> lhs is loaded value, rhs memory target *)
| Load of lval * lval
| Assign of lval * rval
| UnOp of lval * un_op * lval
| BinOp of lval * bin_op * lval * lval
(* Cast the RHS value by the cast_op into the LHS. *)
| Cast of lval * cast_op * lval
(* Yields an lval of some ptr type, that when loaded yields a value of the type
within the ptr, and can store a value of the type pointed to by the ptr. The RHS
lval is the object to index into, to either load from or store into. The LHS is
always a pointer type. *)
| PtrTo of lval * index list * lval
(* Turn a list of separate values into a struct containing those values, whose
members are in the same order as the given list. *)
| ConstructAggregate of lval * lval list
(* Where `lval-result`, `index`, lval-orig-aggregate`, `lval-element`, yield
a new aggregate lval that matches the original aggregate lval, save for the
element at the given index being replaced by the given element. *)
| IntoAggregate of lval * int * lval * lval
(* Yield the lval element at the given index in the given aggregate value. *)
| FromAggregate of lval * int * lval
(* The first lval is the return value, and the second lval is the function to be
called. *)
| Call of lval * lval * lval list
(* The lval is the function to be called. *)
| CallVoid of lval * lval list
| Br of bb
| CondBr of lval * bb * bb
| RetVoid
| Ret of lval

and bb = {
  name: string;
  instrs: instr list;
}

type mir_ctxt = {
  f_name: string;
  f_params: (string * rast_t) list;
  f_ret_rt: rast_t;
  name_gen: int;
  lvars: lval StrMap.t;
  bbs: bb StrMap.t;
}

(* Formatting functions. *)

let fmt_lval_kind kind =
  match kind with
  | Var -> "var"
  | Arg -> "arg"
  | Tmp -> "tmp"

let fmt_constant constant =
  let open Printf in
  match constant with
  | ValNil -> sprintf "nil"
  | ValU8(x) | ValU16(x) | ValU32(x) | ValU64(x)
  | ValI8(x) | ValI16(x) | ValI32(x) | ValI64(x) -> sprintf "%d" x
  | ValF32(f) | ValF64(f) -> sprintf "%f" f
  | ValF128(str) -> sprintf "%s" str
  | ValBool(b) -> sprintf "%b" b
  | ValStr(str) -> sprintf "\"%s\"" (String.escaped str)
  | ValFunc(func_name) -> sprintf "fn<%s>" func_name

let fmt_lval ({t; kind; lname} : lval) =
  Printf.sprintf "%s<%s>: %s" lname (fmt_lval_kind kind) (fmt_rtype t)

let fmt_rval rval =
  match rval with
  | Constant(constant) -> fmt_constant constant
  | RVar(lval) -> fmt_lval lval

let fmt_index idx =
  let open Printf in
  match idx with
  | Static(i) -> sprintf "%d" i
  | Dynamic(lval) -> fmt_lval lval

let fmt_join_indices idxs =
  fmt_join_strs ", " (List.map fmt_index idxs)

let fmt_instr instr =
  let open Printf in
  match instr with
  | GetArg(lval, i) ->
      sprintf "  %s = fn_arg[%d]\n"
        (fmt_lval lval)
        i

  | Alloca(lval, pointed_t) ->
      sprintf "  %s = alloca of %s\n"
        (fmt_lval lval)
        (fmt_rtype pointed_t)

  | Store(lval, rhs_lval) ->
      sprintf "  %s ->[store]-> %s\n"
        (fmt_lval rhs_lval)
        (fmt_lval lval)

  | Load(lval, rhs_lval) ->
      sprintf "  %s <-[load]<- %s\n"
        (fmt_lval lval)
        (fmt_lval rhs_lval)

  | Assign(lval, rval) ->
      sprintf "  %s = %s\n"
        (fmt_lval lval)
        (fmt_rval rval)

  | UnOp(out_lval, op, in_lval) ->
      sprintf "  %s = %s %s\n"
        (fmt_lval out_lval)
        (fmt_un_op op)
        (fmt_lval in_lval)

  | BinOp(lval, op, lhs_lval, rhs_lval) ->
      sprintf "  %s = %s %s %s\n"
        (fmt_lval lval)
        (fmt_lval lhs_lval)
        (fmt_bin_op op)
        (fmt_lval rhs_lval)

  | Cast({t=target_t; _} as lval, un_op, rhs_lval) ->
      let fmt_un_op un_op = begin match un_op with
        | Truncate -> "truncate of"
        | Extend -> "extend of"
        | Bitwise -> "bitwise cast of"
      end in

      sprintf "  %s = %s %s into %s\n"
        (fmt_lval lval)
        (fmt_un_op un_op)
        (fmt_lval rhs_lval)
        (fmt_rtype target_t)

  | PtrTo({t; _} as lval, idxs, aggregate_lval) ->
      sprintf "  %s = getptr %s via %s following indices (%s)\n"
        (fmt_lval lval)
        (fmt_rtype t)
        (fmt_lval aggregate_lval)
        (fmt_join_indices idxs)

  | ConstructAggregate(lval, elems) ->
      sprintf "  %s = aggregate of (%s)\n"
        (fmt_lval lval)
        (fmt_join_strs "; "(List.map fmt_lval elems))

  | IntoAggregate(lval_res, i, lval_aggregate, lval_elem) ->
      sprintf "  %s = %s but %s inserted at index %d\n"
        (fmt_lval lval_res)
        (fmt_lval lval_aggregate)
        (fmt_lval lval_elem)
        i

  | FromAggregate(lval, i, lval_aggregate) ->
      sprintf "  %s = extract index %d from %s\n"
        (fmt_lval lval)
        i
        (fmt_lval lval_aggregate)

  | Call(lval, lval_func, args) ->
      sprintf "  %s = call %s(%s)\n"
        (fmt_lval lval)
        (fmt_lval lval_func)
        (fmt_join_strs ", " (List.map fmt_lval args))

  | CallVoid(lval_func, args) ->
      sprintf "  call %s(%s)\n"
        (fmt_lval lval_func)
        (fmt_join_strs ", " (List.map fmt_lval args))

  | Br({name; _}) ->
      sprintf "  branch to %s\n" name

  | CondBr(lval, {name=lhs_name; _}, {name=rhs_name; _}) ->
      sprintf "  branch to %s if %s else %s\n"
        lhs_name
        (fmt_lval lval)
        rhs_name

  | RetVoid -> sprintf "  ret (void)\n"
  | Ret(lval) ->
      sprintf "  ret %s\n"
        (fmt_lval lval)

let fmt_bb ({name; instrs} : bb) =
  Printf.sprintf "%s:\n%s"
    name
    (List.fold_left (^) "" (List.map fmt_instr instrs))


(* Utility functions *)

(* Given an MIR context, yield a list of the bbs the MIR context knows about,
in such an order that a block will not be encountered in the list before it
is branched to from a previous block. *)
let control_flow_list ?(allow_malformed=false) mir_ctxt : bb list =
  if StrMap.is_empty mir_ctxt.bbs then
    []
  else
    let bbs = StrMap.bindings mir_ctxt.bbs in
    let (_, entry) = List.find (fun (k, _) -> k = "entry") bbs in

    (* Yield lists of the basic blocks that the given basic block can branch
    to. *)
    let get_branches bb : bb list =
      let find_bb bb_name bbs =
        begin match (StrMap.find_opt bb_name bbs) with
        | Some(bb) -> bb
        | None ->
            failwith (
              Printf.sprintf "Could not find bb [%s]" bb_name
            )
        end
      in

      (* The last instruction in any basic block must be a terminator, either
      returning out from the function, or branching to one or more other basic
      blocks. *)
      let terminator = List.hd (List.rev bb.instrs) in
      begin match terminator with
      | Br({name; _}) -> [find_bb name mir_ctxt.bbs]
      | CondBr(_, {name=bb_if_name; _}, {name=bb_else_name; _}) -> [
          find_bb bb_if_name mir_ctxt.bbs;
          find_bb bb_else_name mir_ctxt.bbs
        ]
      | Ret(_) -> []
      | RetVoid -> []
      | _ ->
          if allow_malformed then
            []
          else
            failwith (
              Printf.sprintf
                "Expected terminator, got: [%s]"
                (fmt_instr terminator)
            )
      end
    in

    let graph_so_far_rev = [entry] in
    let next_queue = get_branches entry in
    let seen = StrSet.add "entry" StrSet.empty in

    (* Build the control flow graph (but in reverse). *)
    let rec build_control_flow_graph_rev graph_so_far_rev next_queue seen =
      begin match next_queue with
      | [] -> graph_so_far_rev
      | {name; _} as next::rest_queue ->
          if StrSet.exists (fun elem -> elem = name) seen then
            (* We've already processed this basic block; skip to next. *)
            build_control_flow_graph_rev graph_so_far_rev rest_queue seen
          else
            (* Process this basic block, this is first we've seen it. *)
            let new_branches = get_branches next in
            let next_queue = rest_queue @ new_branches in
            let graph_so_far_rev = next :: graph_so_far_rev in
            let seen = StrSet.add name seen in
            build_control_flow_graph_rev graph_so_far_rev next_queue seen
      end
    in

    List.rev (build_control_flow_graph_rev graph_so_far_rev next_queue seen)

let fmt_mir_ctxt
  ?(sorted=true) ({f_name; f_params; f_ret_rt; bbs=bbs_map; _} as mir_ctxt)
=
  let open Printf in
  let bbs =
    begin if sorted then
      let bbs = control_flow_list ~allow_malformed:true mir_ctxt in
      bbs
    else
      let bbs = List.map (fun (_, bb) -> bb) (StrMap.bindings bbs_map) in
      bbs
    end
  in
  let f_params_fmted =
    fmt_join_strs ", " (
      List.map (fun (n, t) -> sprintf "%s: %s" n (fmt_rtype t)) f_params
    )
  in

  if StrMap.is_empty bbs_map then
    sprintf "\ndecl fn %s(%s) -> %s\n"
      f_name
      f_params_fmted
      (fmt_rtype f_ret_rt)
  else
    sprintf "\nfn %s(%s) -> %s:\n%s"
      f_name
      f_params_fmted
      (fmt_rtype f_ret_rt)
      (List.fold_left (^) "" (List.map fmt_bb bbs))

let pprint_mir_ctxt ppf mir_ctxt =
  Format.fprintf ppf "%s" (fmt_mir_ctxt mir_ctxt)

(* Generating functions. *)

let get_varname ?(prefix="") mir_ctxt : (mir_ctxt * string) =
  let prefix = if String.length prefix > 0 then prefix else "__tmp" in
  (
    {mir_ctxt with name_gen = mir_ctxt.name_gen + 1},
    Printf.sprintf "%s_%d" prefix mir_ctxt.name_gen
  )

(* Get a unique name, useable to create a new basic block. *)
let get_bbname mir_ctxt : (mir_ctxt * string) =
  (
    {mir_ctxt with name_gen = mir_ctxt.name_gen + 1},
    Printf.sprintf "bb_%d" mir_ctxt.name_gen
  )

(* Replace the existing basic block in the MIR ctxt with the given bb, keyed
on the name of the bb. *)
let update_bb mir_ctxt bb =
  let {name=name; _} = bb in
  let bbs = StrMap.add name bb mir_ctxt.bbs in
  let mir_ctxt = {mir_ctxt with bbs=bbs} in

  mir_ctxt

let get_bb mir_ctxt bb_name : bb =
  StrMap.find bb_name mir_ctxt.bbs

let get_entry mir_ctxt : bb = get_bb mir_ctxt "entry"

let instr_lval instr =
  match instr with
  | GetArg(lval, _) -> lval
  | Assign(lval, _) -> lval
  | Alloca(lval, _) -> lval
  | Store(lval, _) -> lval
  | Load(lval, _) -> lval
  | UnOp(lval, _, _) -> lval
  | BinOp(lval, _, _, _) -> lval
  | Cast(lval, _, _) -> lval
  | PtrTo(lval, _, _) -> lval
  | ConstructAggregate(lval, _) -> lval
  | IntoAggregate(lval, _, _, _) -> lval
  | FromAggregate(lval, _, _) -> lval
  | Call(lval, _, _) -> lval
  | CallVoid(_, _) -> failwith "No resultant lval for void call"
  | CondBr(_, _, _) -> failwith "No resultant lval for condbr"
  | Ret(_) -> failwith "No resultant lval for ret"
  | Br(_) -> failwith "No resultant lval for br"
  | RetVoid -> failwith "No resultant lval for ret (void)"

(* Wrap the given lval in an alloca, and yield that alloca lval. *)
let lval_to_alloca mir_ctxt bb lval expected_t =
  (* Allocate stack space for the value *)
  let (mir_ctxt, alloca_varname) = get_varname mir_ctxt in
  let alloca_lval =
    {t=RPtr(expected_t); kind=Tmp; lname=alloca_varname}
  in
  let alloca_instr = Alloca(alloca_lval, expected_t) in

  (* Store the value into the alloca. *)
  let store_instr = Store(alloca_lval, lval) in

  let bb = {bb with instrs = bb.instrs @ [alloca_instr; store_instr]} in

  (mir_ctxt, bb, alloca_lval)
;;


let literal_to_instr mir_ctxt bb t ctor =
  let (mir_ctxt, varname) = get_varname mir_ctxt in
  let lval = {t=t; kind=Tmp; lname=varname} in
  let instr = Assign(lval, Constant(ctor)) in
  let bb = {bb with instrs=bb.instrs @ [instr]} in
  (mir_ctxt, bb, lval)
;;


let assign_rhs_to_decl mir_ctxt bb lhs_name rhs_lval expected_t =
  let (mir_ctxt, bb, alloca_lval) =
    lval_to_alloca mir_ctxt bb rhs_lval expected_t
  in

  let lval = {t=RPtr(expected_t); kind=Var; lname=lhs_name} in
  let assign_instr = Assign(lval, RVar(alloca_lval)) in

  let mir_ctxt = {
    mir_ctxt with lvars = StrMap.add lhs_name lval mir_ctxt.lvars
  } in

  let bb = {bb with instrs = bb.instrs @ [assign_instr]} in

  (mir_ctxt, bb)
;;


(* Perform "clean-up" passes on the basic block, to eg eliminate dead code. *)
let clean_up_bb_mir (bb : bb) =
  let rec _remove_dead_mir rev_instrs_left instrs_preserved : instr list =
    begin match rev_instrs_left with
    | [] -> instrs_preserved

    (* Keep intructions only until the first terminator. *)
    | ((Br(_) | CondBr(_) | RetVoid | Ret(_)) as term_instr) :: rest ->
        _remove_dead_mir rest [term_instr]

    | nonterm_instr :: rest ->
        _remove_dead_mir rest (nonterm_instr :: instrs_preserved)
    end
  in

  let rev_instrs = List.rev bb.instrs in
  let instrs_preserved = _remove_dead_mir rev_instrs [] in

  let bb = {bb with instrs = instrs_preserved} in

  bb


(* Perform "clean-up" passes on the generated MIR. *)
let clean_up_mir (mir_ctxt : mir_ctxt) =
  let bbs_control_flow = control_flow_list mir_ctxt in
  let bbs_cleaned = List.map clean_up_bb_mir bbs_control_flow in

  let mir_ctxt = List.fold_left update_bb mir_ctxt bbs_cleaned in

  mir_ctxt


(* Populate the given basic block (probably `entry`) with MIR required to
translate function args into alloca lvals, making those arguments available to
the rest of MIR generation as named lvars. *)
let func_args_to_mir (mir_ctxt : mir_ctxt) (bb : bb) =
  let (mir_ctxt, bb, _) = begin
    List.fold_left (
      fun (mir_ctxt, bb, i) (param_name, t) ->
        let (mir_ctxt, arg_name) = get_varname mir_ctxt in
        let arg_lval = {t=t; kind=Arg; lname=arg_name} in
        let arg_instr = GetArg(arg_lval, i) in

        let bb = {bb with instrs = bb.instrs @ [arg_instr]} in

        let (mir_ctxt, bb) =
          assign_rhs_to_decl mir_ctxt bb param_name arg_lval t
        in

        (mir_ctxt, bb, i + 1)
    ) (mir_ctxt, bb, 0) mir_ctxt.f_params
  end in

  let (mir_ctxt, next_bb_name) = get_bbname mir_ctxt in
  let next_bb = {name=next_bb_name; instrs=[]} in

  let bb = {bb with instrs = (bb.instrs @ [Br(next_bb)])} in
  let mir_ctxt = update_bb mir_ctxt bb in
  let mir_ctxt = update_bb mir_ctxt next_bb in

  (mir_ctxt, next_bb)
