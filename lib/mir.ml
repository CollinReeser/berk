open Ast
open Ir
open Typing
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
  t: berk_t;
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
| Alloca of lval * berk_t
(* Store -> lhs is memory target, rhs is stored value *)
| Store of lval * lval
(* Load -> lhs is loaded value, rhs memory target *)
| Load of lval * lval
| Assign of lval * rval
| BinOp of lval * bin_op * lval * lval
| UnOp of lval * un_op * lval
(* Yields an lval of some ptr type, that when loaded yields a value of the type
within the ptr. The RHS lval is the object to index into. *)
| PtrTo of lval * index list * lval
(* Turn a list of separate values into a struct containing those values, whose
members are in the same order as the given list. *)
| ConstructAggregate of lval * lval list
(* At the given index, insert the given lval element into the given aggregate
value. *)
| IntoAggregate of int * lval * lval
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
  f_params: (ident_t * berk_t) list;
  f_ret_t: berk_t;
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
  Printf.sprintf "%s<%s>: %s" lname (fmt_lval_kind kind) (fmt_type t)

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
  | Alloca(lval, pointed_t) ->
      sprintf "  %s = alloca of %s\n"
        (fmt_lval lval)
        (fmt_type pointed_t)

  | Store(lval, rhs_lval) ->
      sprintf "  store %s into %s\n"
        (fmt_lval rhs_lval)
        (fmt_lval lval)

  | Load(lval, rhs_lval) ->
      sprintf "  %s = load %s\n"
        (fmt_lval lval)
        (fmt_lval rhs_lval)

  | Assign(lval, rval) ->
      sprintf "  %s = %s\n"
        (fmt_lval lval)
        (fmt_rval rval)

  | BinOp(lval, op, lhs_lval, rhs_lval) ->
      sprintf "  %s = %s %s %s\n"
        (fmt_lval lval)
        (fmt_lval lhs_lval)
        (fmt_bin_op op)
        (fmt_lval rhs_lval)

  | UnOp({t=target_t; _} as lval, un_op, rhs_lval) ->
      let fmt_un_op un_op = begin match un_op with
        | Truncate -> "truncate of"
        | Extend -> "extend of"
        | Bitwise -> "bitwise cast of"
      end in

      sprintf "  %s = %s %s into %s\n"
        (fmt_lval lval)
        (fmt_un_op un_op)
        (fmt_lval rhs_lval)
        (fmt_type target_t)

  | PtrTo({t=Ptr(t); _} as lval, idxs, aggregate_lval) ->
      sprintf "  %s = ptrto %s via %s following indices (%s)\n"
        (fmt_lval lval)
        (fmt_type t)
        (fmt_lval aggregate_lval)
        (fmt_join_indices idxs)

  | PtrTo(_, _, _) -> failwith "Cannot fmt ptrto with non-ptr lval"

  | ConstructAggregate(lval, elems) ->
      sprintf "  %s = aggregate of (%s)\n"
        (fmt_lval lval)
        (fmt_join_strs "; "(List.map fmt_lval elems))

  | IntoAggregate(i, lval_elem, lval_aggregate) ->
      sprintf "  insert %s into %s at index %d\n"
        (fmt_lval lval_elem)
        (fmt_lval lval_aggregate)
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
let control_flow_list mir_ctxt : bb list =
  if StrMap.is_empty mir_ctxt.bbs then
    []
  else
    let bbs = StrMap.bindings mir_ctxt.bbs in
    let (_, entry) = List.find (fun (k, _) -> k = "entry") bbs in

    (* Yield lists of the basic blocks that the given basic block can branch
    to. *)
    let get_branches bb : bb list =
      let terminator = List.hd (List.rev bb.instrs) in
      begin match terminator with
      | Br({name; _}) -> [StrMap.find name mir_ctxt.bbs]
      | CondBr(_, {name=bb_if_name; _}, {name=bb_else_name; _}) -> [
          StrMap.find bb_if_name mir_ctxt.bbs;
          StrMap.find bb_else_name mir_ctxt.bbs
        ]
      | Ret(_) -> []
      | RetVoid -> []
      | _ ->
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
            build_control_flow_graph_rev graph_so_far_rev rest_queue seen
          else
            let new_branches = get_branches next in
            let next_queue = rest_queue @ new_branches in
            let graph_so_far_rev = next :: graph_so_far_rev in
            let seen = StrSet.add name seen in
            build_control_flow_graph_rev graph_so_far_rev next_queue seen
      end
    in

    List.rev (build_control_flow_graph_rev graph_so_far_rev next_queue seen)

let fmt_mir_ctxt
  ?(sorted=true) ({f_name; f_params; f_ret_t; bbs=bbs_map; _} as mir_ctxt)
=
  let open Printf in
  let bbs =
    begin if sorted then
      let bbs = control_flow_list mir_ctxt in
      bbs
    else
      let bbs = List.map (fun (_, bb) -> bb) (StrMap.bindings bbs_map) in
      bbs
    end
  in
  let f_params_fmted =
    fmt_join_strs ", " (
      List.map (fun (n, t) -> sprintf "%s: %s" n (fmt_type t)) f_params
    )
  in

  if StrMap.is_empty bbs_map then
    sprintf "\ndecl fn %s(%s) -> %s\n"
      f_name
      f_params_fmted
      (fmt_type f_ret_t)
  else
    sprintf "\nfn %s(%s) -> %s:\n%s"
      f_name
      f_params_fmted
      (fmt_type f_ret_t)
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
  | Assign(lval, _) -> lval
  | Alloca(lval, _) -> lval
  | Store(lval, _) -> lval
  | Load(lval, _) -> lval
  | BinOp(lval, _, _, _) -> lval
  | UnOp(lval, _, _) -> lval
  | PtrTo(lval, _, _) -> lval
  | ConstructAggregate(lval, _) -> lval
  | IntoAggregate(_, _, _) -> failwith "Aggregate insertion yields no value"
  | FromAggregate(lval, _, _) -> lval
  | Call(lval, _, _) -> lval
  | CallVoid(_, _) -> failwith "No resultant lval for void call"
  | CondBr(_, _, _) -> failwith "No resultant lval for condbr"
  | Ret(_) -> failwith "No resultant lval for ret"
  | Br(_) -> failwith "No resultant lval for br"
  | RetVoid -> failwith "No resultant lval for ret (void)"

(* Wrap the given lval in an alloca, and yield that alloca lval. *)
let lval_to_alloca mir_ctxt bb lval expected_t =
  let {t=actual_t; _} = lval in

  let (mir_ctxt, bb, alloca_lval, instructions) = begin match expected_t with
  | Variant(_, _) as variant_t ->
      (* Allocate stack space for the variant *)
      let (mir_ctxt, variant_alloca_varname) = get_varname mir_ctxt in
      let alloca_lval =
        {t=Ptr(variant_t); kind=Tmp; lname=variant_alloca_varname}
      in
      let alloca_instr = Alloca(alloca_lval, variant_t) in

      (* Bitcast the alloca into a form that agrees with the constructed
      aggregate. *)
      let (mir_ctxt, bitcast_ptr_varname) = get_varname mir_ctxt in
      let bitcast_ptr_lval =
        {t=Ptr(actual_t); kind=Tmp; lname=bitcast_ptr_varname}
      in
      let bitcast_instr = UnOp(bitcast_ptr_lval, Bitwise, alloca_lval) in

      (* Store the variant aggregate into the alloca. *)
      let store_instr = Store(bitcast_ptr_lval, lval) in

      (mir_ctxt, bb, alloca_lval, [alloca_instr; bitcast_instr; store_instr])

  | _ ->
      (* Allocate stack space for the value *)
      let (mir_ctxt, variant_alloca_varname) = get_varname mir_ctxt in
      let alloca_lval =
        {t=Ptr(expected_t); kind=Tmp; lname=variant_alloca_varname}
      in
      let alloca_instr = Alloca(alloca_lval, expected_t) in

      (* Store the variant aggregate into the alloca. *)
      let store_instr = Store(alloca_lval, lval) in

      (mir_ctxt, bb, alloca_lval, [alloca_instr; store_instr])
  end in

  let bb = {bb with instrs = bb.instrs @ instructions} in

  (mir_ctxt, bb, alloca_lval)

let literal_to_instr mir_ctxt bb t ctor =
  let (mir_ctxt, varname) = get_varname mir_ctxt in
  let lval = {t=t; kind=Tmp; lname=varname} in
  let instr = Assign(lval, Constant(ctor)) in
  let bb = {bb with instrs=bb.instrs @ [instr]} in
  (mir_ctxt, bb, lval)

let rec expr_to_mir (mir_ctxt : mir_ctxt) (bb : bb) (exp : Ast.expr) =
  let rec _expr_to_mir
    (mir_ctxt : mir_ctxt) (bb : bb) (exp : Ast.expr) : (mir_ctxt * bb * lval)
  =
    let (mir_ctxt, bb, instr) = begin match exp with
      | ValNil -> ValNil |> literal_to_instr mir_ctxt bb Nil

      | ValBool(b) -> ValBool(b) |> literal_to_instr mir_ctxt bb Bool

      | ValU8 (x) -> ValU8(x)  |> literal_to_instr mir_ctxt bb U8
      | ValU16(x) -> ValU16(x) |> literal_to_instr mir_ctxt bb U16
      | ValU32(x) -> ValU32(x) |> literal_to_instr mir_ctxt bb U32
      | ValU64(x) -> ValU64(x) |> literal_to_instr mir_ctxt bb U64

      | ValI8 (x) -> ValI8 (x) |> literal_to_instr mir_ctxt bb I8
      | ValI16(x) -> ValI16(x) |> literal_to_instr mir_ctxt bb I16
      | ValI32(x) -> ValI32(x) |> literal_to_instr mir_ctxt bb I32
      | ValI64(x) -> ValI64(x) |> literal_to_instr mir_ctxt bb I64

      | ValInt(U8, x) -> ValU8(x) |> literal_to_instr mir_ctxt bb U8
      | ValInt(U16, x) -> ValU16(x) |> literal_to_instr mir_ctxt bb U16
      | ValInt(U32, x) -> ValU32(x) |> literal_to_instr mir_ctxt bb U32
      | ValInt(U64, x) -> ValU64(x) |> literal_to_instr mir_ctxt bb U64
      | ValInt(I8, x) -> ValI8(x) |> literal_to_instr mir_ctxt bb I8
      | ValInt(I16, x) -> ValI16(x) |> literal_to_instr mir_ctxt bb I16
      | ValInt(I32, x) -> ValI32(x) |> literal_to_instr mir_ctxt bb I32
      | ValInt(I64, x) -> ValI64(x) |> literal_to_instr mir_ctxt bb I64

      | ValInt(t, x) ->
          failwith (
            Printf.sprintf "Nonsense type [%s] for int [%d] converting to MIR."
              (fmt_type t) x
          )

      | ValF32(f) -> ValF32(f) |> literal_to_instr mir_ctxt bb F32
      | ValF64(f) -> ValF64(f) |> literal_to_instr mir_ctxt bb F64
      | ValF128(str) -> ValF128(str) |> literal_to_instr mir_ctxt bb F128

      | ValStr(str) -> ValStr(str) |> literal_to_instr mir_ctxt bb String

      | ValFunc(func_t, func_name) ->
          ValFunc(func_name) |> literal_to_instr mir_ctxt bb func_t

      | ValVar(var_t, varname) ->
          (* For variable access in MIR, we assume the variable is nested inside
          an alloca that must be loaded from. *)
          let ptr_lval = try
            StrMap.find varname mir_ctxt.lvars
          with Not_found ->
            failwith (Printf.sprintf "No known varname [%s]" varname)
          in
          let {t=ptr_t; _} = ptr_lval in
          let pointed_t = unwrap_ptr ptr_t in

          let _ = if var_t <> pointed_t then
            failwith (
              Printf.sprintf
                "Unexpected mismatch in var types: [[ %s ]] [[ %s ]] for [%s]"
                (fmt_type var_t)
                (fmt_type pointed_t)
                varname
            )
          else
            ()
          in

          let (mir_ctxt, load_varname) = get_varname mir_ctxt in
          let load_lval = {t=var_t; kind=Tmp; lname=load_varname} in
          let load_instr = Load(load_lval, ptr_lval) in
          let bb = {bb with instrs = bb.instrs @ [load_instr]} in

          (mir_ctxt, bb, load_lval)

      (* FIXME: These casts are are identical in structure; is there a way to
      cleanly collapse their implementations? *)
      | ValCastTrunc(t, exp) ->
          let (mir_ctxt, bb, to_trunc_lval) = _expr_to_mir mir_ctxt bb exp in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let lval = {t=t; kind=Tmp; lname=varname} in
          let instr = UnOp(lval, Truncate, to_trunc_lval) in

          let bb = {bb with instrs=bb.instrs @ [instr]} in

          (mir_ctxt, bb, lval)

      | ValCastBitwise(t, exp) ->
          let (mir_ctxt, bb, to_bitwise_lval) = _expr_to_mir mir_ctxt bb exp in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let lval = {t=t; kind=Tmp; lname=varname} in
          let instr = UnOp(lval, Bitwise, to_bitwise_lval) in

          let bb = {bb with instrs=bb.instrs @ [instr]} in

          (mir_ctxt, bb, lval)

      | ValCastExtend(t, exp) ->
          let (mir_ctxt, bb, to_extend_lval) = _expr_to_mir mir_ctxt bb exp in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let lval = {t=t; kind=Tmp; lname=varname} in
          let instr = UnOp(lval, Extend, to_extend_lval) in

          let bb = {bb with instrs=bb.instrs @ [instr]} in

          (mir_ctxt, bb, lval)

      | FuncCall(t, func_name, exprs) ->
          let ((mir_ctxt, bb), arg_values) =
            List.fold_left_map (
              fun (mir_ctxt, bb) exp ->
                let (mir_ctxt, bb, arg_val) = _expr_to_mir mir_ctxt bb exp in
                ((mir_ctxt, bb), arg_val)
            ) (mir_ctxt, bb) exprs
          in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let func_t = Function(t, (List.map expr_type exprs)) in
          let func_lval = {t=func_t; kind=Tmp; lname=varname} in
          let func_instr = Assign(func_lval, Constant(ValFunc(func_name))) in

          let (mir_ctxt, bb, lval, call_instr) = begin match t with
            | Nil ->
                let (mir_ctxt, bb, nil_lval) =
                  _expr_to_mir mir_ctxt bb ValNil
                in
                let instr = CallVoid(func_lval, arg_values) in

                (mir_ctxt, bb, nil_lval, instr)
            | _ ->
                let (mir_ctxt, varname) = get_varname mir_ctxt in
                let res_lval = {t=t; kind=Tmp; lname=varname} in
                let instr = Call(res_lval, func_lval, arg_values) in

                (mir_ctxt, bb, res_lval, instr)
          end in

          let bb = {bb with instrs=bb.instrs @ [func_instr; call_instr]} in

          (mir_ctxt, bb, lval)

      | VarInvoke(t, varname, exprs) ->
          (* For variable access in MIR, we assume the variable is nested inside
          an alloca that must be loaded from. *)

          (* TODO: Can we combine this loading logic with that for ValVar, since
          they're both doing a load precisely because we're "reading from a
          variable", regardless of contents? *)

          let ptr_lval = StrMap.find varname mir_ctxt.lvars in
          let {t=ptr_t; _} = ptr_lval in
          let pointed_t = unwrap_ptr ptr_t in

          let (mir_ctxt, load_varname) = get_varname mir_ctxt in
          let func_lval = {t=pointed_t; kind=Tmp; lname=load_varname} in
          let load_instr = Load(func_lval, ptr_lval) in
          let bb = {bb with instrs = bb.instrs @ [load_instr]} in

          let ((mir_ctxt, bb), arg_values) =
            List.fold_left_map (
              fun (mir_ctxt, bb) exp ->
                let (mir_ctxt, bb, arg_val) = _expr_to_mir mir_ctxt bb exp in
                ((mir_ctxt, bb), arg_val)
            ) (mir_ctxt, bb) exprs
          in

          let (mir_ctxt, bb, lval, call_instr) = begin match t with
            | Nil ->
                let (mir_ctxt, bb, nil_lval) =
                  _expr_to_mir mir_ctxt bb ValNil
                in
                let instr = CallVoid(func_lval, arg_values) in

                (mir_ctxt, bb, nil_lval, instr)
            | _ ->
                let (mir_ctxt, varname) = get_varname mir_ctxt in
                let res_lval = {t=t; kind=Tmp; lname=varname} in
                let instr = Call(res_lval, func_lval, arg_values) in

                (mir_ctxt, bb, res_lval, instr)
          end in

          let bb = {bb with instrs=bb.instrs @ [call_instr]} in

          (mir_ctxt, bb, lval)

      | BlockExpr(_, stmts, exp) ->
          let (mir_ctxt, bb) =
            List.fold_left (
              fun (mir_ctxt, bb) stmt -> stmt_to_mir mir_ctxt bb stmt
            ) (mir_ctxt, bb) stmts
          in

          let (mir_ctxt, bb, lval) = _expr_to_mir mir_ctxt bb exp in

          (mir_ctxt, bb, lval)

      | TupleExpr(t, exprs) ->
          let ((mir_ctxt, bb), tuple_values) =
            List.fold_left_map (
              fun (mir_ctxt, bb) exp ->
                let (mir_ctxt, bb, tuple_val) = _expr_to_mir mir_ctxt bb exp in
                ((mir_ctxt, bb), tuple_val)
            ) (mir_ctxt, bb) exprs
          in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let lval = {t=t; kind=Tmp; lname=varname} in
          let tuple_instr = ConstructAggregate(lval, tuple_values) in

          let bb = {bb with instrs=bb.instrs @ [tuple_instr]} in

          (mir_ctxt, bb, lval)

      (* TODO: This is structually identical to TupleExprs. Are statically
      sized arrays really so interesting that they need to be different? The
      question really is whether a statically sized array must also be
      statically fully initialized, or if it can be partially/fully
      _un_initialized after first declaration.
       *)
      | ArrayExpr(t, exprs) ->
          let ((mir_ctxt, bb), arr_values) =
            List.fold_left_map (
              fun (mir_ctxt, bb) exp ->
                let (mir_ctxt, bb, arr_val) = _expr_to_mir mir_ctxt bb exp in
                ((mir_ctxt, bb), arr_val)
            ) (mir_ctxt, bb) exprs
          in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let lval = {t=t; kind=Tmp; lname=varname} in
          let arr_instr = ConstructAggregate(lval, arr_values) in

          let bb = {bb with instrs=bb.instrs @ [arr_instr]} in

          (mir_ctxt, bb, lval)

      | BinOp(t, op, lhs, rhs) ->
          let (mir_ctxt, bb, lhs_lval) = _expr_to_mir mir_ctxt bb lhs in
          let (mir_ctxt, bb, rhs_lval) = _expr_to_mir mir_ctxt bb rhs in

          let instructions = [] in
          let lhs_t = expr_type lhs in
          let rhs_t = expr_type rhs in
          let common_t = common_type_of_lr lhs_t rhs_t in

          let (mir_ctxt, instructions, lhs_lval) =
          if lhs_t <> common_t then
            let (mir_ctxt, extend_name) = get_varname mir_ctxt in
            let extend_lval = {t=common_t; kind=Tmp; lname=extend_name} in
            let extend_instr = UnOp(extend_lval, Extend, lhs_lval) in
            let instructions = instructions @ [extend_instr] in

            (mir_ctxt, instructions, extend_lval)
          else
            (mir_ctxt, instructions, lhs_lval)
          in

          let (mir_ctxt, instructions, rhs_lval) =
          if rhs_t <> common_t then
            let (mir_ctxt, extend_name) = get_varname mir_ctxt in
            let extend_lval = {t=common_t; kind=Tmp; lname=extend_name} in
            let extend_instr = UnOp(extend_lval, Extend, rhs_lval) in
            let instructions = instructions @ [extend_instr] in

            (mir_ctxt, instructions, extend_lval)
          else
            (mir_ctxt, instructions, rhs_lval)
          in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let lval = {t=t; kind=Tmp; lname=varname} in
          let instr = BinOp(lval, op, lhs_lval, rhs_lval) in
          let instructions = instructions @ [instr] in

          let bb = {bb with instrs=bb.instrs @ instructions} in

          (mir_ctxt, bb, lval)

      | IfThenElseExpr(t, cond_expr, then_expr, else_expr) ->
          let core_if_then_else_gen mir_ctxt bb maybe_do_store =
            let (mir_ctxt, then_bb_name) = get_bbname mir_ctxt in
            let (mir_ctxt, else_bb_name) = get_bbname mir_ctxt in
            let (mir_ctxt, end_bb_name) = get_bbname mir_ctxt in
            let then_bb = {name=then_bb_name; instrs=[]} in
            let else_bb = {name=else_bb_name; instrs=[]} in
            let end_bb = {name=end_bb_name; instrs=[]} in

            let (mir_ctxt, bb, cond_lval) =
              _expr_to_mir mir_ctxt bb cond_expr
            in

            let (mir_ctxt, then_bb, then_instr) =
              _expr_to_mir mir_ctxt then_bb then_expr
            in
            let (mir_ctxt, else_bb, else_instr) =
              _expr_to_mir mir_ctxt else_bb else_expr
            in

            let then_bb =
              {
                then_bb with instrs =
                  (then_bb.instrs @ (maybe_do_store then_instr)) @ [Br(end_bb)]
              }
            in
            let else_bb =
              {
                else_bb with instrs =
                  (else_bb.instrs @ (maybe_do_store else_instr)) @ [Br(end_bb)]
              }
            in

            let cond_br = CondBr(cond_lval, then_bb, else_bb) in
            let bb = {bb with instrs = bb.instrs @ [cond_br]} in

            (mir_ctxt, (bb, then_bb, else_bb, end_bb))
          in

          let (mir_ctxt, (bb, then_bb, else_bb, end_bb), if_res_lval) =
            begin match t with
            | Nil ->
              let no_store _ = [] in

              let (mir_ctxt, (bb, then_bb, else_bb, end_bb)) =
                core_if_then_else_gen mir_ctxt bb no_store
              in

              let (mir_ctxt, end_bb, nil_lval) =
                _expr_to_mir mir_ctxt end_bb ValNil
              in

              (mir_ctxt, (bb, then_bb, else_bb, end_bb), nil_lval)

            | _ ->
              let (mir_ctxt, if_alloca_name) = get_varname mir_ctxt in
              let if_alloca_lval =
                {t=Ptr(t); kind=Tmp; lname=if_alloca_name}
              in
              let alloca_instr = Alloca(if_alloca_lval, t) in
              let bb = {bb with instrs = bb.instrs @ [alloca_instr]} in

              let do_store if_branch_lval =
                [Store(if_alloca_lval, if_branch_lval)]
              in

              let (mir_ctxt, (bb, then_bb, else_bb, end_bb)) =
                core_if_then_else_gen mir_ctxt bb do_store
              in

              let (mir_ctxt, if_res_varname) = get_varname mir_ctxt in
              let if_res_lval = {t=t; kind=Tmp; lname=if_res_varname} in
              let if_res_instr =
                Load(if_res_lval, if_alloca_lval)
              in
              let end_bb =
                {end_bb with instrs = end_bb.instrs @ [if_res_instr]}
              in

              (mir_ctxt, (bb, then_bb, else_bb, end_bb), if_res_lval)

            end
          in

          (* Update the MIR context with our updated versions of the basic
          blocks. *)
          let (mir_ctxt, _) =
            List.fold_left_map (
              fun mir_ctxt bb -> (update_bb mir_ctxt bb, ())
            ) mir_ctxt [bb; then_bb; else_bb; end_bb]
          in

          (mir_ctxt, end_bb, if_res_lval)

      | StaticIndexExpr(t, idx, exp) ->
          let (mir_ctxt, bb, agg_lval) = _expr_to_mir mir_ctxt bb exp in

          let (mir_ctxt, from_agg_varname) = get_varname mir_ctxt in
          let from_agg_lval = {t=t; kind=Tmp; lname=from_agg_varname} in
          let from_agg_instr = FromAggregate(from_agg_lval, idx, agg_lval) in

          let bb = {
            bb with instrs = bb.instrs @ [from_agg_instr]
          } in

          (mir_ctxt, bb, from_agg_lval)

      | VariantCtorExpr(variant_t, ctor_name, ctor_arg) ->
          let v_ctors = begin match variant_t with
          | Variant(_, v_ctors) -> v_ctors
          | _ -> failwith "Unexpected non-variant type in variant-ctor-expr"
          end in

          (* Assign the variant tag (first field in aggregate), based on the
          specific constructor we're building. *)
          let ctor_idx = get_tag_index_by_variant_ctor v_ctors ctor_name in
          let (mir_ctxt, bb, tag_lval) =
            ValU8(ctor_idx) |> literal_to_instr mir_ctxt bb U8
          in

          (* This constructor may have associated data. Assign it now. *)
          let ctor_t = expr_type ctor_arg in
          let (mir_ctxt, bb, ctor_lval, construct_instr) = begin
            match ctor_t with
            | Nil ->
                let variant_ctor_t = Tuple([U8]) in

                let (mir_ctxt, varname) = get_varname mir_ctxt in
                let ctor_lval =
                  {t=variant_ctor_t; kind=Tmp; lname=varname}
                in
                let construct_instr =
                  ConstructAggregate(ctor_lval, [tag_lval])
                in

                (mir_ctxt, bb, ctor_lval, construct_instr)

            | _ ->
                let variant_ctor_t = Tuple([U8; ctor_t]) in

                let (mir_ctxt, bb, ctor_elem_lval) =
                  _expr_to_mir mir_ctxt bb ctor_arg
                in

                let (mir_ctxt, varname) = get_varname mir_ctxt in
                let ctor_lval = {t=variant_ctor_t; kind=Tmp; lname=varname} in
                let construct_instr =
                  ConstructAggregate(ctor_lval, [tag_lval; ctor_elem_lval])
                in

                (mir_ctxt, bb, ctor_lval, construct_instr)
          end in

          let bb = {bb with instrs = bb.instrs @ [construct_instr]} in

          (mir_ctxt, bb, ctor_lval)

      | MatchExpr(t, matched_exp, patts_to_exps) ->
          let (mir_ctxt, bb, matched_lval) =
            _expr_to_mir mir_ctxt bb matched_exp
          in

          (* Allocate a "first" and "last" block. The first block will be used
          to get the ball rolling on codegen for match arms, and the last block
          is what each of the arms will branch to after they're complete. *)
          let (mir_ctxt, bb_patt_first_name) = get_bbname mir_ctxt in
          let bb_patt_first = {name=bb_patt_first_name; instrs=[]} in

          let (mir_ctxt, bb_end_name) = get_bbname mir_ctxt in
          let bb_end = {name=bb_end_name; instrs=[]} in

          (* Depending on whether this is truly a match expression, yielding
          a value, or instead a match "stmt", yielding nothing, we decide
          whether we need to allocate/store/load anything. *)
          let (
            mir_ctxt,
            maybe_alloca,
            do_maybe_store,
            maybe_load,
            match_res_lval
          ) =
            begin match t with
              | Nil ->
                  let (mir_ctxt, bb, nil_lval) =
                    _expr_to_mir mir_ctxt bb ValNil
                  in

                  let mir_ctxt = update_bb mir_ctxt bb in

                  (mir_ctxt, [], (fun _ -> []), [], nil_lval)

              | _ ->
                  (* Alloca for the match expr result to be written into. *)
                  let (mir_ctxt, match_alloca_name) = get_varname mir_ctxt in
                  let match_alloca_lval =
                    {t=Ptr(t); kind=Tmp; lname=match_alloca_name}
                  in
                  let maybe_alloca = [Alloca(match_alloca_lval, t)] in

                  let do_maybe_store then_lval =
                    [Store(match_alloca_lval, then_lval)]
                  in

                  let (mir_ctxt, match_res_name) = get_varname mir_ctxt in
                  let match_res_lval = {t=t; kind=Tmp; lname=match_res_name} in

                  let maybe_load = [Load(match_res_lval, match_alloca_lval)] in

                  (
                    mir_ctxt,
                    maybe_alloca,
                    do_maybe_store,
                    maybe_load,
                    match_res_lval
                  )
            end
          in

          let bb = {
            bb with instrs = bb.instrs @ maybe_alloca @ [Br(bb_patt_first)]
          } in
          let mir_ctxt = update_bb mir_ctxt bb in

          let gen_patt_arms mir_ctxt bb_patt_first bb_end patts_to_exps =
            (* Returns mir_ctxt. Any other blocks are expected to have already
            been updated into the mir_ctxt. *)
            let rec _gen_patt_arms mir_ctxt bb_patt patts_to_exps_rest =
              begin match patts_to_exps_rest with
              | [] -> mir_ctxt
              | [(patt, exp)] ->
                  (* Since this is the last pattern, both the "then" and the
                  "else" case both branch to the "end" block. The "else"
                  case should be impossible. *)

                  (* TODO: Teach this to make attempting to branch to the
                  "else", which should be impossible, instead cause a halt. *)
                  let mir_ctxt = pattern_to_mir
                    mir_ctxt
                    bb_patt
                    bb_end
                    bb_end
                    matched_lval
                    patt
                    exp
                    do_maybe_store
                  in
                  _gen_patt_arms mir_ctxt bb_end []

              | (patt, exp)::y::zs ->
                  (* We should be given the "then" bb and need to generate
                  an "else" bb. *)
                  let (mir_ctxt, bb_else_name) = get_bbname mir_ctxt in
                  let bb_else = {name=bb_else_name; instrs=[]} in

                  let mir_ctxt = pattern_to_mir
                    mir_ctxt
                    bb_patt
                    bb_else
                    bb_end
                    matched_lval
                    patt
                    exp
                    do_maybe_store
                  in
                  _gen_patt_arms mir_ctxt bb_else (y::zs)
              end
            in
            _gen_patt_arms mir_ctxt bb_patt_first patts_to_exps
          in

          let mir_ctxt =
            gen_patt_arms mir_ctxt bb_patt_first bb_end patts_to_exps
          in

          let bb_end =
            {bb_end with instrs = bb_end.instrs @ maybe_load}
          in

          (mir_ctxt, bb_end, match_res_lval)

      | WhileExpr(_, _, _, _)
      | IndexExpr(_, _, _) ->
          failwith "Unimplemented"
    end in

    (mir_ctxt, bb, instr)
  in

  _expr_to_mir mir_ctxt bb exp


(* bb_patt is the pre-created block to (start with) being populated with the
logic for whether this particular pattern matches the input lval. bb_else is
where to branch to if the pattern does not match. bb_end is where to branch if
the pattern does match.

This function is expected to internally generate any blocks needed to capture
generated MIR for the expression associated with the matched pattern, and the
caller should not need to care about them.

FIXME: It probably makes more sense for this function _not_ to take a bb_else,
and instead return the bb that requires being appended with the branch to the
bb_else that is known only to the caller.

TODO: This will probably need to become smarter if we want to re-use this for
things like `if let`, `while let`, and `for let`. *)
and pattern_to_mir
  mir_ctxt bb_patt bb_else bb_end matched_lval patt exp do_maybe_store
=
  let rec pattern_breakdown_mir mir_ctxt bb_patt bb_else matched_lval patt =
    let {t=matched_t; _} = matched_lval in
    begin match patt with
    | Wild(_) | PNil ->
        let (mir_ctxt, bb_patt, unconditional_match_lval) =
          expr_to_mir mir_ctxt bb_patt (ValBool(true))
        in
        (mir_ctxt, bb_patt, unconditional_match_lval)

    | VarBind(_, ident) ->
        let (mir_ctxt, bb_patt) =
          assign_rhs_to_decl mir_ctxt bb_patt ident matched_lval matched_t
        in
        let (mir_ctxt, bb_patt, unconditional_match_lval) =
          expr_to_mir mir_ctxt bb_patt (ValBool(true))
        in
        (mir_ctxt, bb_patt, unconditional_match_lval)

    | PatternAs(_, patt, ident) ->
        let (mir_ctxt, bb_patt) =
          assign_rhs_to_decl mir_ctxt bb_patt ident matched_lval matched_t
        in

        let (mir_ctxt, bb_patt, is_match_lval) =
          pattern_breakdown_mir mir_ctxt bb_patt bb_else matched_lval patt
        in

        (mir_ctxt, bb_patt, is_match_lval)

    | PBool(b) ->
        let (mir_ctxt, bb_patt, b_lval) =
          expr_to_mir mir_ctxt bb_patt (ValBool(b))
        in

        let (mir_ctxt, bool_patt_lname) = get_varname mir_ctxt in
        let is_match_lval = {t=Bool; kind=Tmp; lname=bool_patt_lname} in
        let instr = BinOp(is_match_lval, Eq, b_lval, matched_lval) in

        let bb_patt = {bb_patt with instrs=bb_patt.instrs @ [instr]} in

        (mir_ctxt, bb_patt, is_match_lval)

    | PTuple(t, patts) ->
        (* Extract the types out so we can deconstruct the tuple. *)
        let tuple_elem_ts = begin match t with
          | Tuple(ts) -> ts
          | _ -> failwith "Typecheck failure deconstructing aggr in MIR"
        end in

        (* Get raw lval objects, which will be associated with deconstructing
        the tuple below. *)
        let (mir_ctxt, tuple_elem_lvals) =
          List.fold_left_map (
            fun mir_ctxt elem_t ->
              let (mir_ctxt, varname) = get_varname mir_ctxt in
              let elem_lval = {lname=varname; t=elem_t; kind=Tmp} in

              (mir_ctxt, elem_lval)
          ) mir_ctxt tuple_elem_ts
        in

        (* Deconstruct the tuple into the lvals we declared. *)
        let extract_instrs =
          List.mapi (
            fun i lval ->
              let decon_instr = FromAggregate(lval, i, matched_lval) in

              decon_instr
          ) tuple_elem_lvals
        in

        let bb_patt =
          {bb_patt with instrs = bb_patt.instrs @ extract_instrs}
        in

        let lvals_patts = List.combine tuple_elem_lvals patts in

        (* To start our chain of recursive evaluations of the patterns within
        the tuple pattern, we begin with an "unconditionally true" success
        lval (which will get optimized out in LLVM). *)
        let (mir_ctxt, bb_patt, unconditional_match_lval) =
          expr_to_mir mir_ctxt bb_patt (ValBool(true))
        in

        let (mir_ctxt, bb_patt, is_match_lval) =
          List.fold_left (
            fun (mir_ctxt, bb_patt, match_lval) (elem_lval, patt) ->
              (* Make a new bb for considering this part of the tuple
              pattern, that we'll branch to from the previous part if we've
              matched so far. *)
              let (mir_ctxt, bb_tuple_part_name) = get_bbname mir_ctxt in
              let bb_tuple_part = {name=bb_tuple_part_name; instrs=[]} in

              let cond_br = CondBr(match_lval, bb_tuple_part, bb_else) in

              let bb_patt = {
                bb_patt with instrs = bb_patt.instrs @ [cond_br]
              } in
              let mir_ctxt = update_bb mir_ctxt bb_patt in

              let (mir_ctxt, bb_tuple_part, is_match_lval) =
                pattern_breakdown_mir
                  mir_ctxt bb_tuple_part bb_else elem_lval patt
              in

              (mir_ctxt, bb_tuple_part, is_match_lval)
          ) (mir_ctxt, bb_patt, unconditional_match_lval) lvals_patts
        in

        (mir_ctxt, bb_patt, is_match_lval)

    | Ctor(t, ctor_name, patt) ->
        let v_ctors = begin match t with
        | Variant(_, v_ctors) -> v_ctors
        | _ -> failwith "Unexpected non-variant type in variant-ctor-patt"
        end in

        (* Assign the variant tag (first field in aggregate), based on the
        specific constructor we're building. *)
        let ctor_idx_expected =
          get_tag_index_by_variant_ctor v_ctors ctor_name
        in
        let (mir_ctxt, bb_patt, tag_expected_lval) =
          ValU8(ctor_idx_expected) |> literal_to_instr mir_ctxt bb_patt U8
        in

        (* Extract the variant tag, that we know is at index 0 of a variant
        constructor "struct". *)
        let (mir_ctxt, tag_actual_lname) = get_varname mir_ctxt in
        let tag_actual_lval = {t=U8; kind=Tmp; lname=tag_actual_lname} in
        let tag_actual_instr =
          FromAggregate(tag_actual_lval, 0, matched_lval)
        in

        let (mir_ctxt, tag_match_lname) = get_varname mir_ctxt in
        let tag_match_lval = {t=U8; kind=Tmp; lname=tag_match_lname} in
        let tag_match_instr =
          BinOp(tag_match_lval, Eq, tag_actual_lval, tag_expected_lval)
        in

        (* Make a new bb for considering the sub-pattern of the ctor. *)
        let (mir_ctxt, bb_ctor_subpatt_name) = get_bbname mir_ctxt in
        let bb_ctor_subpatt = {name=bb_ctor_subpatt_name; instrs=[]} in

        let cond_br_instr = CondBr(tag_match_lval, bb_ctor_subpatt, bb_else) in

        let bb_patt = {
          bb_patt with instrs=bb_patt.instrs @ [
            tag_actual_instr;
            tag_match_instr;
            cond_br_instr
          ]
        } in

        let mir_ctxt = update_bb mir_ctxt bb_patt in

        (* We need to extract the value out of the constructor, if there is one,
        so we can continue the match. *)
        let (_, ctor_val_t) =
          List.find (fun (name, _) -> name = ctor_name) v_ctors
        in

        let (mir_ctxt, bb_ctor_subpatt, is_match_lval) = begin
          match ctor_val_t with
          | Nil ->
              let (mir_ctxt, nil_dummy_lname) = get_varname mir_ctxt in
              let nil_dummy_lval = {t=Nil; kind=Tmp; lname=nil_dummy_lname} in

              let (mir_ctxt, bb_ctor_subpatt, is_match_lval) =
                pattern_breakdown_mir
                  mir_ctxt bb_ctor_subpatt bb_else nil_dummy_lval patt
              in

              (mir_ctxt, bb_ctor_subpatt, is_match_lval)

          | _ ->
              Printf.printf "Matched_t: [[ %s ]]\n" (fmt_type matched_t) ;

              let (mir_ctxt, generic_ctor_val_lname) = get_varname mir_ctxt in
              (* FIXME: This probably isn't right; this should be the type of
              the generic [N x i8] array of non-zero data contained in the ctor,
              before it's bitcasted to its real type. *)
              let generic_ctor_val_lval =
                {t=ctor_val_t; kind=Tmp; lname=generic_ctor_val_lname}
              in
              let generic_ctor_val_instr =
                FromAggregate(generic_ctor_val_lval, 1, matched_lval)
              in

              (* At this point we have an [N x i8] array aggregate, but we need
              to be able to bitcast it to the type we actually need it to be.
              Since LLVM does not allow bitcasting non-pointers, we need to
              "pointlessly" push our generic data array into an alloca, so we
              can bitcast the ptr to the alloca and then extract the data back
              out in the right type. *)

              (* TODO: We need to figure out how to get the type of the generic
              array aggregate containing the ctor value. *)
              let generic_ctor_val_t = ByteArray(ctor_val_t) in

              (* let generic_ctor_val_t = ctor_val_t in *)

              let (mir_ctxt, ctor_val_alloca_lname) = get_varname mir_ctxt in
              let generic_ctor_val_alloca_lval = {
                  t=Ptr(generic_ctor_val_t);
                  kind=Tmp;
                  lname=ctor_val_alloca_lname
              } in
              let generic_ctor_val_alloca_instr =
                Alloca(generic_ctor_val_alloca_lval, generic_ctor_val_t)
              in

              let generic_ctor_val_store_instr =
                Store(generic_ctor_val_alloca_lval, generic_ctor_val_lval)
              in

              let (mir_ctxt, ctor_val_bitcast_lname) = get_varname mir_ctxt in
              let ctor_val_bitcast_lval =
                {t=Ptr(ctor_val_t); kind=Tmp; lname=ctor_val_bitcast_lname}
              in
              let ctor_val_bitcast_instr =
                UnOp(
                  ctor_val_bitcast_lval, Bitwise, generic_ctor_val_alloca_lval
                )
              in

              let (mir_ctxt, ctor_val_load_lname) = get_varname mir_ctxt in
              let ctor_val_lval =
                {t=ctor_val_t; kind=Tmp; lname=ctor_val_load_lname}
              in
              let ctor_val_load_instr =
                Load(ctor_val_lval, ctor_val_bitcast_lval)
              in

              let bb_ctor_subpatt = {
                bb_ctor_subpatt with instrs=bb_ctor_subpatt.instrs @ [
                  generic_ctor_val_instr;
                  generic_ctor_val_alloca_instr;
                  generic_ctor_val_store_instr;
                  ctor_val_bitcast_instr;
                  ctor_val_load_instr;
                ]
              } in

              let mir_ctxt = update_bb mir_ctxt bb_ctor_subpatt in

              let (mir_ctxt, bb_ctor_subpatt, is_match_lval) =
                pattern_breakdown_mir
                  mir_ctxt bb_ctor_subpatt bb_else ctor_val_lval patt
              in

              (mir_ctxt, bb_ctor_subpatt, is_match_lval)
        end in

        (mir_ctxt, bb_ctor_subpatt, is_match_lval)

    end in

    let (mir_ctxt, bb_patt, is_match_lval) =
      pattern_breakdown_mir mir_ctxt bb_patt bb_else matched_lval patt
    in

    (* If match, then branch to new expr bb, else branch to bb_else *)

    let (mir_ctxt, bb_then_name) = get_bbname mir_ctxt in
    let bb_then = {name=bb_then_name; instrs=[]} in

    let cond_br = CondBr(is_match_lval, bb_then, bb_else) in
    let bb_patt = {bb_patt with instrs = bb_patt.instrs @ [cond_br]} in

    let (mir_ctxt, bb_then, then_lval) = expr_to_mir mir_ctxt bb_then exp in

    let maybe_store = do_maybe_store then_lval in

    let bb_then = {
      bb_then with instrs = bb_then.instrs @ maybe_store @ [Br(bb_end)]
    } in

    let mir_ctxt = update_bb mir_ctxt bb_patt in
    let mir_ctxt = update_bb mir_ctxt bb_then in

    (* Strictly speaking this should not need to be necessary, as the "else"
    bb will (should) always be passed in as a "then" bb on the next iteration
    of this function, where the base case is the else block at the end, which
    is just handled (eventually) by the caller as normal. We include this
    update here really just so there's a place to put this comment. *)
    let mir_ctxt = update_bb mir_ctxt bb_else in

    mir_ctxt


and assign_rhs_to_decl mir_ctxt bb lhs_name rhs_lval expected_t =
  let (mir_ctxt, bb, alloca_lval) =
    lval_to_alloca mir_ctxt bb rhs_lval expected_t
  in

  let lval = {t=Ptr(expected_t); kind=Var; lname=lhs_name} in
  let assign_instr = Assign(lval, RVar(alloca_lval)) in

  let mir_ctxt = {
    mir_ctxt with lvars = StrMap.add lhs_name lval mir_ctxt.lvars
  } in

  let bb = {bb with instrs = bb.instrs @ [assign_instr]} in

  (mir_ctxt, bb)


and stmt_to_mir (mir_ctxt : mir_ctxt) (bb : bb) (stmt : Ast.stmt) =
  let _stmt_to_mir
    (mir_ctxt: mir_ctxt) (bb: bb) (stmt: Ast.stmt) : (mir_ctxt * bb)
  =

    match stmt with
    | ExprStmt(exp) ->
        let (mir_ctxt, bb, _) = expr_to_mir mir_ctxt bb exp in

        (mir_ctxt, bb)

    | DeclStmt(lhs_name, _, t, exp) ->
        let (mir_ctxt, bb, rhs_lval) = expr_to_mir mir_ctxt bb exp in

        let (mir_ctxt, bb) =
          assign_rhs_to_decl mir_ctxt bb lhs_name rhs_lval t
        in

        let mir_ctxt = update_bb mir_ctxt bb in

        (mir_ctxt, bb)

    | DeclDeconStmt(ident_quals, t, exp) ->
        let (mir_ctxt, bb, aggregate_lval) = expr_to_mir mir_ctxt bb exp in

        let idents = List.map (fun (ident, _) -> ident) ident_quals in
        let decon_sz = List.length idents in

        let aggregate_types = begin match t with
          | Array(t, _) -> List.init decon_sz (fun _ -> t)
          | Tuple(ts) -> ts
          | _ -> failwith "Typecheck failure deconstructing aggr in MIR"
        end in

        let (mir_ctxt, elem_lvals) =
          List.fold_left_map (
            fun mir_ctxt elem_t ->
              let (mir_ctxt, varname) = get_varname mir_ctxt in
              let elem_lval = {lname=varname; t=elem_t; kind=Tmp} in

              (mir_ctxt, elem_lval)
          ) mir_ctxt aggregate_types
        in

        let extract_instrs =
          List.mapi (
            fun i lval ->
              let decon_instr = FromAggregate(lval, i, aggregate_lval) in

              decon_instr
          ) elem_lvals
        in

        let bb = {bb with instrs = bb.instrs @ extract_instrs} in

        let idents_lvals_ts = combine3 idents elem_lvals aggregate_types in

        let (mir_ctxt, bb) =
          List.fold_left (
            fun (mir_ctxt, bb) (lhs_name, rhs_lval, elem_t) ->
              assign_rhs_to_decl mir_ctxt bb lhs_name rhs_lval elem_t
          ) (mir_ctxt, bb) idents_lvals_ts
        in

        let mir_ctxt = update_bb mir_ctxt bb in

        (mir_ctxt, bb)

    | ReturnStmt(exp) ->
        let (mir_ctxt, bb, ret_lval) = expr_to_mir mir_ctxt bb exp in

        let ret_instr = Ret(ret_lval) in

        let bb = {bb with instrs = bb.instrs @ [ret_instr]} in
        let mir_ctxt = update_bb mir_ctxt bb in

        (mir_ctxt, bb)

    | _ -> failwith "Unimplemented"
  in

  _stmt_to_mir mir_ctxt bb stmt

let func_to_mir {f_decl = {f_name; f_params; f_ret_t}; f_stmts} =
  let mir_ctxt = {
    f_name = f_name;
    f_params = (List.map (fun (param_name, _, t) -> (param_name, t)) f_params);
    f_ret_t = f_ret_t;
    name_gen = 0;
    lvars = StrMap.empty;
    bbs = StrMap.empty
  } in
  let bb_entry = {name="entry"; instrs=[]} in
  let ((mir_ctxt, _), _) =
    List.fold_left_map (
      fun (mir_ctxt, cur_bb) stmt ->
        let (mir_ctxt, cur_bb) = stmt_to_mir mir_ctxt cur_bb stmt in
        ((mir_ctxt, cur_bb), ())
    ) (mir_ctxt, bb_entry) f_stmts
  in

  mir_ctxt

let func_decl_to_mir ({f_name; f_params; f_ret_t} : func_decl_t) =
  let mir_ctxt = {
    f_name = f_name;
    f_params = (List.map (fun (param_name, _, t) -> (param_name, t)) f_params);
    f_ret_t = f_ret_t;
    name_gen = 0;
    lvars = StrMap.empty;
    bbs = StrMap.empty
  } in

  mir_ctxt

