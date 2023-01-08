open Ast
open Ir
open Typing
open Utility

module StrMap = Map.Make(String)

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
(* Turn a list of separate values into a struct containing those values, whose
members are in the same order as the given list. *)
| ConstructAggregate of lval * lval list
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
  | ValStr(str) -> sprintf "\"%s\"" str
  | ValFunc(func_name) -> sprintf "fn<%s>" func_name

let fmt_lval ({t; kind; lname} : lval) =
  Printf.sprintf "%s<%s>: %s" lname (fmt_lval_kind kind) (fmt_type t)

let fmt_rval rval =
  match rval with
  | Constant(constant) -> fmt_constant constant
  | RVar(lval) -> fmt_lval lval

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

  | ConstructAggregate(lval, elems) ->
      sprintf "  %s = aggregate of (%s)\n"
        (fmt_lval lval)
        (fmt_join_strs "; "(List.map fmt_lval elems))

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

let fmt_mir_ctxt {f_name; f_params; f_ret_t; bbs; _} =
  let open Printf in
  let bbs = List.map (fun (_, bb) -> bb) (StrMap.bindings bbs) in
  let f_params_fmted =
    fmt_join_strs ", " (
      List.map (fun (n, t) -> sprintf "%s: %s" n (fmt_type t)) f_params
    )
  in

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

let get_bbname mir_ctxt : (mir_ctxt * string) =
  (
    {mir_ctxt with name_gen = mir_ctxt.name_gen + 1},
    Printf.sprintf "bb_%d" mir_ctxt.name_gen
  )

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
  | ConstructAggregate(lval, _) -> lval
  | FromAggregate(lval, _, _) -> lval
  | Call(lval, _, _) -> lval
  | CallVoid(_, _) -> failwith "No resultant lval for void call"
  | CondBr(_, _, _) -> failwith "No resultant lval for condbr"
  | Ret(_) -> failwith "No resultant lval for ret"
  | Br(_) -> failwith "No resultant lval for br"
  | RetVoid -> failwith "No resultant lval for ret (void)"

let rec expr_to_mir (mir_ctxt : mir_ctxt) (bb : bb) (exp : Ast.expr) =
  let rec _expr_to_mir
    (mir_ctxt : mir_ctxt) (bb : bb) (exp : Ast.expr) : (mir_ctxt * bb * lval)
  =
    let literal_to_instr mir_ctxt bb ctor =
      let (mir_ctxt, varname) = get_varname mir_ctxt in
      let t = expr_type exp in
      let lval = {t=t; kind=Tmp; lname=varname} in
      let instr = Assign(lval, Constant(ctor)) in
      let bb = {bb with instrs=bb.instrs @ [instr]} in
      (mir_ctxt, bb, lval)
    in

    let (mir_ctxt, bb, instr) = begin match exp with
      | ValNil -> ValNil |> literal_to_instr mir_ctxt bb

      | ValBool(b) -> ValBool(b) |> literal_to_instr mir_ctxt bb

      | ValU8 (x) -> ValU8(x)  |> literal_to_instr mir_ctxt bb
      | ValU16(x) -> ValU16(x) |> literal_to_instr mir_ctxt bb
      | ValU32(x) -> ValU32(x) |> literal_to_instr mir_ctxt bb
      | ValU64(x) -> ValU64(x) |> literal_to_instr mir_ctxt bb

      | ValI8 (x) -> ValI8 (x) |> literal_to_instr mir_ctxt bb
      | ValI16(x) -> ValI16(x) |> literal_to_instr mir_ctxt bb
      | ValI32(x) -> ValI32(x) |> literal_to_instr mir_ctxt bb
      | ValI64(x) -> ValI64(x) |> literal_to_instr mir_ctxt bb

      | ValF32(f) -> ValF32(f) |> literal_to_instr mir_ctxt bb
      | ValF64(f) -> ValF64(f) |> literal_to_instr mir_ctxt bb
      | ValF128(str) -> ValF128(str) |> literal_to_instr mir_ctxt bb

      | ValStr(str) -> ValStr(str) |> literal_to_instr mir_ctxt bb

      | ValFunc(_, func_name) ->
          ValFunc(func_name) |> literal_to_instr mir_ctxt bb

      | ValVar(_, varname) ->
          (* For variable access in MIR, we just want to yield the lvar that
          should already exist for this name. *)
          let var_value = StrMap.find varname mir_ctxt.lvars in

          (mir_ctxt, bb, var_value)

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
          let (mir_ctxt, bb, to_bitwise_lval) = _expr_to_mir mir_ctxt bb exp in

          let (mir_ctxt, varname) = get_varname mir_ctxt in
          let lval = {t=t; kind=Tmp; lname=varname} in
          let instr = UnOp(lval, Extend, to_bitwise_lval) in

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
          let ((mir_ctxt, bb), arg_values) =
            List.fold_left_map (
              fun (mir_ctxt, bb) exp ->
                let (mir_ctxt, bb, arg_val) = _expr_to_mir mir_ctxt bb exp in
                ((mir_ctxt, bb), arg_val)
            ) (mir_ctxt, bb) exprs
          in

          (* For variable access in MIR, we just want to yield the lvar that
          should already exist for this name. *)
          let func_lval = StrMap.find varname mir_ctxt.lvars in

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

      | WhileExpr(_, _, _, _)
      | IndexExpr(_, _, _)
      | VariantCtorExpr(_, _, _) ->
          failwith "Unimplemented"
    end in

    (mir_ctxt, bb, instr)
  in

  _expr_to_mir mir_ctxt bb exp

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

        let lval = {t=t; kind=Var; lname=lhs_name} in
        let assign_instr = Assign(lval, RVar(rhs_lval)) in

        let mir_ctxt = {
          mir_ctxt with lvars = StrMap.add lhs_name lval mir_ctxt.lvars
        } in

        let bb = {bb with instrs = bb.instrs @ [assign_instr]} in
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

        let elem_lvals =
          List.map2 (
            fun ident elem_t -> {lname=ident; t=elem_t; kind=Var}
          ) idents aggregate_types
        in

        let extract_instrs =
          List.mapi (
            fun i lval ->
              let decon_instr = FromAggregate(lval, i, aggregate_lval) in

              decon_instr
          ) elem_lvals
        in

        let idents_lvals = List.combine idents elem_lvals in

        let (mir_ctxt, _) =
          List.fold_left_map (
            fun mir_ctxt (ident, lval) ->
              let mir_ctxt = {
                mir_ctxt with lvars = StrMap.add ident lval mir_ctxt.lvars
              } in
              (mir_ctxt, ())
          ) mir_ctxt idents_lvals
        in

        let bb = {bb with instrs = bb.instrs @ extract_instrs} in
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
    name_gen = 0; lvars = StrMap.empty; bbs = StrMap.empty
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

