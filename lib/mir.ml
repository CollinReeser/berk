open Ast
open Typing
open Ir

module StrMap = Map.Make(String)

(* The MIR (mid-level intermediate representation) is a lowering of the
high-level AST (or HIR). This provides a reduced-complexity but computationally
equivalent version of the input program, which is easier to process. *)

type constant =
| ValNil
| ValU8 of int | ValU16 of int | ValU32 of int | ValU64 of int
| ValI8 of int | ValI16 of int | ValI32 of int | ValI64 of int
| ValF32 of float | ValF64 of float
| ValF128 of string
| ValBool of bool
| ValString of string

(* Components of an instruction RHS. *)
type rval =
| Constant of constant
| RVar of lval

(* Lvalues, which can be assigned to and can be read in the RHS. *)
and lval = {
  t: berk_t;
  kind: lval_kind;
  lname: string;
}

and lval_kind =
| Var
| Arg
| Tmp

(* Instruction *)
type instr =
| Alloca of lval
| Store of lval * rval
| Load of lval * lval
| Assign of lval * rval
| BinOp of lval * bin_op * rval * rval
| UnOp of lval * un_op * rval
| Br of bb
| CondBr of lval * bb * bb
| RetVoid
| Ret of rval

and bb = {
  name: string;
  instrs: instr list;
}

type mir_ctxt = {
  name_gen: int;
  lvars: lval StrMap.t;
  bbs: bb StrMap.t;
}

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

let instr_lval instr =
  match instr with
  | Assign(lval, _) -> lval
  | Alloca(lval) -> lval
  | Store(lval, _) -> lval
  | Load(lval, _) -> lval
  | BinOp(lval, _, _, _) -> lval
  | UnOp(lval, _, _) -> lval
  | CondBr(_, _, _) -> failwith "No resultant lval for condbr"
  | Ret(_) -> failwith "No resultant lval for ret"
  | Br(_) -> failwith "No resultant lval for br"
  | RetVoid -> failwith "No resultant lval for ret (void)"

let expr_to_mir (mir_ctxt : mir_ctxt) (bb : bb) (exp : Ast.expr) =
  let rec _expr_to_mir
    (mir_ctxt : mir_ctxt) (bb : bb) (exp : Ast.expr) : (mir_ctxt * bb * instr)
  =
    let literal_to_instr mir_ctxt bb ctor =
      let (mir_ctxt, varname) = get_varname mir_ctxt in
      let t = expr_type exp in
      let lval = {t=t; kind=Tmp; lname=varname} in
      let instr = Assign(lval, Constant(ctor)) in
      let bb = {bb with instrs=bb.instrs @ [instr]} in
      (mir_ctxt, bb, instr)
    in

    let (mir_ctxt, bb, instr) = begin match exp with
      | ValNil -> ValNil |> literal_to_instr mir_ctxt bb

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

      | BinOp(t, op, lhs, rhs) ->
          let (mir_ctxt, bb, lhs_instr) = _expr_to_mir mir_ctxt bb lhs in
          let (mir_ctxt, bb, rhs_instr) = _expr_to_mir mir_ctxt bb rhs in
          let lhs_lval = instr_lval lhs_instr in
          let rhs_lval = instr_lval rhs_instr in
          let (mir_ctxt, varname) = get_varname mir_ctxt in

          let lval = {t=t; kind=Tmp; lname=varname} in
          let instr = BinOp(lval, op, RVar(lhs_lval), RVar(rhs_lval)) in

          let bb = {bb with instrs=bb.instrs @ [instr]} in

          (mir_ctxt, bb, instr)

      | IfThenElseExpr(t, cond_expr, then_expr, else_expr) ->
          let core_if_then_else_gen mir_ctxt bb maybe_do_store =
            let (mir_ctxt, then_bb_name) = get_bbname mir_ctxt in
            let (mir_ctxt, else_bb_name) = get_bbname mir_ctxt in
            let (mir_ctxt, end_bb_name) = get_bbname mir_ctxt in
            let then_bb = {name=then_bb_name; instrs=[]} in
            let else_bb = {name=else_bb_name; instrs=[]} in
            let end_bb = {name=end_bb_name; instrs=[]} in

            let (mir_ctxt, bb, cond_instr) =
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

            let cond_lval = instr_lval cond_instr in
            let cond_br = CondBr(cond_lval, then_bb, else_bb) in
            let bb = {bb with instrs = bb.instrs @ [cond_br]} in

            (mir_ctxt, (bb, then_bb, else_bb, end_bb))
          in

          let (mir_ctxt, (bb, then_bb, else_bb, end_bb), if_res_instr) =
            begin match t with
            | Nil ->
              let no_store _ = [] in

              let (mir_ctxt, (bb, then_bb, else_bb, end_bb)) =
                core_if_then_else_gen mir_ctxt bb no_store
              in

              let (mir_ctxt, end_bb, nil_instr) =
                _expr_to_mir mir_ctxt end_bb ValNil
              in
              let end_bb =
                {end_bb with instrs = end_bb.instrs @ [nil_instr]}
              in

              (mir_ctxt, (bb, then_bb, else_bb, end_bb), nil_instr)

            | _ ->
              let (mir_ctxt, if_alloca_name) = get_varname mir_ctxt in
              let if_alloca_lval = {t=t; kind=Tmp; lname=if_alloca_name} in
              let alloca_instr = Alloca(if_alloca_lval) in
              let bb = {bb with instrs = bb.instrs @ [alloca_instr]} in

              let do_store if_branch_instr =
                let lval = instr_lval if_branch_instr in
                [Store(if_alloca_lval, RVar(lval))]
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

              (mir_ctxt, (bb, then_bb, else_bb, end_bb), if_res_instr)

            end
          in

          (* Update the MIR context with our updated versions of the basic
          blocks. *)
          let (mir_ctxt, _) =
            List.fold_left_map (
              fun mir_ctxt bb -> (update_bb mir_ctxt bb, ())
            ) mir_ctxt [bb; then_bb; else_bb; end_bb]
          in

          (mir_ctxt, end_bb, if_res_instr)


      | _ -> failwith "Unimplemented"
    end in

    (mir_ctxt, bb, instr)
  in

  _expr_to_mir mir_ctxt bb exp

let stmt_to_mir (mir_ctxt : mir_ctxt) (bb : bb) (stmt : Ast.stmt) =
  let _stmt_to_mir
    (mir_ctxt: mir_ctxt) (bb: bb) (stmt: Ast.stmt) : (mir_ctxt * bb * instr)
  =
    match stmt with
    | DeclStmt(lhs_name, _, t, exp) ->
        let (mir_ctxt, bb, instr) = expr_to_mir mir_ctxt bb exp in

        let lval = {t=t; kind=Var; lname=lhs_name} in
        let rhs_lval = instr_lval instr in
        let assign_instr = Assign(lval, RVar(rhs_lval)) in

        let mir_ctxt = {
          mir_ctxt with lvars = StrMap.add lhs_name lval mir_ctxt.lvars
        } in

        let bb = {bb with instrs = bb.instrs @ [assign_instr]} in
        let mir_ctxt = update_bb mir_ctxt bb in

        (mir_ctxt, bb, assign_instr)

    | _ -> failwith "Unimplemented"
  in

  _stmt_to_mir mir_ctxt bb stmt

let func_to_mir {f_stmts; _} =
  let mir_ctxt = {name_gen = 0; lvars = StrMap.empty; bbs = StrMap.empty} in
  let bb_entry = {name="entry"; instrs=[]} in
  let ((mir_ctxt, _), _) =
    List.fold_left_map (
      fun (mir_ctxt, cur_bb) stmt ->
        let (mir_ctxt, cur_bb, instr) = stmt_to_mir mir_ctxt cur_bb stmt in
        ((mir_ctxt, cur_bb), instr)
    ) (mir_ctxt, bb_entry) f_stmts
  in

  mir_ctxt

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
  | ValString(str) -> sprintf "\"%s\"" str

let fmt_lval ({t; kind; lname} : lval) =
  Printf.sprintf "%s<%s> of %s" lname (fmt_lval_kind kind) (fmt_type t)

let fmt_rval rval =
  match rval with
  | Constant(constant) -> fmt_constant constant
  | RVar(lval) -> fmt_lval lval

let fmt_instr instr =
  let open Printf in
  match instr with
  | Alloca(lval) ->
      let {t; kind; lname} = lval in
      sprintf "  %s = alloca<%s> %s\n" lname (fmt_lval_kind kind) (fmt_type t)

  | Store(lval, rval) ->
      let {t; kind; lname} = lval in
      sprintf "  store<%s> %s -> %s -> %s\n"
        (fmt_lval_kind kind)
        (fmt_rval rval)
        (fmt_type t)
        lname

  | Load(lval, rhs_lval) ->
      let {t; kind; lname} = lval in
      let {t=rhs_t; kind=rhs_kind; lname=rhs_lname} = rhs_lval in
      sprintf "  %s<%s>: %s = load %s<%s>: %s\n"
        lname
        (fmt_lval_kind kind)
        (fmt_type t)
        rhs_lname
        (fmt_lval_kind rhs_kind)
        (fmt_type rhs_t)

  | Assign(lval, rval) ->
      let {t; kind; lname} = lval in
      sprintf "  %s<%s>: %s = %s\n"
        lname
        (fmt_lval_kind kind)
        (fmt_type t)
        (fmt_rval rval)

  | BinOp(lval, op, lhs, rhs) ->
      let {t; kind; lname} = lval in
      sprintf "  %s<%s>: %s = %s%s%s\n"
        lname
        (fmt_lval_kind kind)
        (fmt_type t)
        (fmt_rval lhs)
        (fmt_bin_op op)
        (fmt_rval rhs)

  | UnOp(lval, un_op, rval) ->
      let fmt_un_op un_op = begin match un_op with
        | Truncate -> "truncate of"
        | Extend -> "extend of"
        | BitwiseCast -> "bitwise cast of"
      end in

      let {t; kind; lname} = lval in
      sprintf "  %s<%s>: %s = %s %s\n"
        lname
        (fmt_lval_kind kind)
        (fmt_type t)
        (fmt_un_op un_op)
        (fmt_rval rval)

  | Br({name; _}) ->
      sprintf "  unconditional branch to %s\n" name

  | CondBr(lval, {name=lhs_name; _}, {name=rhs_name; _}) ->
      let {t; kind; lname} = lval in
      sprintf "  branch on %s<%s>: %s among %s, %s\n"
        lname
        (fmt_lval_kind kind)
        (fmt_type t)
        lhs_name
        rhs_name

  | RetVoid -> sprintf "  ret (void)\n"
  | Ret(rval) ->
      sprintf "  ret %s\n" (fmt_rval rval)

let fmt_bb ({name; instrs} : bb) =
  Printf.sprintf "%s:\n%s"
    name
    (List.fold_left (^) "" (List.map fmt_instr instrs))

let fmt_mir_ctxt mir_ctxt =
  let bbs = List.map (fun (_, bb) -> bb) (StrMap.bindings mir_ctxt.bbs) in
  Printf.sprintf "%s"
    (List.fold_left (^) "" (List.map fmt_bb bbs))

let pprint_mir_ctxt ppf mir_ctxt =
  Format.fprintf ppf "%s" (fmt_mir_ctxt mir_ctxt)
