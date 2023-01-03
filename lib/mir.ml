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
| RVar of string

type mutability =
| Mutable
| Immutable

type lval_kind =
| Var
| Arg
| Tmp

(* RHS of an instruction. *)
type rhs =
| Use of rval
| BinOp of bin_op * rval * rval
| UnOp of un_op * rval

(* Lvalues, which can be assigned to and can be read in the RHS. *)
and lval = {
  t: berk_t;
  kind: lval_kind;
  mut: mutability;
  lname: string;
  rhs: rhs;
}

(* Instruction *)
type instr =
| Assign of lval
| Br of bb
| CondBr of lval * bb * bb
| RetVoid
| Ret of lval

and bb = {
  name: string;
  instrs: instr list;
}

type mir_ctxt = {
  name_gen: int;
  lvars: lval StrMap.t;
}

let get_varname ?(prefix="") mir_ctxt : (mir_ctxt * string) = (
  let prefix = if String.length prefix > 0 then prefix else "__tmp" in
  (
    {mir_ctxt with name_gen = mir_ctxt.name_gen + 1},
    Printf.sprintf "%s_%d" prefix mir_ctxt.name_gen
  )
)

let expr_to_mir (mir_ctxt : mir_ctxt) (exp : Ast.expr) =
  let rec _expr_to_mir
    (mir_ctxt : mir_ctxt) (exp : Ast.expr) : (mir_ctxt * lval)
  =
    let literal_to_lval mir_ctxt ctor =
      let (mir_ctxt, varname) = get_varname mir_ctxt in
      let t = expr_type exp in
      let lval = {
        t=t; kind=Tmp; mut=Immutable; lname=varname; rhs=Use(Constant(ctor))
      } in
      (mir_ctxt, lval)
    in

    match exp with
    | ValNil -> literal_to_lval mir_ctxt ValNil

    | ValU8 (x) -> ValU8(x)  |> literal_to_lval mir_ctxt
    | ValU16(x) -> ValU16(x) |> literal_to_lval mir_ctxt
    | ValU32(x) -> ValU32(x) |> literal_to_lval mir_ctxt
    | ValU64(x) -> ValU64(x) |> literal_to_lval mir_ctxt

    | ValI8 (x) -> ValI8 (x) |> literal_to_lval mir_ctxt
    | ValI16(x) -> ValI16(x) |> literal_to_lval mir_ctxt
    | ValI32(x) -> ValI32(x) |> literal_to_lval mir_ctxt
    | ValI64(x) -> ValI64(x) |> literal_to_lval mir_ctxt

    | ValF32(f) -> ValF32(f) |> literal_to_lval mir_ctxt
    | ValF64(f) -> ValF64(f) |> literal_to_lval mir_ctxt
    | ValF128(str) -> ValF128(str) |> literal_to_lval mir_ctxt

    | BinOp(t, op, lhs, rhs) ->
        let (mir_ctxt, {lname=lhs_n; _}) = _expr_to_mir mir_ctxt lhs in
        let (mir_ctxt, {lname=rhs_n; _}) = _expr_to_mir mir_ctxt rhs in
        let (mir_ctxt, varname) = get_varname mir_ctxt in
        let lval = {
          t=t; kind=Tmp; mut=Immutable; lname=varname;
          rhs=BinOp(op, RVar(lhs_n), RVar(rhs_n))
        } in

        (mir_ctxt, lval)

    | _ -> failwith "Unimplemented"
  in

  _expr_to_mir mir_ctxt exp

let stmt_to_mir (mir_ctxt : mir_ctxt) (stmt : Ast.stmt) =
  let _stmt_to_mir
    (mir_ctxt : mir_ctxt) (stmt : Ast.stmt) : (mir_ctxt * instr)
  =
    match stmt with
    | DeclStmt(lhs_name, {mut}, t, exp) ->
        let (mir_ctxt, {lname=rhs_name; _}) = expr_to_mir mir_ctxt exp in

        let is_mut = if mut then Mutable else Immutable in
        let lval =
          {t=t; kind=Var; mut=is_mut; lname=lhs_name; rhs=Use(RVar(rhs_name))}
        in

        let mir_ctxt = {
          mir_ctxt with lvars = StrMap.add lhs_name lval mir_ctxt.lvars
        } in

        (mir_ctxt, Assign(lval))

    | _ -> failwith "Unimplemented"
  in

  _stmt_to_mir mir_ctxt stmt

let func_to_mir {f_stmts; _} =
  let mir_ctxt = {name_gen=0; lvars = StrMap.empty} in
  let (_, _) =
    List.fold_left_map (
      fun mir_ctxt stmt ->
        let (mir_ctxt, instr) = stmt_to_mir mir_ctxt stmt in
        (mir_ctxt, instr)
    ) mir_ctxt f_stmts
  in
  ()

