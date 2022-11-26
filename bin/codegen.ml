open Ast


let rec codegen_expr context builder expr =
  let i64_t = Llvm.i64_type context in
  let i32_t = Llvm.i32_type context in
  let bool_t = Llvm.i8_type context in
  let _codegen_expr = codegen_expr context builder in

  match expr with
  | ValI64(n) -> Llvm.const_int i64_t n
  | ValI32(n) -> Llvm.const_int i32_t n
  | ValBool(false) -> Llvm.const_int bool_t 0
  | ValBool(true)  -> Llvm.const_int bool_t 1
  | Add(lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      Llvm.build_add lhs_val rhs_val "addtmp" builder
  | Sub(lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      Llvm.build_sub lhs_val rhs_val "addtmp" builder
  | Mul(lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      Llvm.build_mul lhs_val rhs_val "addtmp" builder
  | IfExpr((* {
      if_block = {cond = if_cond; stmts = if_stmts};
      else_if_blocks;
      else_block;
    } *) _ ) -> failwith "not implemented"
;;
