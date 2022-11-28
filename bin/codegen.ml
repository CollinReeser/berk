open Ast
open Pretty_print


let rec codegen_expr context builder expr =
  let i64_t = Llvm.i64_type context in
  let i32_t = Llvm.i32_type context in
  let f32_t = Llvm.float_type context in
  let bool_t = Llvm.i8_type context in
  let _codegen_expr = codegen_expr context builder in

  match expr with
  | ValI64(n) -> Llvm.const_int i64_t n
  | ValI32(n) -> Llvm.const_int i32_t n
  | ValF32(n) -> Llvm.const_float f32_t n
  | ValBool(false) -> Llvm.const_int bool_t 0
  | ValBool(true)  -> Llvm.const_int bool_t 1
  | BinOp(typ, op, lhs, rhs) ->
      let lhs_val = _codegen_expr lhs in
      let rhs_val = _codegen_expr rhs in
      begin match typ with
      | I64 | I32 ->
          begin match op with
          | Add -> Llvm.build_add lhs_val rhs_val "addtmp" builder
          | Sub -> Llvm.build_sub lhs_val rhs_val "addtmp" builder
          | Mul -> Llvm.build_mul lhs_val rhs_val "addtmp" builder
          end
      | F32 ->
          begin match op with
          | Add -> Llvm.build_fadd lhs_val rhs_val "addtmp" builder
          | Sub -> Llvm.build_fsub lhs_val rhs_val "addtmp" builder
          | Mul -> Llvm.build_fmul lhs_val rhs_val "addtmp" builder
          end
      | typ ->
        failwith (
          Printf.sprintf
            "Unexpected expression type in BinOp: %s" (fmt_type typ)
        )
      end
  | BlockExpr(_) -> failwith "not implemented"
  | IfThenElseExpr(_) -> failwith "not implemented"
;;
