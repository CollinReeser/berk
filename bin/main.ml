open Ast
open Pretty_print
open Typing
open Type_check


let build_example_ast =
  {
    f_name = "example_func";
    f_params = [
      {
        p_name = "arg_1";
        p_type = I64;
      };
      {
        p_name = "arg_2";
        p_type = I64;
      }
    ];
    f_stmts = [
      DeclDef(
        "abc", I64,
        Add(ValI64(5), Mul(Sub(ValI64(6), ValI64(7)), ValI64 (8)))
      );
      ExprStmt(
        IfExpr({
          if_block = {cond = ValI64(30); stmts = [ResolveStmt(ValI64(31))]};
          else_if_blocks = [
            {cond = ValI64(32); stmts = [ResolveStmt(ValI64(33))]};
            {cond = ValI64(34); stmts = [ResolveStmt(ValI64(35))]};
          ];
          else_block = Some([ResolveStmt(ValI64(35))])
        })
      );
      DeclDef(
        "def", I64,
        IfExpr({
          if_block = {cond = ValI64(50); stmts = [ExprStmt(ValI64(51))]};
          else_if_blocks = [];
          else_block = Some([ExprStmt(ValI64(55))])
        })
      );
      DeclDef(
        "ghi", I64,
        IfExpr({
          if_block = {cond = ValI64(50); stmts = [ExprStmt(ValI64(51))]};
          else_if_blocks = [];
          else_block = None;
        })
      );
      IfStmt({
        if_block = {cond = ValI64(40); stmts = [ExprStmt(ValI64(41))]};
        else_if_blocks = [
          {cond = ValI64(42); stmts = [ExprStmt(ValI64(43))]};
        ];
        else_block = Some([ExprStmt(ValI64(45))])
      })
    ];
  }
;;


let test_typecheck ast =
  Printf.printf "Expression [";
  print_expr "" ast;
  Printf.printf "] typechecks to: ";
  match type_check_expr ast with
  | None -> Printf.printf "<typecheck failed>\n"
  | Some(t) -> print_berk_type t; Printf.printf "\n"
;;


let dump_to_object filename the_fpm the_module =
  Llvm_all_backends.initialize ();
  (* "x86_64-pc-linux-gnu" *)
  let target_triple = Llvm_target.Target.default_triple () in
  let target = Llvm_target.Target.by_triple target_triple in
  let cpu = "generic" in
  let reloc_mode = Llvm_target.RelocMode.Default in
  let machine = Llvm_target.TargetMachine.create ~triple:target_triple ~cpu ~reloc_mode target in
  let data_layout = Llvm_target.TargetMachine.data_layout machine |> Llvm_target.DataLayout.as_string in
  Llvm.set_target_triple target_triple the_module;
  Llvm.set_data_layout data_layout the_module;
  Llvm_target.TargetMachine.add_analysis_passes the_fpm machine;
  let file_type = Llvm_target.CodeGenFileType.ObjectFile in
  Llvm_target.TargetMachine.emit_to_file the_module file_type filename machine;
  Printf.printf "Wrote %s\n" filename;
  ()


let main = begin
  print_func_ast build_example_ast;

  test_typecheck (Add(ValI64(5), ValI64(6)));

  test_typecheck (
    IfExpr({
      if_block = {cond = ValBool(true); stmts = [ResolveStmt(ValI32(31))]};
      else_if_blocks = [
        {cond = ValBool(true); stmts = [ResolveStmt(ValI64(33))]};
        {cond = ValBool(true); stmts = [ResolveStmt(ValI32(35))]};
      ];
      else_block = Some([ResolveStmt(ValI64(35))])
    })
  );

  test_typecheck (
    IfExpr({
      if_block = {cond = ValBool(true); stmts = [ResolveStmt(ValI64(31))]};
      else_if_blocks = [
        {cond = ValBool(true); stmts = [ResolveStmt(ValBool(true))]};
        {cond = ValBool(true); stmts = [ResolveStmt(ValI64(35))]};
      ];
      else_block = Some([ResolveStmt(ValBool(false))])
    })
  );

  test_typecheck (
    IfExpr({
      if_block = {cond = ValBool(true); stmts = [ResolveStmt(ValBool(true))]};
      else_if_blocks = [
        {cond = ValBool(true); stmts = [ResolveStmt(ValBool(false))]};
      ];
      else_block = Some([ResolveStmt(ValBool(false))])
    })
  );

  begin
    let context = Llvm.global_context () in
    let the_module = Llvm.create_module context "main" in
    let the_fpm = Llvm.PassManager.create_function the_module in
    let builder = Llvm.builder context in
    let _ = begin
      (* Promote allocas to registers. *)
      Llvm_scalar_opts.add_memory_to_register_promotion the_fpm ;
      (* Do simple "peephole" optimizations and bit-twiddling optzn. *)
      Llvm_scalar_opts.add_instruction_combination the_fpm ;
      (* reassociate expressions. *)
      Llvm_scalar_opts.add_reassociation the_fpm ;
      (* Eliminate Common SubExpressions. *)
      Llvm_scalar_opts.add_gvn the_fpm ;
      (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
      Llvm_scalar_opts.add_cfg_simplification the_fpm ;
      (* Return value here only indicates whether internal state was modified *)
      Llvm.PassManager.initialize the_fpm |> ignore ;

      let double_t = Llvm.double_type context in
      let doubles_empty = Array.make 0 double_t in
      let func_sig_t = Llvm.function_type double_t doubles_empty in
      let func_name = "main" in
      let new_func = Llvm.declare_function func_name func_sig_t the_module in
      let bb = Llvm.append_block context "entry" new_func in
      Llvm.position_at_end bb builder ;

      let return_val = begin
        let lhs_val = Llvm.const_float double_t 1.7 in
        let rhs_val = Llvm.const_float double_t 2.4 in
        Llvm.build_fadd lhs_val rhs_val "addtmp" builder
      end in

      let _ : Llvm.llvalue = Llvm.build_ret return_val builder in
      (* Validate the generated code, checking for consistency. *)
      let _ = begin
        match Llvm_analysis.verify_function new_func with
        | true -> ()
        | false ->
          begin
            Printf.printf "invalid function generated\n%s\n"
              (Llvm.string_of_llvalue new_func) ;
            Llvm_analysis.assert_valid_function new_func ;
            ()
          end
      end in
      (* Optimize the function. *)
      let _ : bool = Llvm.PassManager.run_function new_func the_fpm in
      ()
    end in
    let filename = "output.o" in
    let _ = dump_to_object filename the_fpm the_module in
    let _ = Sys.command "clang -o output output.o" in
    ()
  end
end
;;

main;;
