open Ast
open Pretty_print
open Typing
open Type_check
open Codegen


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
        "abc", Undecided,
        BinOp(
          Undecided, Add,
          ValI32(5),
          BinOp(
            Undecided, Mul,
            BinOp(
              Undecided, Sub,
              ValI32(6),
              ValI32(7)
            ),
            ValI32(8)
          )
        )
      );
      ExprStmt(
        IfThenElseExpr(
          Undecided,
          ValBool(true),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(31));
            ]
          ),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(32));
            ]
          )
        )
      );
      DeclDef(
        "def", I64,
        IfThenElseExpr(
          Undecided,
          ValBool(false),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(33));
            ]
          ),
          BlockExpr(
            Undecided, [
              ResolveStmt(ValI64(34));
            ]
          )
        )
      );
    ];
  }
;;


let test_typecheck ast =
  Printf.printf "Expression [";
  print_expr "" ast;
  Printf.printf "] typechecks to: ";
  let expr_typechecked = type_check_expr ast in
  let expr_t = expr_type expr_typechecked in
  Printf.printf "%s" (fmt_type expr_t);
  Printf.printf "\n"
;;


let dump_to_file file_type filename the_fpm the_module =
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
  Llvm_target.TargetMachine.emit_to_file the_module file_type filename machine;
  Printf.printf "Wrote %s\n" filename;
  ()
;;


let dump_llvm_ir filename the_module =
  Llvm.print_module filename the_module ;
  Printf.printf "Wrote %s\n" filename;
  ()
;;


let generate_executable filename_exe filename_obj =
  let cmd = Printf.sprintf "clang -o %s %s" filename_exe filename_obj in
  begin match Sys.command cmd with
    | 0 -> Printf.printf "Wrote %s\n" filename_exe
    | n -> Printf.printf "clang failed with %d\n" n
  end


let initialize_fpm the_fpm =
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
  Llvm.PassManager.initialize the_fpm
;;


let main = begin
  print_func_ast build_example_ast;

  test_typecheck (BinOp(Undecided, Add, ValI32(1), ValI32(2)));
  test_typecheck (BinOp(Undecided, Add, ValI32(1), ValI64(2)));
  test_typecheck (BinOp(Undecided, Add, ValI64(1), ValI64(2)));

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(true),
      BlockExpr(Undecided, []),
      BlockExpr(Undecided, [])
    )
  );

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(true),
      BlockExpr(
        Undecided, [
          ResolveStmt(ValI32(11));
        ]
      ),
      BlockExpr(
        Undecided, [
          ResolveStmt(ValI64(12));
        ]
      )
    )
  );

  test_typecheck (
    IfThenElseExpr(
      Undecided,
      ValBool(false),
      BlockExpr(
        Undecided, [
          DeclDef(
            "egh", I64,
            BinOp(
              Undecided, Add,
              ValI64(5),
              BinOp(
                Undecided, Mul,
                BinOp(
                  Undecided, Sub,
                  ValI64(6),
                  ValI64(7)
                ),
                ValI64 (8)
              )
            )
          );
          ResolveStmt(ValI64(22));
        ]
      ),
      BlockExpr(
        Undecided, [
          DeclDef("ijk", Undecided, ValBool(false));
          ResolveStmt(ValI64(24));
        ]
      )
    )
  );

  begin
    let context = Llvm.global_context () in
    let the_module = Llvm.create_module context "main" in
    let the_fpm = Llvm.PassManager.create_function the_module in
    let builder = Llvm.builder context in
    let _ = begin
      initialize_fpm the_fpm |> ignore ;

      let i64_t = Llvm.i64_type context in
      let doubles_empty = Array.make 0 i64_t in
      let func_sig_t = Llvm.function_type i64_t doubles_empty in
      let func_name = "main" in
      let new_func = Llvm.declare_function func_name func_sig_t the_module in
      let bb = Llvm.append_block context "entry" new_func in
      Llvm.position_at_end bb builder ;

      let expr_raw = (
        BinOp(
          Undecided, Add,
          ValI64(5),
          BinOp(
            Undecided, Mul,
            BinOp(
              Undecided, Sub,
              ValI64(10),
              ValI64(7)
            ),
            ValI64 (8)
          )
        )
      )
      in
        test_typecheck expr_raw;
        Printf.printf "Expr type: %s\n" (
          type_check_expr expr_raw |> expr_type |> fmt_type
        );
        print_expr "" expr_raw;
        Printf.printf "\n";
        print_expr "" (type_check_expr expr_raw);
        Printf.printf "\n";
      let expr_typechecked = type_check_expr expr_raw in
      let return_val = codegen_expr context builder expr_typechecked in

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

    let filename_ll = "output.ll" in
    dump_llvm_ir filename_ll the_module ;

    let filename_asm = "output.s" in
    let file_type = Llvm_target.CodeGenFileType.AssemblyFile in
    dump_to_file file_type filename_asm the_fpm the_module ;

    let filename_obj = "output.o" in
    let file_type = Llvm_target.CodeGenFileType.ObjectFile in
    dump_to_file file_type filename_obj the_fpm the_module ;

    let filename_exe = "output" in
    generate_executable filename_exe filename_obj ;

    ()
  end
end
;;

main;;
