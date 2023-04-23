open Berk.Ast
open Berk.Rast
open Berk.Codegen_mir
open Berk.Lexer
open Berk.Llvm_utility
open Berk.Mir
open Berk.Parser
open Berk.Type_check


let () =
  let source_text = {|
    extern fn printf(fmt: string, ...): i32

    variant Empty {}

    variant Unary {
    | One
    }

    variant BinaryNoFields {
    | Left
    | Right
    }

    variant BinarySameFields {
    | North(i8)
    | South(i8)
    }

    variant Binary {
    | True(bool)
    | False
    }

    variant Opt<`a> {
    | Some(`a)
    | None
    }

    variant YesOrNo<`a> {
    | Yes(`a)
    | No(`a)
    }

    variant MultipleFields {
    | MultiTwo(bool, Unary)
    | MultiThree(BinaryNoFields, bool, Unary)
    }

    fn is_unsigned_sub_safe(lhs: u64, rhs: u64): YesOrNo<bool> {
      if lhs >= rhs {
        return Yes(true);
      }

      return No(false);
    }

    fn fib_t(n: u64, s_last: u64, last: u64): u64 {
      if n == 1 {
        return last;
      };
      return fib_t(n - 1, last, s_last + last);
    }

    fn fib(n: u64): u64 {
      return fib_t(n, 0, 1);
    }

    fn ret_int(): i32 {
      return 20;
    }

    fn collatz(n: u64) {
      while {let mut i = n;} i > 1 {
        ignore printf("%llu\n", i);

        if (i % 2 == 0) {
          i = i / 2;
        }
        else {
          i = i * 3 + 1;
        }
      }

      ignore printf("1\n");
    }

    // Implement the Sieve of Eratosthenes, with the trivial evens optimization.
    fn primes() {
      let mut how_many = 1;

      ignore printf("Prime: 2\n");

      while { // Side-comment test: while-expr init-var-decl block.
        let len = 16;
        let mut sieve: [16]bool;
        let mut i = 3;
      } i < len {
        if sieve[i] != true {
          ignore printf("Prime: %d\n", i);

          how_many = how_many + 1;

          while {let mut cross_off = i;} cross_off < len {
            sieve[cross_off] = true;

            cross_off = cross_off + i;
          }
        }

        i = i + 2;
      }

      ignore printf("There were %d primes!\n", how_many);

      return;
    }

    fn short_circuit(val: bool, str: string): bool {
      ignore printf("%s", str);

      return val;
    }

    fn ufcs_identity(v: u32): u32 {
      return v;
    }

    fn ufcs_add(v1: u32, v2: u32): u32 {
      return v1 + v2;
    }

    fn ufcs_mult(v1: u32, v2: u32): u32 {
      return v1 * v2;
    }

    fn ufcs_sub_add(v1: u32, v2: u32, v3: u32): u32 {
      let v4 = v2 - v3;
      return v1 + v4;
    }

    fn main(): i8 {
      let dup_hello_1 = "Hello, world!";
      let dup_hello_2 = "Hello, world!";
      let dup_hello_3 = "Hello, world!";

      ignore printf("%s\n", dup_hello_1);
      ignore printf("%s\n", dup_hello_2);
      ignore printf("%s\n", dup_hello_3);

      let val: bool = false;

      if val {
        ignore printf("True? Bad! Expected false!\n");
      } else {
        ignore printf("False! Good!\n");
      }

      let def_int: u32;
      let def_str: string;

      ignore printf("Default int: [%d], default str: [%s]\n", def_int, def_str);

      let mut bool_vars: [12]bool;
      bool_vars[2] = true;
      bool_vars[6] = true;

      while {let mut i: u32 = 0;} i < 12 {
        ignore printf("Bool var: [%d] [%d]\n", i, bool_vars[i]);

        i = i + 1;
      }

      let my_str = "Hello, world! [%d] [%llu]\n";
      let var = 6 + 7 * 8 - ret_int();
      let var2: i32 = 6 + 7 * 8 - ret_int();
      let fib_res = fib(50);
      ignore printf(my_str, var, fib_res);

      let mut tup = (1, 2, 3);
      tup.1 = 4;

      let left = tup.0;
      let middle = tup.1;
      let right = tup.2;

      ignore printf(
        "Tuple: left[%d], mid[%d], right[%d]\n", left, middle, right
      );

      let fn_ptr = ret_int;
      let fn_ptr_val = fn_ptr.();

      ignore printf("fn ptr val: [%d] [%d]\n", fn_ptr_val, fn_ptr.());

      let fn_tup = (fib, fib);
      ignore printf("Double-indirection fib: [%llu]\n", fn_tup.1.(50));

      while {let mut iter: u32 = 0;} iter < 16 {
        ignore printf("iter: %d\n", iter);

        iter = iter + 1;
      }

      let mut ultra_multi_vars: [10][20][30][40]bool;
      let mut layer_one = ultra_multi_vars[9];
      let mut layer_two = layer_one[19];
      let mut layer_thr = layer_two[29];
      let mut ultra_val = layer_thr[39];

      ignore printf(
        "Before change, multi-dimensional: [%d] [%d] [%d] [%d] [%d]\n",
        ultra_val,
        layer_thr[39],
        layer_two[29][39],
        layer_one[19][29][39],
        ultra_multi_vars[9][19][29][39]
      );

      layer_thr[39] = true;
      ultra_val = layer_thr[39];

      ignore printf(
        "After  change, multi-dimensional: [%d] [%d] [%d] [%d] [%d]\n",
        ultra_val,
        layer_thr[39],
        layer_two[29][39],
        layer_one[19][29][39],
        ultra_multi_vars[9][19][29][39]
      );

      layer_thr[39] = true;
      layer_two[29][39] = true;
      layer_one[19][29][39] = true;
      ultra_multi_vars[9][19][29][39] = true;
      ultra_multi_vars[0][1][2][3] = true;

      ignore printf(
        "Values at various indices: [%d] [%d] [%d] [%d]\n",
        ultra_multi_vars[0][1][2][2],
        ultra_multi_vars[0][1][2][3],
        ultra_multi_vars[0][1][2][4],
        ultra_multi_vars[0][1][1][3]
      );

      collatz(5);

      primes();

      let mut map: [25][79]bool;

      while {let mut map_i = 0;} map_i < 25 {
        while {let mut map_j = 0;} map_j < 79 {
          if map_i % 2 != 0 {
            if map_j % 2 != 0 {
              map[map_i][map_j] = true;
            }
          }
          map_j = map_j + 1;
        }
        map_i = map_i + 1;
      }

      while {let mut map_ii = 0;} map_ii < 25 {
        while {let mut map_jj = 0;} map_jj < 79 {
          if map[map_ii][map_jj] == true {
            ignore printf("X");
          }
          else {
            ignore printf(".");
          }

          map_jj = map_jj + 1;
        }
        ignore printf("\n");

        map_ii = map_ii + 1;
      }

      let mut arr_of_tup: [7](i32, bool);
      ignore printf(
        "val: [%d], bool: [%d]\n", arr_of_tup[0].0, arr_of_tup[0].1
      );
      arr_of_tup[0].0 = 37;
      arr_of_tup[0].1 = true;
      ignore printf(
        "val: [%d], bool: [%d]\n", arr_of_tup[0].0, arr_of_tup[0].1
      );
      arr_of_tup[0] = (41, false);
      ignore printf(
        "val: [%d], bool: [%d]\n", arr_of_tup[0].0, arr_of_tup[0].1
      );

      let mut arr_2d: [14][21](i32, bool, string);
      ignore printf(
        "2d.left: [%d], 2d.middle: [%d], 2d.right: [%s]\n",
        arr_2d[1][2].0, arr_2d[1][2].1, arr_2d[1][2].2
      );
      arr_2d[1][2].0 = 6;
      arr_2d[1][2].1 = true;
      arr_2d[1][2].2 = "Fantastic!";
      ignore printf(
        "2d.left: [%d], 2d.middle: [%d], 2d.right: [%s]\n",
        arr_2d[1][2].0, arr_2d[1][2].1, arr_2d[1][2].2
      );
      arr_2d[1][2] = (12, false, "Awful!");
      ignore printf(
        "2d.left: [%d], 2d.middle: [%d], 2d.right: [%s]\n",
        arr_2d[1][2].0, arr_2d[1][2].1, arr_2d[1][2].2
      );

      //let weird_array: (u32, [10]bool, [20][30](u32, [40]bool));

      let variant_val = True(true);

      let variant_match = match variant_val {
      | True(x) -> (x, false, x)
      | False -> (false, true, false)
      };

      ignore printf(
        "variant_match: [%d] [%d] [%d]\n",
        variant_match.0, variant_match.1, variant_match.2
      );

      match variant_val {
      | _ -> {
          ignore printf("Non-expr match statement!\n");
        }
      }

      let variant_unary = One;
      let variant_binary_no_fields = Left;
      let variant_binary_no_fields_tuple = (Left, Right);

      let expr_block_val = {
        let expr_block_val_one = 1;
        let expr_block_val_two = 2;
        expr_block_val_one + expr_block_val_two
      };

      ignore printf("expr_block_val == 3? [%d]\n", expr_block_val);

      let f_val1: f64 = 123.456;
      let f_val2: f64 = 456.789;
      let f_val3 = f_val1 + f_val2;
      ignore printf(
        "f_val1 [%f], f_val2 [%f], f_val3 [%f]\n",
        f_val1, f_val2, f_val3
      );

      let decl_test_1 = 3;
      let mut decl_test_2: (bool, u32) = (true, 15 + 7);
      // TODO: Disallow shadowing?
      let (decl_many_1, decl_many_2) = (1, 2);
      let (
        decl_many_1,
        decl_many_2: u32,
        mut decl_many_3,
        mut decl_many_4: bool
      ) = (1, 2, 3, true);

      ignore printf("decl_test_1: [%d]\n", decl_test_1);
      ignore printf("decl_test_2: [%d] [%d]\n", decl_test_2.0, decl_test_2.1);
      ignore printf("decl_many_1: [%d]\n", decl_many_1);
      ignore printf("decl_many_2: [%d]\n", decl_many_2);
      ignore printf("decl_many_3: [%d]\n", decl_many_3);
      ignore printf("decl_many_4: [%d]\n", decl_many_4);

      let sanity_true = true;
      let sanity_false = false;

      ignore printf("sanity_true: [%d]\n", sanity_true);
      ignore printf("sanity_false: [%d]\n", sanity_false);

      let and_true = true && true;
      let and_false_1 = false && true;
      let and_false_2 = true && false;
      let and_false_3 = false && false;

      let or_false = false || false;
      let or_true_1 = true || false;
      let or_true_2 = false || true;
      let or_true_3 = true || true;

      ignore printf("and_true:    [%d] ([1] expected)\n", and_true);
      ignore printf("and_false_1: [%d] ([0] expected)\n", and_false_1);
      ignore printf("and_false_2: [%d] ([0] expected)\n", and_false_2);
      ignore printf("and_false_3: [%d] ([0] expected)\n", and_false_3);
      ignore printf("or_false:    [%d] ([0] expected)\n", or_false);
      ignore printf("or_true_1:   [%d] ([1] expected)\n", or_true_1);
      ignore printf("or_true_2:   [%d] ([1] expected)\n", or_true_2);
      ignore printf("or_true_3:   [%d] ([1] expected)\n", or_true_3);

      ignore short_circuit(true, "short circuit sanity");

      ignore printf("Expect LHS only: ");
      let and_ff =
        short_circuit(false, "do LHS") && short_circuit(false, ", NO RHS");
      ignore printf("\nExpect LHS only: ");
      let and_ft =
        short_circuit(false, "do LHS") && short_circuit(true, ", NO RHS");
      ignore printf("\nExpect LHS and RHS: ");
      let and_tf =
        short_circuit(true, "do LHS") && short_circuit(false, ", do RHS");
      ignore printf("\nExpect LHS and RHS: ");
      let and_tt =
        short_circuit(true, "do LHS") && short_circuit(true, ", do RHS");

      ignore printf("\nExpect LHS and RHS: ");
      let or_ff =
        short_circuit(false, "do LHS") || short_circuit(false, ", do RHS");
      ignore printf("\nExpect LHS and RHS: ");
      let or_ft =
        short_circuit(false, "do LHS") || short_circuit(true, ", do RHS");
      ignore printf("\nExpect LHS only: ");
      let or_tf =
        short_circuit(true, "do LHS") || short_circuit(false, ", NO RHS");
      ignore printf("\nExpect LHS only: ");
      let or_tt =
        short_circuit(true, "do LHS") || short_circuit(true, ", NO RHS");
      ignore printf("\n");

      ignore printf("and_ff: [%d] ([0] expected)\n", and_ff);
      ignore printf("and_ft: [%d] ([0] expected)\n", and_ft);
      ignore printf("and_tf: [%d] ([0] expected)\n", and_tf);
      ignore printf("and_tt: [%d] ([1] expected)\n", and_tt);
      ignore printf("or_ff:  [%d] ([0] expected)\n", or_ff);
      ignore printf("or_ft:  [%d] ([1] expected)\n", or_ft);
      ignore printf("or_tf:  [%d] ([1] expected)\n", or_tf);
      ignore printf("or_tt:  [%d] ([1] expected)\n", or_tt);

      // The template instantation can be inferred from the expression.
      let some_test_1 = Some(true);
      // An explicit template instantiation at decl time typechecks.
      let some_test_2: Opt<bool> = Some(false);
      // Not having a concrete typevar at decl time is okay if the expr knows
      let some_test_3: Opt<`a> = Some(true);
      // Using an alias for the expected typevar works?
      let some_test_4: Opt<`b> = Some(false);

      match (some_test_1, some_test_2, some_test_3, some_test_4) {
      | (Some(b1), Some(b2), Some(b3), Some(b4)) -> {
          ignore printf(
            "Matched `(Some(%d), Some(%d), Some(%d), Some(%d))`\n",
            b1, b2, b3, b4
          );
        }
      | _ -> { ignore printf("Incorrectly matched None?\n"); }
      }

      // Explicit typevar instantiation at decl time is necessary when the
      // expr is not enough.
      let none_test: Opt<bool> = None;

      // Not enough info to typecheck:
      //let none_test = None;
      //let none_test: Opt<`a> = None;

      let sub_success_1 = is_unsigned_sub_safe(60, 25);
      let sub_success_2 = is_unsigned_sub_safe(25, 25);
      let sub_fail = is_unsigned_sub_safe(10, 25);

      match sub_success_1 {
      | Yes(b) -> {
          ignore printf("Subtraction success: [%d]\n", b);
        }
      | No(b) -> {
          ignore printf("Unexpected failure to subtract! [%d]\n", b);
        }
      }

      match sub_success_2 {
      | Yes(b) -> {
          ignore printf("Subtraction success: [%d]\n", b);
        }
      | No(b) -> {
          ignore printf("Unexpected failure to subtract! [%d]\n", b);
        }
      }

      match sub_fail {
      | Yes(b) -> {
          ignore printf("Subtraction success: [%d]\n", b);
        }
      | No(b) -> {
          ignore printf("Correctly expected failure to subtract: [%d]\n", b);
        }
      }

      let test_false = false;
      let test_true = true;
      let negate_false_is_true = !test_false;
      let negate_true_is_false = !test_true;
      ignore printf(
        "False? [%d], True? [%d], True? [%d], False? [%d]\n",
        test_false, test_true, negate_false_is_true, negate_true_is_false
      );

      // Test UFCS "method" calls and chaining.

      let ufcs_identity_test = 5.ufcs_identity();
      let ufcs_identity_chained =
        5.ufcs_identity().ufcs_identity().ufcs_identity().ufcs_identity();
      let ufcs_add_test = 5.ufcs_add(10);
      let ufcs_math_chain =
        5.ufcs_identity().ufcs_add(10).ufcs_mult(3).ufcs_sub_add(20, 15);

      ignore printf("ufcs_identity_test: [%d] (5?)\n", ufcs_identity_test);
      ignore printf("ufcs_identity_chained: [%d]\n", ufcs_identity_chained);
      ignore printf("ufcs_add_test: [%d] (15?)\n", ufcs_add_test);
      ignore printf("ufcs_math_chain: [%d] (50?)\n", ufcs_math_chain);

      // Variant constructors can have multiple fields, and can have tuples as
      // "single" fields.
      let some_tuple = Some((true, false));
      let multi_test_1 = MultiTwo(true, One);
      let multi_test_2 = MultiThree(Right, true, One);
      let multi_test_3 = MultiThree(Right, false, One);

      match some_tuple {
      | Some((a, b)) -> {
          ignore printf("a: [%d](1); b: [%d](0)\n", a, b);
        }
      | None -> {}
      }

      match multi_test_1 {
      | MultiTwo(b, One) -> {
          ignore printf("MultiTwo: [%d](1)\n", b);
        }
      | MultiThree(_, _, _) -> {
          ignore printf("Should not match MultiThree!\n");
        }
      }

      match (multi_test_2, multi_test_3) {
      | (MultiThree(_, b1, One), MultiThree(_, b2, _)) -> {
          ignore printf("MultiThree: [%d](1), [%d](0)\n", b1, b2);
        }
      | _ -> {}
      }

      // Exercise `as` bindings in matches.
      let quad_some = Some((true, false, true, true));
      match quad_some {
      | Some((quad_b1, _, _, _) as quad_tup) -> {
          ignore printf("as-matching: quad_b1: [%d](1)\n", quad_b1);

          match quad_tup {
          | (_, _ as quad_ex_false, _, quad_b4) as quad_tup_2 -> {
              ignore printf("as-matching: quad_b4: [%d](1)\n", quad_b4);

              match (quad_ex_false, quad_tup_2) {
              | (false, (_, false, quad_b3, _)) -> {
                  ignore printf(
                    "Expected match: quad_b3: [%d]\n", quad_b3
                  );
                }
              | (true, (_, false, quad_b3, _)) -> {
                  ignore printf(
                    "UN-expected match 1: quad_b3: [%d]\n", quad_b3
                  );
                }
              | (false, (_, true, quad_b3, _)) -> {
                  ignore printf(
                    "UN-expected match 2: quad_b3: [%d]\n", quad_b3
                  );
                }
              | (_, (_, _, quad_b3, _)) -> {
                  ignore printf(
                    "UN-expected match 3: quad_b3: [%d]\n", quad_b3
                  );
                }
              }
            }
          }
        }
      | None -> {}
      }

      let layer_one = {
        let layer_two = {
          let layer_three = {
            let layer_four = 4;

            layer_four + 5
          };

          layer_three + 6
        };

        layer_two + 7
      };

      ignore printf("layer_one: [%d](22)\n", layer_one);

      return 0;
    }
  |} in

  Printexc.record_backtrace true ;
  Llvm.enable_pretty_stacktrace () ;

  (* Lexing. *)
  let lexbuf = Sedlexing.Latin1.from_gen (Gen.of_string source_text) in
  let tokens = tokenize lexbuf in
  print_tokens tokens ;

  (* Parsing into module-declaration AST list. *)
  let mod_decls = parse_tokens ~trace:true tokens in

  (* Currently require declaration before use, but we build a list of module
  declarations in reverse order. *)
  let mod_decls = List.rev mod_decls in

  let _ =
    List.iter (
      fun decl ->
        Printf.printf "%s\n" (dump_module_decl_ast decl)
    ) mod_decls
  in

  (* Typechecking. *)
  let mod_decls_tc = type_check_mod_decls mod_decls in

  (* Uniquify varnames for MIR generation. *)
  let mod_decls_tc_rewritten =
    List.map (
      fun mod_decl ->
        match mod_decl with
        | FuncDef(func_def) ->
            let func_def_rewritten = rewrite_to_unique_varnames func_def in
            FuncDef(func_def_rewritten)

        | FuncExternDecl(_)
        | VariantDecl(_) -> mod_decl
    ) mod_decls_tc
  in

  (* Print typechecked source. *)
  let asts_fmted =
    List.map
      (fmt_mod_decl ~pretty_unbound:true ~print_typ:true)
      mod_decls_tc_rewritten
  in
  let _ = List.iter (Printf.printf "%s") asts_fmted in

  (* Generate MIR. *)
  let mir_ctxts =
    List.filter_map (
      fun mod_decl ->
        begin match mod_decl with
          | VariantDecl(_) -> None

          | FuncExternDecl(func_decl) ->
              let rfunc_decl = func_decl_t_to_rfunc_decl_t func_decl in

              Printf.printf "RAST:\n%s\n" (fmt_rfunc_decl_t rfunc_decl) ;

              let mir_ctxt = rfunc_decl_to_mir rfunc_decl in
              Some(mir_ctxt)
          | FuncDef(func_def) ->
              let rfunc_def = func_def_t_to_rfunc_def_t func_def in

              Printf.printf "RAST:\n%s\n" (fmt_rfunc_def_t rfunc_def) ;

              let mir_ctxt = rfunc_to_mir rfunc_def in
              Some(mir_ctxt)
        end
    ) mod_decls_tc_rewritten
  in

  (* Print MIR. *)
  let _ =
    List.iter (
      fun mir_ctxt -> Printf.printf "%s%!" (fmt_mir_ctxt mir_ctxt)
    ) mir_ctxts
  in

  (* Setup LLVM context. *)
  Llvm.enable_pretty_stacktrace ();
  let llvm_ctxt = Llvm.global_context () in
  let the_module = Llvm.create_module llvm_ctxt "main" in
  let the_fpm = Llvm.PassManager.create_function the_module in
  let the_mpm = Llvm.PassManager.create () in
  let builder = Llvm.builder llvm_ctxt in
  let _ = initialize_fpm the_fpm |> ignore in
  let _ = initialize_mpm the_mpm |> ignore in

  let data_layout_str = Llvm.data_layout the_module in
  let data_layout_mod = Llvm_target.DataLayout.of_string data_layout_str in

  let llvm_sizeof typ =
    let llvm_sizeof_int64 =
      Llvm_target.DataLayout.store_size typ data_layout_mod
    in
    Int64.to_int llvm_sizeof_int64
  in

  let mod_gen_ctxt : module_gen_context = {
    func_sigs = StrMap.empty;
    llvm_mod = the_module;
    data_layout_mod = data_layout_mod;
    berk_t_to_llvm_t = berk_t_to_llvm_t llvm_sizeof llvm_ctxt;
    llvm_sizeof = llvm_sizeof;
  } in

  (* MIR -> LLVM codegen. *)
  let _ =
    codegen_func_mirs
      llvm_ctxt
      the_fpm
      the_mpm
      builder
      mod_gen_ctxt
      mir_ctxts
  in

  (* Dump various output files from populated LLVM context. *)
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
;;

