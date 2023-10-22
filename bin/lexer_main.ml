(* NOTE: Deliberately in approximately "compiler pipeline" order. *)
open Berk.Lexer
open Berk.Parser
open Berk.Ast
open Berk.Type_check
open Berk.Ast_to_rast
open Berk.Rast
open Berk.Rast_to_hir
open Berk.Hir
open Berk.Hir_to_mir
open Berk.Mir
open Berk.Mir_to_llvm
open Berk.Llvm_utility


let () =
  let timing_program_start = Unix.gettimeofday () in

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
    | North(i32)
    | South(i32)
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

    fn tuple_interior_references() {
      let mut tup = (1, 2, "hello!");
      let mut tup_ref_1 = ref tup.1;
      let mut tup_ref_2 = ref tup.2;

      ignore printf(
        "tup.1: [%d], tup_ref_1.*: [%d], tup.2: [%s], tup_ref_2.*: [%s]\n",
        tup.1,
        tup_ref_1.*,
        tup.2,
        tup_ref_2.*
      );

      tup.1 = 20;
      tup.2 = "greetings!";

      ignore printf(
        "tup.1: [%d], tup_ref_1.*: [%d], tup.2: [%s], tup_ref_2.*: [%s]\n",
        tup.1,
        tup_ref_1.*,
        tup.2,
        tup_ref_2.*
      );

      tup_ref_1.* = 200;
      tup_ref_2.* = "farewell!";

      ignore printf(
        "tup.1: [%d], tup_ref_1.*: [%d], tup.2: [%s], tup_ref_2.*: [%s]\n",
        tup.1,
        tup_ref_1.*,
        tup.2,
        tup_ref_2.*
      );

      return;
    }

    fn complex_variable_references() {
      let mut x = 5;
      let mut ref_x = ref x;

      ignore printf("x: [%d], ref_x: [%d]\n", x, ref_x.*);

      x = 50;
      ignore printf("x: [%d], ref_x: [%d]\n", x, ref_x.*);

      ref_x.* = 100;
      ignore printf("x: [%d], ref_x: [%d]\n", x, ref_x.*);

      let y = 10;

      // Test being able to dereference a temporary reference.
      let z = ref_x.* + (ref y).*;

      ignore printf(
        "x: [%d], ref_x: [%d], y: [%d] (10), z: [%d] (110)\n",
        x,
        ref_x.*,
        y,
        z
      );

      return;
    }

    fn ref_array_direct() {
      let mut ultra_multi_vars: [10][20]i32;
      let mut ref_direct = ref ultra_multi_vars[9][19];

      ultra_multi_vars[9][19] = 1001;

      if
        ref_direct.* == ultra_multi_vars[9][19] &&
        ref_direct.* == 1001 &&
        ultra_multi_vars[9][19] == 1001
      {
        ignore printf(
          "Direct references work! [%d] [%d] (%d)\n",
          ref_direct.*,
          ultra_multi_vars[9][19],
          1001
        );
      }
      else {
        ignore printf(
          "FAILURE in ref_array_direct! [%d] [%d] (%d)\n",
          ref_direct.*,
          ultra_multi_vars[9][19],
          1001
        );
      }

      ref_direct.* = 2002;

      if
        ref_direct.* == ultra_multi_vars[9][19] &&
        ref_direct.* == 2002 &&
        ultra_multi_vars[9][19] == 2002
      {
        ignore printf(
          "Direct references work! [%d] [%d] (%d)\n",
          ref_direct.*,
          ultra_multi_vars[9][19],
          2002
        );
      }
      else {
        ignore printf(
          "FAILURE in ref_array_direct! [%d] [%d] (%d)\n",
          ref_direct.*,
          ultra_multi_vars[9][19],
          2002
        );
      }

      return;
    }

    fn if_is_expr_test() {
      if Some(5) is Some(i) {
        ignore printf("if_is_expr_test [%d] (5)\n", i);
      }

      if Yes("Value!") is Yes(s) && Some(10.5) is Some(f) {
        ignore printf(
          "if_is_expr_test [%s] ('Value!'); [%.1f] (10.5)\n", s, f
        );
      }

      return;
    }

    fn if_is_expr() {
      let opt = Some(5);

      match opt {
      | Some(i) -> {
          ignore printf("if_is_expr::match::i: [%d]\n", i);
        }
      | None -> {
          ignore printf("if_is_expr::match failed!\n");
        }
      }

      if opt is Some(_) {
        ignore printf("if_is_expr::is!\n");
      }

      if opt is None {
        ignore printf("if_is_expr::None??\n");
      }

      if true && opt is Some(_) {
        ignore printf("if_is_expr::is 2!\n");
      }

      if opt is Some(_) && true {
        ignore printf("if_is_expr::is 3!\n");
      }

      if false && opt is Some(_) {
        ignore printf("if_is_expr::is 4!\n");
      }

      if opt is Some(_) && false {
        ignore printf("if_is_expr::is 5!\n");
      }

      let yes_val = Yes(":D");
      if opt is Some(i) && yes_val is Yes(str) {
        ignore printf("if_is_expr::is, could it be... [%d] [%s]\n", i, str);
      }

      if opt is Some(i) && i == 5 {
        ignore printf("if_is_expr::is, could it be... [%d]\n", i);
      }

      return;
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
        let len = 32;
        let mut sieve: [32]bool;
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

    fn ufcs_identity(v: i32): i32 {
      return v;
    }

    fn ufcs_add(v1: i32, v2: i32): i32 {
      return v1 + v2;
    }

    fn ufcs_mult(v1: i32, v2: i32): i32 {
      return v1 * v2;
    }

    fn ufcs_sub_add(v1: i32, v2: i32, v3: i32): i32 {
      let v4 = v2 - v3;
      return v1 + v4;
    }

    fn phi_test(one: i64, two: i64) {
      let mut phi_one = one;
      let mut phi_two = two;

      if phi_one + phi_two > 20 {
        phi_one = 30;
        phi_two = 40;
      }

      ignore printf("one: [%d]; two: [%d]\n", phi_one, phi_two);

      return;
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

      // Declared variables are auto-initialized.
      let def_int: u32;
      let def_str: string;

      ignore printf("Default int: [%d], default str: [%s]\n", def_int, def_str);

      // No need to initialize; declared datastructures are auto-initialized.
      let mut bool_vars: [12]bool;

      bool_vars[2] = true;
      bool_vars[6] = true;

      while {let mut idx_i: u32 = 0;} idx_i < 12 {
        ignore printf("Bool var: [%d] [%d]\n", idx_i, bool_vars[idx_i]);

        idx_i = idx_i + 1;
      }

      let my_str = "Hello, world! [%d] (%d) [%llu] (%llu)\n";
      let var = 6 + 7 * 8 - ret_int();
      let var2: i32 = 6 + 7 * 8 - ret_int();
      let fib_res = fib(50);
      let fib_exp: u64 = 12586269025;
      ignore printf(my_str, var, 42, fib_res, fib_exp);

      let mut tup = (1, 2, 3);
      tup.1 = 4;

      let left = tup.0;
      let middle = tup.1;
      let right = tup.2;

      ignore printf(
        "Tuple: left[%d], mid[%d], right[%d] ((%d) (%d) (%d))\n",
        left, middle, right,
        1, 4, 3
      );

      let fn_ptr = ret_int;
      let fn_ptr_val = fn_ptr.();

      ignore printf("fn ptr val: [%d] [%d] (20) (20)\n", fn_ptr_val, fn_ptr.());

      let fn_tup = (fib, fib);
      ignore printf(
        "Double-indirection fib: [%llu] (%llu)\n", fn_tup.1.(50), fib_exp
      );

      while {let mut iter: u32 = 0;} iter < 8 {
        ignore printf("iter: %d\n", iter);

        iter = iter + 1;
      }

      let mut ultra_multi_vars: [10][20][30][40]i32;
      let mut ref_layer_one: ref [20][30][40]i32 = ref ultra_multi_vars[9];
      let mut indir_ref_layer_two = ref ref_layer_one.*[19];
      let mut indir_ref_layer_thr: ref [40]i32 = ref indir_ref_layer_two.*[29];

      let mut ref_layer_two = ref ultra_multi_vars[9][19];
      let mut ref_layer_thr = ref ultra_multi_vars[9][19][29];

      ultra_multi_vars[9][19][29][39] = 100;

      ignore printf(
        "Change zro, multi-dimensional: [%d], [%d], [%d], [%d], [%d], [%d]\n",
        ultra_multi_vars[9][19][29][39],
        ref_layer_one.*[19][29][39],
        indir_ref_layer_two.*[29][39],
        indir_ref_layer_thr.*[39],
        ref_layer_two.*[29][39],
        ref_layer_thr.*[39]
      );

      let indir_ref_layer_thr_value = indir_ref_layer_thr.*[39];
      indir_ref_layer_thr.*[39] = 200;

      ignore printf(
        "Change one, multi-dimensional: [%d], [%d], [%d], [%d]\n",
        ultra_multi_vars[9][19][29][39],
        ref_layer_one.*[19][29][39],
        indir_ref_layer_two.*[29][39],
        indir_ref_layer_thr.*[39]
      );

      let indir_ref_layer_two_value = indir_ref_layer_two.*[29][39];
      indir_ref_layer_two.*[29][39] = 300;

      ignore printf(
        "Change two, multi-dimensional: [%d], [%d], [%d], [%d]\n",
        ultra_multi_vars[9][19][29][39],
        ref_layer_one.*[19][29][39],
        indir_ref_layer_two.*[29][39],
        indir_ref_layer_thr.*[39]
      );

      let ref_layer_one_value = ref_layer_one.*[19][29][39];
      ref_layer_one.*[19][29][39] = 400;

      ignore printf(
        "Change thr, multi-dimensional: [%d], [%d], [%d], [%d], [%d], [%d], [%d]\n",
        ultra_multi_vars[9][19][29][39],
        ref_layer_one.*[19][29][39],
        indir_ref_layer_two.*[29][39],
        indir_ref_layer_thr.*[39],
        indir_ref_layer_thr_value,
        indir_ref_layer_two_value,
        ref_layer_one_value
      );

      collatz(5);

      primes();

      let mut map: [25][79]bool;

      // Populate the map with a checkerboard pattern.
      while {let mut map_i = 0;} map_i < 25 {
        while {let mut map_j = 0;} map_j < 79 {
          // No need to initialize; arbitrary stack datastructures are
          // auto-initialized.

          if map_i % 2 != 0 {
            if map_j % 2 != 0 {
              // Set the entry.
              map[map_i][map_j] = true;
            }
          }
          else {
            if map_j % 2 == 0 {
              // Set the entry.
              map[map_i][map_j] = true;
            }
          }
          map_j = map_j + 1;
        }
        map_i = map_i + 1;
      }

      // Print the checkerboard pattern.
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

      ignore printf("decl_test_1: [%d] (3)\n", decl_test_1);
      ignore printf(
        "decl_test_2: [%hhd] [%d] (1, 22)\n", decl_test_2.0, decl_test_2.1
      );
      ignore printf("decl_many_1: [%d] (1)\n", decl_many_1);
      ignore printf("decl_many_2: [%d] (2)\n", decl_many_2);
      ignore printf("decl_many_3: [%d] (3)\n", decl_many_3);
      ignore printf("decl_many_4: [%hhd] (1)\n", decl_many_4);

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

      ignore short_circuit(true, "short circuit sanity\n");

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
      ignore printf("ufcs_identity_chained: [%d] (5?)\n", ufcs_identity_chained);
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

      // Ensure that variable names can be repeated in disparate scopes.
      let my_disparate_values = (10, 20);
      match my_disparate_values {
      | (1, b) -> {
          ignore printf("b: %d\n", b);
        }
      | (2, b) -> {
          ignore printf("b: %d\n", b);
        }
      | (a, 1) -> {
          ignore printf("a: %d\n", a);
        }
      | (a, 2) -> {
          ignore printf("a: %d\n", a);
        }
      | (a, b) -> {
          ignore printf("a, b: %d, %d\n", a, b);
        }
      }
      match my_disparate_values {
      | (a, b) -> {
          ignore printf("a!, b!: %d, %d\n", a, b);
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
          ignore printf("as-matching: quad_b1: [%hhd](1)\n", quad_b1);

          match quad_tup {
          | (_, _ as quad_ex_false, _, quad_b4) as quad_tup_2 -> {
              ignore printf("as-matching: quad_b4: [%hhd](1)\n", quad_b4);

              match (quad_ex_false, quad_tup_2) {
              | (false, (_, false, quad_b3, _)) -> {
                  ignore printf(
                    "Expected match: quad_b3: [%hhd]\n", quad_b3
                  );
                }
              | (true, (_, false, quad_b3, _)) -> {
                  ignore printf(
                    "UN-expected match 1: quad_b3: [%hhd]\n", quad_b3
                  );
                }
              | (false, (_, true, quad_b3, _)) -> {
                  ignore printf(
                    "UN-expected match 2: quad_b3: [%hhd]\n", quad_b3
                  );
                }
              | (_, (_, _, quad_b3, _)) -> {
                  ignore printf(
                    "UN-expected match 3: quad_b3: [%hhd]\n", quad_b3
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

      // UFCS can be used in some more complex situations.
      let yes_or_no = No(true);
      let fancy_ufcs =
        match yes_or_no {
        | Yes(true) -> 5
        | Yes(false) -> 10
        | No(true) -> 15
        | No(false) -> 20
        }
        .ufcs_add(10);
      ignore printf("fancy_ufcs: [%d](25)\n", fancy_ufcs);

      // UFCS allows underscores to indicate the position in the function call
      // into which the LHS dotted argument is inserted.
      ignore printf(
        "Underscore UFCS:\n [%d] (-5)\n [%d] (-14)\n [%d] (-23)\n [%d] (46)\n",
        1.ufcs_sub_add(4, 10),
        1.ufcs_sub_add(_, 5, 20),
        1.ufcs_sub_add(6, _, 30),
        1.ufcs_sub_add(7, 40, _)
      );

      // Can match against integer literals.
      let my_int_match = 5;
      match my_int_match {
      | 4 -> {
          ignore printf("Incorrect match <4>. [%d]\n", my_int_match);
        }
      | 5 -> {
          ignore printf("Correct match! [%d]\n", my_int_match);
        }
      | 8 -> {
          ignore printf("Incorrect match <8>. [%d]\n", my_int_match);
        }
      | _ -> {
          ignore printf("Incorrect match <_>. [%d]\n", my_int_match);
        }
      }

      // Can match against integers inside other constructs.
      let my_int_tuple_match = (4, 6);
      match my_int_tuple_match {
      | (3, 7) -> {
          ignore printf("Incorrect match <3, 7>.\n");
        }
      | (4, 8) -> {
          ignore printf("Incorrect match <4, 8>.\n");
        }
      | (2, 6) -> {
          ignore printf("Incorrect match <2, 6>.\n");
        }
      | (4 as a, 6 as b) -> {
          ignore printf("Correct match!! <4, 6>. [%d] [%d]\n", a, b);
        }
      | (a, b) -> {
          ignore printf("Incorrect match <_, _>. [%d] [%d]\n", a, b);
        }
      }

      let my_int_opt_match = Some(17);
      match my_int_opt_match {
      | Some(16) -> {
          ignore printf("Incorrect match <16>.\n");
        }
      | Some(17 as a) -> {
          ignore printf("Correct match!! <17>. [%d]\n", a);
        }
      | Some(18) -> {
          ignore printf("Incorrect match <16>.\n");
        }
      | Some(_ as a) -> {
          ignore printf("Incorrect match <_> (17). [%d]\n", a);
        }
      | None -> {
          ignore printf("Incorrect match <None> (17).\n");
        }
      }

      // Can match various integer ranges.
      let my_int_match_ranges = 17;
      match my_int_match_ranges {
      | 2 .. 5 as a -> {
          ignore printf("Incorrect match: 2..5: [%d]\n", a);
        }
      | 12 .. 16 as b -> {
          ignore printf("Incorrect match: 12..16: [%d]\n", b);
        }
      | 16 .. 20 as c -> {
          ignore printf("Correct match! 16..20: [%d]\n", c);
        }
      | q -> {
          ignore printf("Incorrect match: [%d]\n", q);
        }
      }

      // Can match various integer ranges.
      let my_int_match_low_high = 17;
      match my_int_match_low_high {
      | .. 5 as a -> {
          ignore printf("Incorrect match: ..5: [%d]\n", a);
        }
      | 8 .. 12 as b -> {
          ignore printf("Incorrect match! 8..12: [%d]\n", b);
        }
      | 15 .. as c -> {
          ignore printf("Correct match: 15..: [%d]\n", c);
        }
      | q -> {
          ignore printf("Incorrect match: [%d]\n", q);
        }
      }

      let my_explosion_of_options = North(7);

      match my_explosion_of_options {
      | South(15..20) -> {
          ignore printf("Incorrect match 15..20\n");
        }
      | North(5) -> {
          ignore printf("Incorrect match: 6\n");
        }
      | South(..15) -> {
          ignore printf("Other bad ranges!\n");
        }
      | South(20..) -> {
          ignore printf("Other bad ranges!\n");
        }
      | North(6.. as a) -> {
          ignore printf("Match! [%d]\n", a);
        }
      | North(..6) -> {
          ignore printf("Other bad ranges!\n");
        }
      }

      let short_circuit_val = if true && false {
        10
      } else if false || false {
        20
      } else if true && true {
        30
      } else {
        40
      };

      ignore printf("Short-circuit val: [%d]\n", short_circuit_val);

      if_is_expr();

      if_is_expr_test();

      phi_test(10, 20);

      ref_array_direct();

      complex_variable_references();

      tuple_interior_references();

      return 0;
    }
  |} in

  Printexc.record_backtrace true ;
  Llvm.enable_pretty_stacktrace () ;

  let timing_lex_start = Unix.gettimeofday () in

  (* Lexing. *)
  let lexbuf = Sedlexing.Latin1.from_gen (Gen.of_string source_text) in
  let tokens = tokenize lexbuf in

  let timing_lex_end = Unix.gettimeofday () in

  print_tokens tokens ;

  let timing_parse_start = Unix.gettimeofday () in

  (* Parsing into module-declaration AST list. *)
  let mod_decls = parse_tokens ~trace:false tokens in

  let timing_parse_end = Unix.gettimeofday () in

  (* Currently require declaration before use, but we build a list of module
  declarations in reverse order. *)
  let mod_decls = List.rev mod_decls in

  let _ =
    List.iter (
      fun decl ->
        Printf.printf "%s\n" (dump_module_decl_ast decl)
    ) mod_decls
  in

  let timing_typecheck_start = Unix.gettimeofday () in

  (* Typechecking. *)
  let mod_decls_tc = type_check_mod_decls mod_decls in

  let timing_typecheck_end = Unix.gettimeofday () in
  let timing_uniquify_varnames_start = Unix.gettimeofday () in

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

  let timing_uniquify_varnames_end = Unix.gettimeofday () in

  (* Print typechecked source. *)
  let asts_fmted =
    List.map
      (fmt_mod_decl ~pretty_unbound:true ~print_typ:true)
      mod_decls_tc_rewritten
  in
  let _ = List.iter (Printf.printf "%s") asts_fmted in

  (* let timing_ast_to_rast_start = Unix.gettimeofday () in
  let timing_ast_to_rast_end = Unix.gettimeofday () in

  let timing_rast_to_hir_start = Unix.gettimeofday () in
  let timing_rast_to_hir_end = Unix.gettimeofday () in

  let timing_hir_to_mir_start = Unix.gettimeofday () in
  let timing_hir_to_mir_end = Unix.gettimeofday () in *)

  let timing_ast_to_rast_to_hir_to_mir_start = Unix.gettimeofday () in

  (* Generate MIR. *)
  let mir_ctxts =
    List.filter_map (
      fun mod_decl ->
        begin match mod_decl with
          | VariantDecl(_) -> None

          | FuncExternDecl(func_decl) ->
              let rfunc_decl = func_decl_t_to_rfunc_decl_t func_decl in

              Printf.printf "RAST:\n%s\n%!" (fmt_rfunc_decl_t rfunc_decl) ;

              let hfunc_decl_t = rfunc_decl_t_to_hfunc_decl_t rfunc_decl in
              let mir_ctxt = hfunc_decl_to_mir hfunc_decl_t in

              Printf.printf
                "RAST-generated MIR:\n%s\n%!"
                (fmt_mir_ctxt mir_ctxt);

              Some(mir_ctxt)
          | FuncDef(func_def) ->
              let rfunc_def = func_def_t_to_rfunc_def_t func_def in

              Printf.printf "RAST:\n%s\n%!" (fmt_rfunc_def_t rfunc_def) ;

              let hfunc_def = rfunc_def_t_to_hfunc_def_t rfunc_def in

              Printf.printf "HIR:\n%s\n%!" (fmt_hfunc_def_t hfunc_def) ;

              let mir_ctxt_from_hir = begin
                let mir_ctxt = hfunc_def_to_mir hfunc_def in
                Printf.printf
                  "HIR-generated MIR:\n%s\n%!"
                  (fmt_mir_ctxt mir_ctxt) ;
                mir_ctxt
              end in

              mir_ctxt_from_hir |> ignore;

              Some(mir_ctxt_from_hir)

        end
    ) mod_decls_tc_rewritten
  in

  let timing_ast_to_rast_to_hir_to_mir_end = Unix.gettimeofday () in

  let timing_llvm_init_start = Unix.gettimeofday () in

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

  let timing_llvm_init_end = Unix.gettimeofday () in

  let mod_gen_ctxt : module_gen_context = {
    func_sigs = StrMap.empty;
    llvm_mod = the_module;
    data_layout_mod = data_layout_mod;
    rast_t_to_llvm_t = rast_t_to_llvm_t llvm_sizeof llvm_ctxt;
    llvm_sizeof = llvm_sizeof;
    validate = true;
    optimize = true;
  } in

  let timing_llvm_codegen_start = Unix.gettimeofday () in

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

  let timing_llvm_codegen_end = Unix.gettimeofday () in
  let timing_output_gen_start = Unix.gettimeofday () in
  let timing_output_ll_start = Unix.gettimeofday () in

  (* Dump various output files from populated LLVM context. *)

  (* Dump LLVM human-readable IR. *)
  let filename_ll = "output.ll" in
  dump_llvm_ir filename_ll the_module ;

  let timing_output_ll_end = Unix.gettimeofday () in
  let timing_output_s_start = Unix.gettimeofday () in

  (* Dump human-readable assembly. *)
  let filename_asm = "output.s" in
  let file_type = Llvm_target.CodeGenFileType.AssemblyFile in
  dump_to_file file_type filename_asm the_fpm the_module ;

  let timing_output_s_end = Unix.gettimeofday () in
  let timing_output_o_start = Unix.gettimeofday () in

  (* Dump machine-readable object file. *)
  let filename_obj = "output.o" in
  let file_type = Llvm_target.CodeGenFileType.ObjectFile in
  dump_to_file file_type filename_obj the_fpm the_module ;

  let timing_output_o_end = Unix.gettimeofday () in
  let timing_output_exe_start = Unix.gettimeofday () in

  (* Dump executable. *)
  let filename_exe = "output" in
  generate_executable filename_exe filename_obj ;

  let timing_output_exe_end = Unix.gettimeofday () in
  let timing_output_gen_end = Unix.gettimeofday () in

  let timing_program_end = Unix.gettimeofday () in

  (* Calcuclate and print timing info for compiler stages. *)
  let _ = begin
    let timing_lex = timing_lex_end -. timing_lex_start in
    let timing_parse = timing_parse_end -. timing_parse_start in
    let timing_typecheck = timing_typecheck_end -. timing_typecheck_start in
    let timing_uniquify_varnames = (
      timing_uniquify_varnames_end -. timing_uniquify_varnames_start
    ) in
    let timing_ast_to_rast_to_hir_to_mir = (
      timing_ast_to_rast_to_hir_to_mir_end -.
      timing_ast_to_rast_to_hir_to_mir_start
    ) in
    let timing_llvm_init = timing_llvm_init_end -. timing_llvm_init_start in
    let timing_llvm_codegen = (
      timing_llvm_codegen_end -. timing_llvm_codegen_start
    ) in
    let timing_output_ll = timing_output_ll_end -. timing_output_ll_start in
    let timing_output_s = timing_output_s_end -. timing_output_s_start in
    let timing_output_o = timing_output_o_end -. timing_output_o_start in
    let timing_output_exe = timing_output_exe_end -. timing_output_exe_start in
    let timing_output_gen = timing_output_gen_end -. timing_output_gen_start in

    let timing_program = timing_program_end -. timing_program_start in

    let timing_lex_pct = 100.0 *. timing_lex /. timing_program in
    let timing_parse_pct = 100.0 *. timing_parse /. timing_program in
    let timing_typecheck_pct = 100.0 *. timing_typecheck /. timing_program in
    let timing_uniquify_varnames_pct =
      100.0 *. timing_uniquify_varnames /. timing_program
    in
    let timing_ast_to_rast_to_hir_to_mir_pct =
      100.0 *. timing_ast_to_rast_to_hir_to_mir /. timing_program
    in
    let timing_llvm_init_pct = 100.0 *. timing_llvm_init /. timing_program in
    let timing_output_ll_pct = 100.0 *. timing_output_ll /. timing_program in
    let timing_output_s_pct = 100.0 *. timing_output_s /. timing_program in
    let timing_output_o_pct = 100.0 *. timing_output_o /. timing_program in
    let timing_output_exe_pct = 100.0 *. timing_output_exe /. timing_program in
    let timing_llvm_codegen_pct =
      100.0 *. timing_llvm_codegen /. timing_program
    in
    let timing_output_gen_pct = 100.0 *. timing_output_gen /. timing_program in

    Printf.printf "timing_lex                      : (%6.2f%%) %f s\n"
      timing_lex_pct
      timing_lex
    ;
    Printf.printf "timing_parse                    : (%6.2f%%) %f s\n"
      timing_parse_pct
      timing_parse
    ;
    Printf.printf "timing_typecheck                : (%6.2f%%) %f s\n"
      timing_typecheck_pct
      timing_typecheck
    ;
    Printf.printf "timing_uniquify_varnames        : (%6.2f%%) %f s\n"
      timing_uniquify_varnames_pct
      timing_uniquify_varnames
    ;
    Printf.printf "timing_ast_to_rast_to_hir_to_mir: (%6.2f%%) %f s\n"
      timing_ast_to_rast_to_hir_to_mir_pct
      timing_ast_to_rast_to_hir_to_mir
    ;
    Printf.printf "timing_llvm_init                : (%6.2f%%) %f s\n"
      timing_llvm_init_pct
      timing_llvm_init
    ;
    Printf.printf "timing_llvm_codegen             : (%6.2f%%) %f s\n"
      timing_llvm_codegen_pct
      timing_llvm_codegen
    ;
    Printf.printf "timing_output_gen               : (%6.2f%%) %f s\n"
      timing_output_gen_pct
      timing_output_gen
    ;
    Printf.printf "  timing_output_ll              : (%6.2f%%) %f s\n"
      timing_output_ll_pct
      timing_output_ll
    ;
    Printf.printf "  timing_output_s               : (%6.2f%%) %f s\n"
      timing_output_s_pct
      timing_output_s
    ;
    Printf.printf "  timing_output_o               : (%6.2f%%) %f s\n"
      timing_output_o_pct
      timing_output_o
    ;
    Printf.printf "  timing_output_exe             : (%6.2f%%) %f s\n"
      timing_output_exe_pct
      timing_output_exe
    ;
    Printf.printf "timing_program                  : (100.00%%) %f s\n"
      timing_program
    ;
    ()
  end in

  ()
;;

