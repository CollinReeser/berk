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

    variant BinaryNoFields {
    | Left
    | Right
    }

    variant Opt<`a> {
    | Some(`a)
    | None
    }

    fn test_tuple() {
      let tup = (1, 2);
      let val = tup.1;

      return;
    }

    fn test_complex_tuple() {
      let tup = (1, ("two", 3, "four"), 5);
      let inner = tup.1;
      let str = inner.2;

      return;
    }

    fn test_variant_decl() {
      let binary_left = Left;
      let binary_right = Right;

      let opt_some = Some(true);
      let opt_none: Opt<bool> = None;

      return;
    }

    fn test_var_decls(): i64 {
      let mut var_one: u8;
      let mut var_two: i16;
      let mut var_three: i64;
      let mut var_four: (string, u8);

      var_one = 5;
      var_two = 1005;
      var_three = 1000000000005;
      var_four = ("Hello!", var_one);

      return var_three;
    }

    fn test_float(): f128 {
      let floating = 12.34f32;
      let doubling = 123.456f64;
      let quadling = 123456.789012f128;

      return quadling;
    }

    fn test_array_expr() {
      let arr1 = [1, 2, 3];
      let arr2 = ["one", "two", "three"];

      return;
    }

    fn test_un_op(in: bool): bool {
      return !in;
    }

    fn test_while() {
      let mut counter_one = 10;
      while {let counter_two = 1;} counter_one > 0 {
        counter_one = counter_one - counter_two;
      }

      return;
    }

    fn dummy_func(i: u32): u32 {
      return i;
    }

    fn func_call() {
      let dummy_var = dummy_func(10);

      return;
    }

    fn func_var_call() {
      let func_var = dummy_func;
      let dummy_var = func_var.(10);

      return;
    }

    fn basic_if() {
      let cond = true;

      if cond {
        let if_arm = 10;
      }
      else {
        let else_arm = 20;
      }

      return;
    }

    fn basic_if_expr(): i32 {
      let cond = true;

      let result =
        if cond {
          10
        }
        else {
          20
        };

      return result;
    }

    fn if_else_if_else_expr(): i32 {
      let value = 10;

      let result =
        if value == 5 {
          500
        }
        else if value == 10 {
          1000
        }
        else if value == 15 {
          1500
        }
        else {
          2000
        };

      return result;
    }

    fn if_or(): i32 {
      let mut val = 0;

      if val == 0 || val == 10 {
        val = val + 10;
      }

      if val == 0 || val == 10 {
        val = val + 10;
      }

      if val == 0 || val == 10 {
        val = val + 10;
      }

      return val;
    }

    fn if_and(): i32 {
      let mut val = 0;

      if val > 0 && val < 10 {
        val = val + 10;
      }

      if val == 0 && val == 10 {
        val = val + 20;
      }

      if val == 0 && val != 10 {
        val = val + 30;
      }

      return val;
    }

    fn basic_match_expr(): i32 {
      let cond = false;

      let result = match cond {
      | true -> 10
      | false -> 20
      };

      return result;
    }

    fn var_bind_match_expr(): i32 {
      let cond = false;

      let result = match cond {
      | true -> 10
      | cond_bind -> 20
      };

      return result;
    }

    fn as_match_expr(): i32 {
      let cond = true;

      let result = match cond {
      | true as true_var -> 10
      | false as false_var -> 20
      };

      return result;
    }

    fn tup_match_simple(): i32 {
      let tup = (true, false, true);

      return match tup {
      | (_, false, _) -> 5
      | (_, true, _) -> 20
      };
    }

    fn match_ints(): (i32, i32, i32) {
      let val = 10;

      let result_one = match val {
      | .. 5 -> 250
      | 5 -> 1000
      | 6 .. -> 2000
      };

      let result_two = match 5 {
      | .. 5 -> 250
      | 5 -> 1000
      | 6 .. -> 2000
      };

      let result_three = match -10 {
      | .. 5 -> 250
      | 5 -> 1000
      | 6 .. -> 2000
      };

      return (result_one, result_two, result_three);
    }

    fn test_block_expr(lhs: u64): u64 {
      let new_lhs = lhs + 5;
      let arg_result = lhs + new_lhs;

      let scope_result = {
        let fst_block_var: u64 = 10;
        let new_block_var: u64 = 15;
        fst_block_var + new_block_var
      };

      return arg_result + scope_result;
    }

    fn test_alloca(): string {
      let a: i64 = -64;
      let b: i16 = -16;
      let c: i32 = -32;
      let d: i8 = -8;
      let e: bool = true;
      let f: (bool, string, i8) = (true, "hello", 6);
      let g: u32 = 32;
      let h: u8 = 8;
      let i: u16 = 16;
      let j: u64 = 64;

      return f.1;
    }

    fn basic_arith(): i8 {
      let a: i8 = 5;
      let b: i8 = 10;
      return a + b;
    }

    fn arg_arith(a: i8, b: i8): i8 {
      return a + b;
    }

    fn func_var(a: i8, b: i8): i8 {
      let arg_arith_func_var = arg_arith;
      let arg_result = arg_arith_func_var.(a, b);

      return arg_result;
    }

    fn test_match_variant(): i32 {
      let opt_val = Some(true);

      let match_result = match opt_val {
      | Some(false) -> 10
      | Some(true) -> 20
      | None -> 30
      };

      return match_result;
    }

    fn test_static_array(a: i32, b: i32, c: u16, d: u16, e: i32): u16 {
      let mut array: [3]u16;

      array[a] = c;
      array[b] = d;

      let val = array[e];

      return val;
    }

    fn test_static_array_multi(
      a: i32, b: i32, c: i32, d: i32,
      e: i16, f: i16, g: i32, h: i32
    ): i16 {
      let mut array: [3][7](i16, i16);

      array[a][b].1 = e;
      array[c][d].1 = f;
      let val = array[g][h].1;

      return val;
    }

    fn test_static_complex(
      a: i32, b: i32, c: i32,
      d: i32, e: i32, f: i32,
      g: i16
    ): i16 {
      let mut array: [3][7]([4]i16, [5]i16);

      array[a][b].1[c] = g;
      let val = array[d][e].1[f];

      return val;
    }

    fn test_static_array_multi_partial(): i16 {
      let mut array: [3][7]i16;

      array[1][2] = 89;
      let inner_arr: ref [7]i16 = array[1];
      let inner_val: i16 = inner_arr[2];

      return inner_val;
    }

    fn test_tuple_ref(): i32 {
      let mut array: [3]([4]i32, [5]i32);

      array[1].0[2] = 55;

      let inner_one: ref ([4]i32, [5]i32) = array[1];
      let inner_two: ref [4]i32 = inner_one.0;

      let val = inner_two[2];

      return val;
    }

    fn test_tuple_ref_2(): i32 {
      let mut tuple: ([4]i32, [5]i32);

      tuple.0[2] = 45;

      let inner_one: ref [4]i32 = tuple.0;
      let val = inner_one[2];

      return val;
    }

    fn test_static_crazy(a: i16): i16 {
      let mut array: [3](
        [4](
          [5]i16, [6]i16
        ),
        [7](
          [8]i16, [9]i16
        )
      );

      array[1].0[2].0[3] = a;

      let inner_one: ref (
        [4](
          [5]i16, [6]i16
        ),
        [7](
          [8]i16, [9]i16
        )
      ) = array[1];

      let inner_two: ref [4](
        [5]i16, [6]i16
      ) = inner_one.0;

      let inner_three: ref (
        [5]i16, [6]i16
      ) = inner_two[2];

      let inner_four: ref [5]i16 = inner_three.0;

      let inner_five: i16 = inner_four[3];

      return inner_five;
    }

    fn test_default_init() {
      let a: i64;
      let b: i32;
      let c: i16;
      let d: i8;
      let e: u64;
      let f: u32;
      let g: u16;
      let h: u8;
      let i: f128;
      let j: f64;
      let k: f32;
      let l: bool;
      let m: string;
      let n: (u32, i64, u8);
      let o: (string, bool);
      let p: ((i8, u64, i32), u16, (bool, string));
      let q: [10]i32;
      let r: [10][20]i32;
      let s: [10](u32, i64);
      let t: [10]([20]u32, [30]i64);
      let u: [2]([3](i16, string), [4]([5]bool, f32));
      let v: ([3](i16, string), [4]([5]bool, f32));

      ignore printf("a: %lld\n", a);
      ignore printf("b: %d\n", b);
      ignore printf("c: %hd\n", c);
      ignore printf("d: %hhd\n", d);
      ignore printf("e: %llu\n", e);
      ignore printf("f: %u\n", f);
      ignore printf("g: %hu\n", g);
      ignore printf("h: %hhu\n", h);
      ignore printf("i: %Lf\n", i);
      ignore printf("j: %f\n", j);
      ignore printf("k: %f\n", h);
      ignore printf("l: %hhd\n", l);
      ignore printf("m: \"%s\"\n", m);
      ignore printf("n: (%u, %lld, %hhu)\n", n.0, n.1, n.2);
      ignore printf("o: (\"%s\", %hhd)\n", o.0, o.1);
      ignore printf(
        "p: ((%hhd, %llu, %d), %hu, (%hhd, \"%s\"))\n",
        p .0 .0, p .0 .1, p .0 .2,
        p .1,
        p .2 .0, p .2 .1
      );

      {
        ignore printf("u: [\n");
        while {let mut idx = 0;} idx < 2 {
          let top_level_tuple_lhs_arr: ref [3](i16, string) = u[idx].0;

          ignore printf("  (\n");
          ignore printf("    [\n");
          while {let mut jdx = 0;} jdx < 3 {
            let inner_lhs_i16 = top_level_tuple_lhs_arr[jdx].0;
            let inner_rhs_str = top_level_tuple_lhs_arr[jdx].1;

            ignore printf("      (%hd, \"%s\"),\n", inner_lhs_i16, inner_rhs_str);

            jdx = jdx + 1;
          }
          ignore printf("    ],\n");

          let top_level_tuple_rhs_arr: ref [4]([5]bool, f32) = u[idx].1;

          ignore printf("    [\n");
          while {let mut kdx = 0;} kdx < 4 {
            let inner_bool_arr: ref [5]bool = top_level_tuple_rhs_arr[kdx].0;

            ignore printf("      ([");
            while {let mut ldx = 0;} ldx < 5 {
              let inner_lhs_bool = inner_bool_arr[ldx];

              if ldx < 4 {
                ignore printf("%hhd, ", inner_lhs_bool);
              }
              else {
                ignore printf("%hhd", inner_lhs_bool);
              }

              ldx = ldx + 1;
            }
            ignore printf("], ");

            let inner_rhs_f32 = top_level_tuple_rhs_arr[kdx].1;

            ignore printf("%.1f),\n", inner_rhs_f32);

            kdx = kdx + 1;
          }
          ignore printf("    ],\n");
          ignore printf("  ),\n");

          idx = idx + 1;
        }
        ignore printf("]\n");
      }

      {
        ignore printf("v: (\n");

        let top_level_tuple_lhs_arr: ref [3](i16, string) = v.0;

        ignore printf("  [\n");
        while {let mut mdx = 0;} mdx < 3 {
          let inner_lhs_i16 = top_level_tuple_lhs_arr[mdx].0;
          let inner_rhs_str = top_level_tuple_lhs_arr[mdx].1;

          ignore printf("    (%hd, \"%s\"),\n", inner_lhs_i16, inner_rhs_str);

          mdx = mdx + 1;
        }
        ignore printf("  ],\n");

        let top_level_tuple_rhs_arr: ref [4]([5]bool, f32) = v.1;

        ignore printf("  [\n");
        while {let mut ndx = 0;} ndx < 4 {
          let inner_bool_arr: ref [5]bool = top_level_tuple_rhs_arr[ndx].0;

          ignore printf("    ([");
          while {let mut odx = 0;} odx < 5 {
            let inner_lhs_bool = inner_bool_arr[odx];

            if odx < 4 {
              ignore printf("%hhd, ", inner_lhs_bool);
            }
            else {
              ignore printf("%hhd", inner_lhs_bool);
            }

            odx = odx + 1;
          }
          ignore printf("], ");

          let inner_rhs_f32 = top_level_tuple_rhs_arr[ndx].1;

          ignore printf("%.1f),\n", inner_rhs_f32);

          ndx = ndx + 1;
        }
        ignore printf("  ],\n");

        ignore printf(")\n");
      }

      return;
    }

    fn main(): i8 {
      {
        let if_or_result = if_or();
        ignore printf("Got [%d] | [%d] Expected\n", if_or_result, 20);
      }
      {
        let if_and_result = if_and();
        ignore printf("Got [%d] | [%d] Expected\n", if_and_result, 30);
      }
      {
        let if_else_if_else_expr_result = if_else_if_else_expr();
        ignore printf(
          "Got [%d] | [%d] Expected\n", if_else_if_else_expr_result, 1000
        );
      }
      {
        let basic_match_expr_result = basic_match_expr();
        ignore printf(
          "Got [%d] | [%d] Expected\n", basic_match_expr_result, 20
        );
      }
      {
        let var_bind_match_expr_result = var_bind_match_expr();
        ignore printf(
          "Got [%d] | [%d] Expected\n", var_bind_match_expr_result, 20
        );
      }
      {
        let as_match_expr_result = as_match_expr();
        ignore printf("Got [%d] | [%d] Expected\n", as_match_expr_result, 10);
      }
      {
        let tup_match_simple_result = tup_match_simple();
        ignore printf("Got [%d] | [%d] Expected\n", tup_match_simple_result, 5);
      }
      {
        let match_ints_res = match_ints();
        ignore printf(
          "Got [%d, %d, %d] | [%d, %d, %d] Expected\n",
          match_ints_res.0, match_ints_res.1, match_ints_res.2,
          2000, 1000, 250
        );
      }
      {
        let test_block_expr_result = test_block_expr(20);
        ignore printf("Got [%d] | [%d] Expected\n", test_block_expr_result, 70);
      }
      {
        let test_alloca_str = test_alloca();
        ignore printf("Got [%s] | [%s] Expected\n", test_alloca_str, "hello");
      }
      {
        let basic_arith_result = basic_arith();
        ignore printf("Got [%d] | [%d] Expected\n", basic_arith_result, 15);
      }
      {
        let arg_arith_result: i8 = arg_arith(-15, 10);
        let arg_arith_expected: i8 = -5;
        ignore printf(
          "Got [%hhd] | [%hhd] Expected\n",
          arg_arith_result, arg_arith_expected
        );
      }
      {
        let func_var_result = func_var(1, 2);
        ignore printf("Got [%d] | [%d] Expected\n", func_var_result, 3);
      }
      {
        let test_static_array_result_1 = test_static_array(1, 2, 17, 19, 1);
        ignore printf(
          "Got [%hd] | [%hd] Expected\n", test_static_array_result_1, 17
        );

        let test_static_array_result_2 = test_static_array(1, 2, 17, 19, 2);
        ignore printf(
          "Got [%hd] | [%hd] Expected\n", test_static_array_result_2, 19
        );
      }
      {
        let test_static_array_multi_result_1 = test_static_array_multi(
          1, 2, 3, 4, 27, 29, 1, 2
        );
        ignore printf(
          "Got [%hd] | [%hd] Expected\n", test_static_array_multi_result_1, 27
        );

        let test_static_array_multi_result_2 = test_static_array_multi(
          1, 2, 3, 4, 27, 29, 3, 4
        );
        ignore printf(
          "Got [%hd] | [%hd] Expected\n", test_static_array_multi_result_2, 29
        );
      }
      {
        let test_static_complex_result = test_static_complex(
          1, 2, 3,
          1, 2, 3,
          99
        );
        ignore printf(
          "Got [%hd] | [%hd] Expected\n", test_static_complex_result, 99
        );
      }
      {
        let test_static_array_multi_partial_result =
          test_static_array_multi_partial();

        ignore printf(
          "Got [%hd] | [%hd] Expected\n",
          test_static_array_multi_partial_result,
          89
        );
      }
      {
        let test_tuple_ref_result = test_tuple_ref();

        ignore printf(
          "Got [%d] | [%d] Expected\n", test_tuple_ref_result, 55
        );
      }
      {
        let test_tuple_ref_2_result = test_tuple_ref_2();

        ignore printf(
          "Got [%d] | [%d] Expected\n", test_tuple_ref_2_result, 45
        );
      }
      {
        let test_static_crazy_result = test_static_crazy(101);

        ignore printf(
          "Got [%hd] | [%hd] Expected\n", test_static_crazy_result, 101
        );
      }
      {
        test_default_init();
      }

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
        | FuncExternTemplateDecl(_, _)
        | FuncTemplateDef(_, _) ->
            failwith (
              Printf.sprintf
                "Mod decl should not have survived typechecking: [[ %s ]]\n"
                (fmt_mod_decl mod_decl)
            )

        | FuncDef(func_def) ->
            let func_def_rewritten = rewrite_to_unique_varnames func_def in
            FuncDef(func_def_rewritten)

        | GeneratorDef(generator_def) ->
            let generator_def_rewritten =
              rewrite_gen_to_unique_varnames generator_def
            in
            GeneratorDef(generator_def_rewritten)

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
          | FuncExternTemplateDecl(_, _)
          | FuncTemplateDef(_, _) ->
              failwith (
                Printf.sprintf
                  "Mod decl should not have survived typechecking: [[ %s ]]\n"
                  (fmt_mod_decl mod_decl)
              )

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

          | GeneratorDef(generator_def) ->
              let rgenerator_def =
                generator_def_t_to_rgenerator_def_t generator_def
              in

              Printf.printf "RAST:\n%s\n%!"
                (fmt_rgenerator_def_t rgenerator_def)
              ;

              let hgenerator_def =
                rgenerator_def_t_to_hgenerator_def_t rgenerator_def
              in

              Printf.printf "HIR:\n%s\n%!"
                (fmt_hgenerator_def_t hgenerator_def)
              ;

              let mir_ctxt_from_hir = begin
                let mir_ctxt = hgenerator_def_to_mir hgenerator_def in
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
    llvm_ctxt = llvm_ctxt;
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

  (* Dump various output files from populated LLVM context. *)

  let timing_output_gen_start = Unix.gettimeofday () in

  Printf.printf "Generating human-readable LLVM *.ll file...\n%!";

  let timing_output_ll_start = Unix.gettimeofday () in

  (* Dump LLVM human-readable IR. *)
  let filename_ll = "output.ll" in
  dump_llvm_ir filename_ll the_module ;

  let timing_output_ll_end = Unix.gettimeofday () in

  Printf.printf "Generating human-readable ASM *.s file...\n%!";

  let timing_output_s_start = Unix.gettimeofday () in

  (* Dump human-readable assembly. *)
  let filename_asm = "output.s" in
  let file_type = Llvm_target.CodeGenFileType.AssemblyFile in
  dump_to_file file_type filename_asm the_fpm the_module ;

  let timing_output_s_end = Unix.gettimeofday () in

  Printf.printf "Generating machine-readable object *.o file...\n%!";

  let timing_output_o_start = Unix.gettimeofday () in

  (* Dump machine-readable object file. *)
  let filename_obj = "output.o" in
  let file_type = Llvm_target.CodeGenFileType.ObjectFile in
  dump_to_file file_type filename_obj the_fpm the_module ;

  let timing_output_o_end = Unix.gettimeofday () in

  Printf.printf "Generating executable file...\n%!";

  let timing_output_exe_start = Unix.gettimeofday () in

  (* Dump executable. *)
  let filename_exe = "output" in
  generate_executable filename_exe filename_obj ;

  let timing_output_exe_end = Unix.gettimeofday () in
  let timing_output_gen_end = Unix.gettimeofday () in

  let timing_program_end = Unix.gettimeofday () in

  Printf.printf "Done compiling.\n%!";

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

