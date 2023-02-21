open Berk.Ast
open Berk.Lexer
open Berk.Parser
open Berk.Type_check


let () =
  let text = {|
    extern fn printf(fmt: string, ...): i32

    fn main(): i8 {
      let my_str := "Hello, world! [%d]\n";
      let var := 6;
      printf(my_str, var);

      return 0;
    }
  |} in
  let lexbuf = Sedlexing.Latin1.from_gen (Gen.of_string text) in
  let tokens = tokenize lexbuf in
  print_tokens tokens ;

  let mod_decls = parse_tokens tokens in

  (* Currently require declaration before use. *)
  let mod_decls = List.rev mod_decls in

  let mod_decls_tc = type_check_mod_decls mod_decls in
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

  let asts_fmted =
    List.map
      (fmt_mod_decl ~pretty_unbound:true ~print_typ:true)
      mod_decls_tc_rewritten
  in
  let _ = List.iter (Printf.printf "%s") asts_fmted in
  ()
;;

