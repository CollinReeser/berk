open Berk.Mir

open Berk.Ast
open Berk.Type_check

let ast_raw = begin
  IfThenElseExpr(
    Undecided,
    BinOp(Undecided, Eq, ValU8(1), ValU8(2)),
    ValU64(20),
    ValU64(30)
  )
end

let ast_typechecked = type_check_expr (default_tc_ctxt Nil) Undecided ast_raw

let mir_ctxt_tst = Alcotest.testable pprint_mir_ctxt (=)

let mir_ctxt_default = {name_gen=0; lvars=StrMap.empty; bbs=StrMap.empty}

let test_expr_to_mir expect given () =
  let bb = {name="entry"; instrs=[]} in
  let mir_ctxt = {
    name_gen=0; lvars=StrMap.empty; bbs=StrMap.add "entry" bb StrMap.empty
  } in
  let (mir_ctxt_actual, _, _) = expr_to_mir mir_ctxt bb given in
  Alcotest.(check' mir_ctxt_tst)
    ~msg:"expr_to_mir"
    ~expected:expect
    ~actual:mir_ctxt_actual

let gen_mir = let open Alcotest in [(
  test_case "interesting" `Quick (
    test_expr_to_mir mir_ctxt_default ast_typechecked
  )
)]

let () =
  let open Alcotest in
  run "Mir" [
    ("bb_mir", gen_mir);
  ]
