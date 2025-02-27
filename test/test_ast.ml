open Berk.Ast
open Berk.Typing

let expr_tst = Alcotest.testable pprint_expr (=)

let test_inject_type_into_expr expect (given_typ, given_exp) () =
  Alcotest.(check' expr_tst)
    ~msg:"inject_type_into_expr"
    ~expected:expect
    ~actual:(inject_type_into_expr given_typ given_exp)

let inject_type = let open Alcotest in [(
  let bounded_variant
    ?(a=Unbound("`a")) ?(b=Unbound("`b")) ?(c=Unbound("`c")) ?(d=Unbound("`d"))
    ()
  = begin
    Variant(
      "Ternary", [
        {name="Off";      fields=[{t=a}; {t=b}]};
        {name="On";       fields=[{t=b}; {t=c}]};
        {name="Unstable"; fields=[{t=String}; {t=d}]};
      ]
    )
  end in
  let resolved_variant = bounded_variant ~a:I32 ~b:String ~c:F32 ~d:Bool () in
  test_case "interesting" `Quick
    (
      test_inject_type_into_expr (
        IfThenElseExpr(
          resolved_variant,
          ValBool(true),
          VariantCtorExpr(
            resolved_variant, "Off",
            [ValCast(I32, Extend, ValInt(I16, 123)); ValStr("!")]
          ),
          VariantCtorExpr(
            resolved_variant, "On",
            [ValStr("?"); ValF32(1.2)]
          )
        )
      ) (
        bounded_variant ~a:I32 ~d:Bool (), (
          IfThenElseExpr(
            bounded_variant (),
            ValBool(true),
            VariantCtorExpr(
              bounded_variant ~a:I16 ~b:String (), "Off",
              [ValInt(I16, 123); ValStr("!")]
            ),
            VariantCtorExpr(
              bounded_variant ~b:String ~c:F32 (), "On",
              [ValStr("?"); ValF32(1.2)]
            )
          )
        )
      )
    )
  );
]

let () =
  let open Alcotest in
  run "Ast" [
    ("inject_type", inject_type);
  ]
