open Berk.Typing

let berk_t_tst = Alcotest.testable pprint_berk_t (=)

let test_common_type_of_lst expect given () =
  Alcotest.(check' berk_t_tst)
    ~msg:"common_type_of_lst"
    ~expected:expect
    ~actual:(common_type_of_lst given)

let common_type = let open Alcotest in [(
  test_case "lst_sanity" `Quick (
    test_common_type_of_lst (
      Variant("Tri", [
        {name="A"; fields=[{t=U64}]};
        {name="B"; fields=[{t=I32}; {t=U32}]};
        {name="C"; fields=[{t=String}; {t=Bool}; {t=I16}]};
      ])
    )
    [
      Variant("Tri", [
        {name="A"; fields=[{t=U64}]};
        {name="B"; fields=[{t=I32}; {t=U32}]};
          {name="C"; fields=[{t=String}; {t=Bool}; {t=I16}]};
      ]);
      Variant("Tri", [
        {name="A"; fields=[{t=U64}]};
        {name="B"; fields=[{t=I32}; {t=U32}]};
          {name="C"; fields=[{t=String}; {t=Bool}; {t=I16}]};
      ]);
    ]
  )
); (
  test_case "implicit_type_promotion" `Quick (
    test_common_type_of_lst (
      Variant("Tri", [
        {name="A"; fields=[{t=U64}]};
        {name="B"; fields=[{t=I32}; {t=U32}]};
          {name="C"; fields=[{t=String}; {t=Bool}; {t=I16}]};
      ])
    )
    [
      Variant("Tri", [
        {name="A"; fields=[{t=U32}]};
        {name="B"; fields=[{t=I32}; {t=U8}]};
          {name="C"; fields=[{t=String}; {t=Bool}; {t=I8}]};
      ]);
      Variant("Tri", [
        {name="A"; fields=[{t=U16}]};
        {name="B"; fields=[{t=I16}; {t=U16}]};
          {name="C"; fields=[{t=String}; {t=Bool}; {t=I16}]};
      ]);
      Variant("Tri", [
        {name="A"; fields=[{t=U64}]};
        {name="B"; fields=[{t=I8}; {t=U32}]};
          {name="C"; fields=[{t=String}; {t=Bool}; {t=I8}]};
      ]);
    ]
  )
); (
  test_case "resolve_tvars" `Quick (
    test_common_type_of_lst (
      Variant("Tri", [
        {name="A"; fields=[{t=U64}]};
        {name="B"; fields=[{t=I32}; {t=U16}]};
        {name="C"; fields=[{t=String}; {t=Bool}; {t=I16}]};
      ])
    )
    [
      Variant("Tri", [
        {name="A"; fields=[{t=Unbound("`a")}]};
        {name="B"; fields=[{t=I32}; {t=Unbound("`c")}]};
        {name="C"; fields=[{t=Unbound("`d")}; {t=Bool}; {t=I16}]};
      ]);
      Variant("Tri", [
        {name="A"; fields=[{t=Unbound("`a")}]};
        {name="B"; fields=[{t=Unbound("`b")}; {t=U16}]};
        {name="C"; fields=[{t=String}; {t=Unbound("`e")}; {t=I8}]};
      ]);
      Variant("Tri", [
        {name="A"; fields=[{t=U64}]};
        {name="B"; fields=[{t=Unbound("`b")}; {t=Unbound("`c")}]};
        {name="C"; fields=[{t=String}; {t=Bool}; {t=Unbound("`f")}]};
      ]);
    ]
  )
);]

let () =
  let open Alcotest in
  run "Typing" [
    ("common_type", common_type);
  ]
