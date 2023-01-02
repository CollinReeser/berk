open Berk.Typing

let berk_t_tst = Alcotest.testable pprint_berk_t (=)

let test_common_type_of_lst expect given () = Alcotest.(check' berk_t_tst)
  ~msg:"common_type_of_lst"
  ~expected:expect
  ~actual:(common_type_of_lst given)

let common_type = let open Alcotest in [(
  test_case "lst_sanity" `Quick (
    test_common_type_of_lst (
      Variant("Tri", [
        ("A", U64); ("B", Tuple([I32; U32])); ("C", Tuple([String; Bool; I16]));
      ])
    )
    [
      Variant("Tri", [
        ("A", U64); ("B", Tuple([I32; U32])); ("C", Tuple([String; Bool; I16]));
      ]);
      Variant("Tri", [
        ("A", U64); ("B", Tuple([I32; U32])); ("C", Tuple([String; Bool; I16]));
      ]);
    ]
  )
); (
  test_case "implicit_type_promotion" `Quick (
    test_common_type_of_lst (
      Variant("Tri", [
        ("A", U64); ("B", Tuple([I32; U32])); ("C", Tuple([String; Bool; I16]));
      ])
    )
    [
      Variant("Tri", [
        ("A", U32); ("B", Tuple([I32; U8])); ("C", Tuple([String; Bool; I8]));
      ]);
      Variant("Tri", [
        ("A", U16); ("B", Tuple([I16; U16])); ("C", Tuple([String; Bool; I16]));
      ]);
      Variant("Tri", [
        ("A", U64); ("B", Tuple([I8; U32])); ("C", Tuple([String; Bool; I8]));
      ]);
    ]
  )
); (
  test_case "resolve_tvars" `Quick (
    test_common_type_of_lst (
      Variant("Tri", [
        ("A", U64); ("B", Tuple([I32; U16])); ("C", Tuple([String; Bool; I16]));
      ])
    )
    [
      Variant("Tri", [
        ("A", Unbound("`a"));
        ("B", Tuple([I32; Unbound("`c")]));
        ("C", Tuple([Unbound("`d"); Bool; I16]));
      ]);
      Variant("Tri", [
        ("A", Unbound("`a"));
        ("B", Tuple([Unbound("`b"); U16]));
        ("C", Tuple([String; Unbound("`e"); I8]));
      ]);
      Variant("Tri", [
        ("A", U64);
        ("B", Tuple([Unbound("`b"); Unbound("`c")]));
        ("C", Tuple([String; Bool; Unbound("`f")]));
      ]);
    ]
  )
);]

let () =
  let open Alcotest in
  run "Typing" [
    ("common_type", common_type);
  ]
