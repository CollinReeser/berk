open Berk.Typing

let berk_t_tst = Alcotest.testable pprint_berk_t (=)

let test_common_type_of_lst () = Alcotest.(check' berk_t_tst)
  ~msg:"common_type"
  ~expected:(
    Variant("Tri", [
      ("One", U64);
      ("Two", Tuple([I32; U32]));
      ("Three", Tuple([String; Bool; I8]));
    ])
  ) ~actual: (
    Variant("Tri", [
      ("One", U64);
      ("Two", Tuple([I32; U32]));
      ("Three", Tuple([String; Bool; I8]));
    ])
  )

let () =
  let open Alcotest in
  run "Typing" [
    "common_type", [
        test_case "common_type" `Quick test_common_type_of_lst;
      ];
    ]
