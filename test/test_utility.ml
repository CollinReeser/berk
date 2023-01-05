open Berk.Utility

let test_tuplify () =
  Alcotest.(check' (list (pair int int)))
    ~msg:"tuplify"
    ~expected:[(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (3, 4)]
    ~actual:(List.sort compare (list_to_2_tuples [1; 2; 3; 4]))

let test_fmt_join_strs expected delim given () =
  Alcotest.(check' string)
    ~msg:"tuplify"
    ~expected:expected
    ~actual:(fmt_join_strs delim given)

let () =
  let open Alcotest in
  run "Utility" [
    "tuplify", [
      test_case "tuplify" `Quick test_tuplify;
    ];
    "join_strs", [
      test_case "sanity" `Quick (test_fmt_join_strs "" "" [""]);
      test_case "sanity" `Quick (test_fmt_join_strs "1" "" ["1"]);
      test_case "sanity" `Quick (test_fmt_join_strs "1" ", " ["1"]);
      test_case "join" `Quick (test_fmt_join_strs "1, 2" ", " ["1"; "2"]);
      test_case "join" `Quick (test_fmt_join_strs "12" "" ["1"; "2"]);
      test_case "join" `Quick (test_fmt_join_strs "1 ; 2" " ; " ["1"; "2"]);
      test_case "join" `Quick (test_fmt_join_strs "1;2" ";" ["1"; "2"]);
      test_case "join" `Quick (test_fmt_join_strs "1, 2, 3" ", " ["1"; "2"; "3"]);
    ]
  ]
