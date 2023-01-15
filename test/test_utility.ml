open Berk.Utility

let test_tuplify () =
  Alcotest.(check' (list (pair int int)))
    ~msg:"tuplify"
    ~expected:[(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (3, 4)]
    ~actual:(List.sort compare (list_to_2_tuples [1; 2; 3; 4]))

let test_fmt_join_strs expected delim given () =
  Alcotest.(check' string)
    ~msg:"fmt_join_strs"
    ~expected:expected
    ~actual:(fmt_join_strs delim given)

let test_combine3 check expected lhs mid rhs () =
  check
    ~msg:"combine3"
    ~expected:expected
    ~actual:(combine3 lhs mid rhs)

let test_cartesian_product expected given () =
  Alcotest.(check' (list (list int)))
    ~msg:"cartesian_product2"
    ~expected:expected
    ~actual:(cartesian_product given)

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
    ];
    "combine3", [
      test_case "combine3" `Quick (
        test_combine3 Alcotest.(check' (list (triple int int int)))
          [] [] [] []
      );
      test_case "combine3" `Quick (
        test_combine3 Alcotest.(check' (list (triple int int int)))
          [(1, 2, 3)] [1] [2] [3]
      );
      test_case "combine3" `Quick (
        test_combine3 Alcotest.(check' (list (triple int string int)))
          [(1, "a", 100); (2, "b", 200); (3, "c", 300)]
          [1; 2; 3]
          ["a"; "b"; "c"]
          [100; 200; 300]
      );
    ];
    "cartesian_product", [
      test_case "cartesian_product" `Quick (test_cartesian_product
          []
          []
      );
      test_case "cartesian_product" `Quick (test_cartesian_product
          [[1]; [2]]
          [[1; 2]]
      );
      test_case "cartesian_product" `Quick (test_cartesian_product
          [[2; 3]; [2; 4]; [1; 3]; [1; 4]]
          [[1; 2]; [3; 4]]
      );
      test_case "cartesian_product" `Quick (test_cartesian_product
          [[1; 3]; [1; 4]]
          [[1]; [3; 4]]
      );
      test_case "cartesian_product" `Quick (test_cartesian_product
          [[2; 3]; [1; 3]]
          [[1; 2]; [3]]
      );
      test_case "cartesian_product" `Quick (test_cartesian_product
          [[3]; [4]]
          [[]; [3; 4]]
      );
      test_case "cartesian_product" `Quick (test_cartesian_product
          [[1]; [2]]
          [[1; 2]; []]
      );
      test_case "cartesian_product" `Quick (test_cartesian_product
          [
            [2; 4; 5]; [2; 4; 6]; [2; 4; 7]; [2; 3; 5]; [2; 3; 6]; [2; 3; 7];
            [1; 4; 5]; [1; 4; 6]; [1; 4; 7]; [1; 3; 5]; [1; 3; 6]; [1; 3; 7]
          ]
          [[1; 2]; [3; 4]; [5; 6; 7]]
      );
    ];
  ]
