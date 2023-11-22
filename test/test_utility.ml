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

let test_fold_left_map2 expected f acc lhs rhs () =
  Alcotest.(check' (pair int (list int)))
    ~msg:"fold_left_map2"
    ~expected:expected
    ~actual:(fold_left_map2 f acc lhs rhs)

let test_map2i expected f lhs rhs () =
  Alcotest.(check' (list string))
    ~msg:"map2i"
    ~expected:expected
    ~actual:(map2i f lhs rhs)

let test_partition_i expected i ls () =
  Alcotest.(check' (pair (list int) (list int)))
    ~msg:"partition_i"
    ~expected:expected
    ~actual:(partition_i i ls)

let test_take_with_tail expected n ls () =
  Alcotest.(check' (pair (list int) (list int)))
    ~msg:"take_with_tail"
    ~expected:expected
    ~actual:(take_with_tail n ls)

let test_insert expected lst idx elem () =
  Alcotest.(check' (list string))
    ~msg:"insert"
    ~expected:expected
    ~actual:(insert lst idx elem)

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
    "fold_left_map2", [
      test_case "fold_left_map2" `Quick (
        let f acc lhs rhs =
          let acc' = acc + lhs + rhs in
          (acc', lhs + rhs)
        in
        test_fold_left_map2
          (35, [3; 5; 7; 9; 11])
          f 0 [1; 2; 3; 4; 5] [2; 3; 4; 5; 6]
      );
    ];
    "map2i", [
      test_case "map2i" `Quick (
        let f i lhs rhs =
          Printf.sprintf "%d_%s_%s" i lhs rhs
        in
        test_map2i
          ["0_a_x"; "1_b_y"; "2_c_z"]
          f ["a"; "b"; "c"] ["x"; "y"; "z"]
      );
    ];
    "partition_i", [
      test_case "partition_i" `Quick (
        test_partition_i
          ([], [])
          0 []
      );
      test_case "partition_i" `Quick (
        test_partition_i
          ([], [])
          3 []
      );
      test_case "partition_i" `Quick (
        test_partition_i
          ([1], [3])
          1 [1; 2; 3]
      );
      test_case "partition_i" `Quick (
        test_partition_i
          ([], [2; 3])
          0 [1; 2; 3]
      );
      test_case "partition_i" `Quick (
        test_partition_i
          ([1; 2], [])
          2 [1; 2; 3]
      );
      test_case "partition_i" `Quick (
        test_partition_i
          ([1; 2; 3], [])
          3 [1; 2; 3]
      );
    ];
    "take_with_tail", [
      test_case "take_with_tail" `Quick (
        test_take_with_tail
          ([], [])
          0 []
      );
      test_case "take_with_tail" `Quick (
        test_take_with_tail
          ([1; 2; 3], [])
          3 [1; 2; 3]
      );
      test_case "take_with_tail" `Quick (
        test_take_with_tail
          ([1; 2], [3])
          2 [1; 2; 3]
      );
      test_case "take_with_tail" `Quick (
        test_take_with_tail
          ([1], [2; 3])
          1 [1; 2; 3]
      );
      test_case "take_with_tail" `Quick (
        test_take_with_tail
          ([], [1; 2; 3])
          0 [1; 2; 3]
      );
    ];
    "insert", [
      test_case "insert" `Quick (
        test_insert
          ["new"]
          [] 0 "new"
      );
      test_case "insert" `Quick (
        test_insert
          ["new"; "old"; "old"]
          ["old"; "old"] 0 "new"
      );
      test_case "insert" `Quick (
        test_insert
          ["old"; "new"; "old"]
          ["old"; "old"] 1 "new"
      );
      test_case "insert" `Quick (
        test_insert
          ["old"; "old"; "new"]
          ["old"; "old"] 2 "new"
      );
    ];
  ]
