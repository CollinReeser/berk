open Berk.Utility

let test_tuplify () =
  Alcotest.(check' (list (pair int int)))
    ~msg:"tuplify"
    ~expected:[(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (3, 4)]
    ~actual:(List.sort compare (list_to_2_tuples [1; 2; 3; 4]))

let () =
  let open Alcotest in
  run "Utility" [
    "tuplify", [
        test_case "tuplify" `Quick test_tuplify;
      ];
    ]
