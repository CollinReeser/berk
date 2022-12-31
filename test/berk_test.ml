(* open Berk_ocaml.Utility *)

let test_lowercase () =
  Alcotest.(check string) "same string" "hello!" (String.lowercase_ascii "hELLO!")

let () =
  let open Alcotest in
  run "Utils" [
    "string-case", [
        test_case "Lower case" `Quick test_lowercase;
      ];
    ]
