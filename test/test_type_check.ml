open Berk.Ast
open Berk.Type_check
open Berk.Typing

let pattern_tst = Alcotest.testable pprint_pattern (=)

let test_pattern_dominates expect lhs rhs () =
  Alcotest.(check' bool)
    ~msg:"pattern_dominates"
    ~expected:expect
    ~actual:(pattern_dominates lhs rhs)

let test_generate_value_patts expect given () =
  Alcotest.(check' (list pattern_tst))
    ~msg:"generate_value_patts"
    ~expected:expect
    ~actual:(generate_value_patts given)

let test_determine_pattern_completeness expect lhs_given rhs_given () =
  Alcotest.(check' (pair (list pattern_tst) (list pattern_tst)))
    ~msg:"determine_pattern_completeness"
    ~expected:expect
    ~actual:(determine_pattern_completeness lhs_given rhs_given)

let variant_option_bool = Variant("Option", [("Some", Bool); ("None", Nil)])
let variant_left_right = Variant(
  "LeftRight", [("Left", variant_option_bool); ("Right", variant_option_bool)]
)

let pattern_domination = let open Alcotest in [
  (test_case "bool_sanity" `Quick (
    test_pattern_dominates true (PBool(true)) (PBool(true))));
  (test_case "bool_sanity" `Quick (
    test_pattern_dominates true (PBool(false)) (PBool(false))));
  (test_case "bool_rev" `Quick (
    test_pattern_dominates false (PBool(true)) (PBool(false))));
  (test_case "bool_rev" `Quick (
    test_pattern_dominates false (PBool(false)) (PBool(true))));
  (test_case "bool_wild" `Quick (
    test_pattern_dominates true (Wild(Undecided)) (PBool(false))));
  (test_case "bool_var" `Quick (
    test_pattern_dominates true (VarBind(Undecided, "x")) (PBool(false))));
  (test_case "ctor_wild" `Quick (
    test_pattern_dominates true (
      Wild(Undecided)
    ) (
      Ctor(variant_option_bool, "Some", Wild(Undecided))
    )
  ));
  (test_case "ctor_var" `Quick (
    test_pattern_dominates true (
      VarBind(Undecided, "x")
    ) (
      Ctor(variant_option_bool, "Some", Wild(Undecided))
    )
  ));
  (test_case "ctor_full_match" `Quick (
    test_pattern_dominates true (
      Ctor(variant_option_bool, "Some", PBool(true))
    ) (
      Ctor(variant_option_bool, "Some", PBool(true))
    )
  ));
  (test_case "ctor_full_non_match" `Quick (
    test_pattern_dominates false (
      Ctor(variant_option_bool, "Some", PBool(true))
    ) (
      Ctor(variant_option_bool, "Some", PBool(false))
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates true (
      Wild(variant_left_right)
    ) (
      Ctor(
        variant_left_right, "Left",
        Ctor(variant_option_bool, "Some", PBool(false))
      )
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates true (
      Ctor(variant_left_right, "Left", Wild(variant_option_bool))
    ) (
      Ctor(
        variant_left_right, "Left",
        Ctor(variant_option_bool, "Some", PBool(false))
      )
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates true (
      Ctor(
        variant_left_right, "Left",
        Ctor(variant_option_bool, "Some", Wild(Bool))
      )
    ) (
      Ctor(
        variant_left_right, "Left",
        Ctor(variant_option_bool, "Some", PBool(false))
      )
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates false (
      Ctor(variant_left_right, "Right", Wild(variant_option_bool))
    ) (
      Ctor(
        variant_left_right, "Left",
        Ctor(variant_option_bool, "Some", PBool(false))
      )
    )
  ));
]

let value_patts = let open Alcotest in [
  (test_case "bool_vals" `Quick (
    test_generate_value_patts
      [PBool(true); PBool(false)]
      Bool
  ));
  (test_case "option_vals" `Quick (
    test_generate_value_patts
      [
        Ctor(variant_option_bool, "Some", PBool(true));
        Ctor(variant_option_bool, "Some", PBool(false));
        Ctor(variant_option_bool, "None", PNil);
      ]
      variant_option_bool
  ));
  (test_case "nested_variant_vals" `Quick (
    test_generate_value_patts
      [
        Ctor(
          variant_left_right, "Left",
          Ctor(variant_option_bool, "Some", PBool(true))
        );
        Ctor(
          variant_left_right, "Left",
          Ctor(variant_option_bool, "Some", PBool(false))
        );
        Ctor(
          variant_left_right, "Left",
          Ctor(variant_option_bool, "None", PNil)
        );
        Ctor(
          variant_left_right, "Right",
          Ctor(variant_option_bool, "Some", PBool(true))
        );
        Ctor(
          variant_left_right, "Right",
          Ctor(variant_option_bool, "Some", PBool(false))
        );
        Ctor(
          variant_left_right, "Right",
          Ctor(variant_option_bool, "None", PNil)
        );
      ]
      variant_left_right
  ));
]

let pattern_completeness = let open Alcotest in [
  (test_case "bool_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [Wild(Bool)]
      (generate_value_patts Bool)
  ));
  (test_case "bool_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [VarBind(Bool, "x")]
      (generate_value_patts Bool)
  ));
  (test_case "bool_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [PBool(true); PBool(false)]
      (generate_value_patts Bool)
  ));
  (test_case "bool_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [PBool(false); PBool(true)]
      (generate_value_patts Bool)
  ));
  (test_case "partial_bool_vals" `Quick (
    test_determine_pattern_completeness
      ([], [PBool(false)])
      [PBool(true)]
      (generate_value_patts Bool)
  ));
  (test_case "incomplete_bool_vals" `Quick (
    test_determine_pattern_completeness
      ([], [PBool(true)])
      [PBool(false)]
      (generate_value_patts Bool)
  ));
  (test_case "incomplete_bool_vals" `Quick (
    test_determine_pattern_completeness
      ([], [PBool(true); PBool(false)])
      []
      (generate_value_patts Bool)
  ));
  (test_case "useless_bool_patts" `Quick (
    test_determine_pattern_completeness
      ([PBool(false); PBool(true)], [])
      [PBool(true); PBool(false); PBool(false); PBool(true)]
      (generate_value_patts Bool)
  ));
  (test_case "option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [Wild(variant_option_bool)]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [
        Ctor(variant_option_bool, "Some", Wild(Bool));
        Wild(variant_option_bool);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [
        Ctor(variant_option_bool, "Some", Wild(Bool));
        Ctor(variant_option_bool, "None", PNil);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [
        Ctor(variant_option_bool, "Some", PBool(true));
        Ctor(variant_option_bool, "Some", PBool(false));
        Ctor(variant_option_bool, "None", PNil);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "incomplete_option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [Ctor(variant_option_bool, "Some", PBool(false))])
      [
        Ctor(variant_option_bool, "Some", PBool(true));
        Ctor(variant_option_bool, "None", PNil);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "incomplete_option_vals" `Quick (
    test_determine_pattern_completeness
      (
        [],
        [
          Ctor(variant_option_bool, "Some", PBool(true));
          Ctor(variant_option_bool, "Some", PBool(false));
        ]
      )
      [
        Ctor(variant_option_bool, "None", Wild(Nil));
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "incomplete_option_vals" `Quick (
    test_determine_pattern_completeness
      (
        [],
        [
          Ctor(variant_option_bool, "Some", PBool(true));
          Ctor(variant_option_bool, "Some", PBool(false));
          Ctor(variant_option_bool, "None", PNil);
        ]
      )
      []
      (generate_value_patts variant_option_bool)
  ));
  (test_case "useless_option_vals" `Quick (
    test_determine_pattern_completeness
      ([Ctor(variant_option_bool, "Some", PBool(false))], [])
      [
        Ctor(variant_option_bool, "Some", Wild(Bool));
        Ctor(variant_option_bool, "Some", PBool(false));
        Ctor(variant_option_bool, "None", PNil);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "useless_option_vals" `Quick (
    test_determine_pattern_completeness
      ([Wild(variant_option_bool)], [])
      [
        Ctor(variant_option_bool, "Some", Wild(Bool));
        Ctor(variant_option_bool, "None", PNil);
        Wild(variant_option_bool);
      ]
      (generate_value_patts variant_option_bool)
  ));
]

let () =
  let open Alcotest in
  run "Pattern" [
    ("pattern_dominates", pattern_domination);
    ("generate_value_patts", value_patts);
    ("pattern_completeness", pattern_completeness);
  ]
