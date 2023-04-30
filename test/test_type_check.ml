open Berk.Ast
open Berk.Type_check
open Berk.Typing

let pattern_tst = Alcotest.testable pprint_pattern (=)

let test_pattern_dominates expect lhs rhs () =
  Alcotest.(check' (pair bool pass))
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

let variant_option_bool =
  Variant(
    "Option", [
      {name="Some"; fields=[{t=Bool}]};
      {name="None"; fields=[]}
    ]
  )
let variant_left_right =
  Variant(
    "LeftRight", [
      {name="Left"; fields=[{t=variant_option_bool}]};
      {name="Right"; fields=[{t=variant_option_bool}]}
    ]
  )

let tuple_t = Tuple([variant_option_bool; variant_left_right])

type lr = Left of bool option | Right of bool option

let gen_tuple_patt lhs rhs =
  let gen_opt b_opt =
    begin match b_opt with
    | None -> Ctor(variant_option_bool, "None", [])
    | Some(b) -> Ctor(variant_option_bool, "Some", [PBool(b)])
    end
  in
  let lhs = gen_opt lhs in
  let rhs = begin match rhs with
  | Left(b_opt) -> Ctor(variant_left_right, "Left", [gen_opt b_opt])
  | Right(b_opt) -> Ctor(variant_left_right, "Right", [gen_opt b_opt])
  end in

  [lhs; rhs]
;;

let pattern_domination = let open Alcotest in [
  (test_case "bool_sanity" `Quick (
    test_pattern_dominates (true, []) (PBool(true)) (PBool(true))));
  (test_case "bool_sanity" `Quick (
    test_pattern_dominates (true, []) (PBool(false)) (PBool(false))));
  (test_case "bool_rev" `Quick (
    test_pattern_dominates (false, []) (PBool(true)) (PBool(false))));
  (test_case "bool_rev" `Quick (
    test_pattern_dominates (false, []) (PBool(false)) (PBool(true))));
  (test_case "bool_wild" `Quick (
    test_pattern_dominates (true, []) (Wild(Undecided)) (PBool(false))));
  (test_case "bool_var" `Quick (
    test_pattern_dominates (true, []) (VarBind(Undecided, "x")) (PBool(false))));
  (test_case "ctor_wild" `Quick (
    test_pattern_dominates (true, []) (
      Wild(Undecided)
    ) (
      Ctor(variant_option_bool, "Some", [Wild(Undecided)])
    )
  ));
  (test_case "ctor_var" `Quick (
    test_pattern_dominates (true, []) (
      VarBind(Undecided, "x")
    ) (
      Ctor(variant_option_bool, "Some", [Wild(Undecided)])
    )
  ));
  (test_case "ctor_full_match" `Quick (
    test_pattern_dominates (true, []) (
      Ctor(variant_option_bool, "Some", [PBool(true)])
    ) (
      Ctor(variant_option_bool, "Some", [PBool(true)])
    )
  ));
  (test_case "ctor_full_non_match" `Quick (
    test_pattern_dominates (false, []) (
      Ctor(variant_option_bool, "Some", [PBool(true)])
    ) (
      Ctor(variant_option_bool, "Some", [PBool(false)])
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates (true, []) (
      Wild(variant_left_right)
    ) (
      Ctor(
        variant_left_right, "Left", [
          Ctor(variant_option_bool, "Some", [PBool(false)])
        ]
      )
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates (true, []) (
      Ctor(variant_left_right, "Left", [Wild(variant_option_bool)])
    ) (
      Ctor(
        variant_left_right, "Left", [
          Ctor(variant_option_bool, "Some", [PBool(false)])
        ]
      )
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates (true, []) (
      Ctor(
        variant_left_right, "Left", [
          Ctor(variant_option_bool, "Some", [Wild(Bool)])
        ]
      )
    ) (
      Ctor(
        variant_left_right, "Left", [
          Ctor(variant_option_bool, "Some", [PBool(false)])
        ]
      )
    )
  ));
  (test_case "nested_variant_superset" `Quick (
    test_pattern_dominates (false, []) (
      Ctor(variant_left_right, "Right", [Wild(variant_option_bool)])
    ) (
      Ctor(
        variant_left_right, "Left", [
          Ctor(variant_option_bool, "Some", [PBool(false)])
        ]
      )
    )
  ));
  (test_case "tuple_sanity" `Quick (
    test_pattern_dominates (true, []) (
      Wild(tuple_t)
    ) (
      PTuple(tuple_t, gen_tuple_patt None (Left(None)))
    )
  ));
  (test_case "tuple_sanity_match" `Quick (
    test_pattern_dominates (true, []) (
      PTuple(tuple_t, gen_tuple_patt None (Left(None)))
    ) (
      PTuple(tuple_t, gen_tuple_patt None (Left(None)))
    )
  ));
  (test_case "tuple_partial" `Quick (
    test_pattern_dominates (true, []) (
      PTuple(tuple_t, [
        Ctor(variant_option_bool, "None", []);
        Wild(variant_left_right)
      ])
    ) (
      PTuple(tuple_t, gen_tuple_patt None (Left(None)))
    )
  ));
  (test_case "tuple_partial" `Quick (
    test_pattern_dominates (true, []) (
      PTuple(tuple_t, [
        Wild(variant_option_bool);
        Ctor(variant_left_right, "Left", [Wild(variant_option_bool)])
      ])
    ) (
      PTuple(tuple_t, gen_tuple_patt None (Left(None)))
    )
  ));
  (test_case "tuple_nested_match_failure" `Quick (
    test_pattern_dominates (false, []) (
      PTuple(tuple_t, [
        Wild(variant_option_bool);
        Ctor(
          variant_left_right, "Left", [
            Ctor(variant_option_bool, "Some", [PBool(true)])
          ]
        )
      ])
    ) (
      PTuple(tuple_t, gen_tuple_patt None (Left(None)))
    )
  ));
  (test_case "tuple_nested_match_failure" `Quick (
    test_pattern_dominates (false, []) (
      PTuple(tuple_t, [
        Wild(variant_option_bool);
        Ctor(
          variant_left_right, "Left", [
            Ctor(variant_option_bool, "Some", [PBool(true)])
          ]
        )
      ])
    ) (
      PTuple(tuple_t, gen_tuple_patt None (Left(Some(false))))
    )
  ));
  (test_case "tuple_nested_match_sanity" `Quick (
    test_pattern_dominates (true, []) (
      PTuple(tuple_t, [
        Wild(variant_option_bool);
        Ctor(
          variant_left_right, "Left", [
            Ctor(variant_option_bool, "Some", [PBool(false)])
          ]
        )
      ])
    ) (
      PTuple(tuple_t, gen_tuple_patt None (Left(Some(false))))
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
        Ctor(variant_option_bool, "Some", [PBool(true)]);
        Ctor(variant_option_bool, "Some", [PBool(false)]);
        Ctor(variant_option_bool, "None", []);
      ]
      variant_option_bool
  ));
  (test_case "nested_variant_vals" `Quick (
    test_generate_value_patts
      [
        Ctor(
          variant_left_right, "Left", [
            Ctor(variant_option_bool, "Some", [PBool(true)])
          ]
        );
        Ctor(
          variant_left_right, "Left", [
            Ctor(variant_option_bool, "Some", [PBool(false)])
          ]
        );
        Ctor(
          variant_left_right, "Left", [
            Ctor(variant_option_bool, "None", [])
          ]
        );
        Ctor(
          variant_left_right, "Right", [
            Ctor(variant_option_bool, "Some", [PBool(true)])
          ]
        );
        Ctor(
          variant_left_right, "Right", [
            Ctor(variant_option_bool, "Some", [PBool(false)])
          ]
        );
        Ctor(
          variant_left_right, "Right", [
            Ctor(variant_option_bool, "None", [])
          ]
        );
      ]
      variant_left_right
  ));
  (test_case "tuple_of_variants" `Quick (
    test_generate_value_patts
      [
        PTuple(tuple_t, gen_tuple_patt None          (Left(Some(true))));
        PTuple(tuple_t, gen_tuple_patt None          (Left(Some(false))));
        PTuple(tuple_t, gen_tuple_patt None          (Left(None)));
        PTuple(tuple_t, gen_tuple_patt None          (Right(Some(true))));
        PTuple(tuple_t, gen_tuple_patt None          (Right(Some(false))));
        PTuple(tuple_t, gen_tuple_patt None          (Right(None)));
        PTuple(tuple_t, gen_tuple_patt (Some(false)) (Left(Some(true))));
        PTuple(tuple_t, gen_tuple_patt (Some(false)) (Left(Some(false))));
        PTuple(tuple_t, gen_tuple_patt (Some(false)) (Left(None)));
        PTuple(tuple_t, gen_tuple_patt (Some(false)) (Right(Some(true))));
        PTuple(tuple_t, gen_tuple_patt (Some(false)) (Right(Some(false))));
        PTuple(tuple_t, gen_tuple_patt (Some(false)) (Right(None)));
        PTuple(tuple_t, gen_tuple_patt (Some(true))  (Left(Some(true))));
        PTuple(tuple_t, gen_tuple_patt (Some(true))  (Left(Some(false))));
        PTuple(tuple_t, gen_tuple_patt (Some(true))  (Left(None)));
        PTuple(tuple_t, gen_tuple_patt (Some(true))  (Right(Some(true))));
        PTuple(tuple_t, gen_tuple_patt (Some(true))  (Right(Some(false))));
        PTuple(tuple_t, gen_tuple_patt (Some(true))  (Right(None)));
      ]
      tuple_t
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
        Ctor(variant_option_bool, "Some", [Wild(Bool)]);
        Wild(variant_option_bool);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [
        Ctor(variant_option_bool, "Some", [Wild(Bool)]);
        Ctor(variant_option_bool, "None", []);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [])
      [
        Ctor(variant_option_bool, "Some", [PBool(true)]);
        Ctor(variant_option_bool, "Some", [PBool(false)]);
        Ctor(variant_option_bool, "None", []);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "incomplete_option_vals" `Quick (
    test_determine_pattern_completeness
      ([], [Ctor(variant_option_bool, "Some", [PBool(false)])])
      [
        Ctor(variant_option_bool, "Some", [PBool(true)]);
        Ctor(variant_option_bool, "None", []);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "incomplete_option_vals" `Quick (
    test_determine_pattern_completeness
      (
        [],
        [
          Ctor(variant_option_bool, "Some", [PBool(true)]);
          Ctor(variant_option_bool, "Some", [PBool(false)]);
        ]
      )
      [
        Ctor(variant_option_bool, "None", []);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "incomplete_option_vals" `Quick (
    test_determine_pattern_completeness
      (
        [],
        [
          Ctor(variant_option_bool, "Some", [PBool(true)]);
          Ctor(variant_option_bool, "Some", [PBool(false)]);
          Ctor(variant_option_bool, "None", []);
        ]
      )
      []
      (generate_value_patts variant_option_bool)
  ));
  (test_case "useless_option_vals" `Quick (
    test_determine_pattern_completeness
      ([Ctor(variant_option_bool, "Some", [PBool(false)])], [])
      [
        Ctor(variant_option_bool, "Some", [Wild(Bool)]);
        Ctor(variant_option_bool, "Some", [PBool(false)]);
        Ctor(variant_option_bool, "None", []);
      ]
      (generate_value_patts variant_option_bool)
  ));
  (test_case "useless_option_vals" `Quick (
    test_determine_pattern_completeness
      ([Wild(variant_option_bool)], [])
      [
        Ctor(variant_option_bool, "Some", [Wild(Bool)]);
        Ctor(variant_option_bool, "None", []);
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
