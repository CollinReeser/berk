open Ast
open Ir
open Lexer
open Typing


exception Backtrack


let rec parse_tokens ?(trace=false) tokens : module_decl list =
  let _ = begin
    if trace then
      begin
        Printf.printf "Parsing: [%s] with [%s]\n"
          __FUNCTION__ (fmt_next_token tokens) ;
        ()
      end
    else ()
  end in

  let rec _parse_tokens tokens mod_decls_so_far =
    begin match tokens with
    | [] -> mod_decls_so_far

    | KWExtern(_) :: rest ->
        let (rest, mod_decl) = parse_extern ~ind:" " rest in
        _parse_tokens rest (mod_decl :: mod_decls_so_far)

    | KWFn(_) :: rest ->
        let (rest, func_def) = parse_func ~ind:" " rest in
        let mod_decl = FuncDef(func_def) in
        _parse_tokens rest (mod_decl :: mod_decls_so_far)

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s], expected among `extern`|`fn`" fmted
        )
    end
  in

  _parse_tokens tokens []


and parse_extern ?(ind="") tokens : (token list * module_decl) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | KWFn(_) :: rest ->
      let (rest, f_decl) = parse_func_decl ~ind:ind_next rest in
      (rest, FuncExternDecl(f_decl))

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected `fn`." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing `extern` declaration."
  end


and parse_func_decl ?(ind="") tokens : (token list * func_decl_t) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LowIdent(_, f_name) :: LParen(_) :: rest ->
      let (rest, f_params) = parse_func_params ~ind:ind_next rest in

      begin match rest with
      | Colon(_) :: rest ->
          let (rest, f_ret_t) = parse_type ~ind:ind_next rest in
          (
            rest, {
              f_name=f_name;
              f_params=f_params;
              f_ret_t=f_ret_t;
            }
          )

      | _ ->
          (
            rest, {
              f_name=f_name; f_params=f_params; f_ret_t=Nil
            }
          )
      end

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected lc-identifer" fmted
      )
  | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
  end


and parse_func_params ?(ind="") tokens : (token list * f_param list) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let parse_func_param ?(ind="") tokens params_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    let (rest, qual) = parse_var_qual ~ind:ind_next tokens in

    begin match rest with
    | LowIdent(_, p_name) :: Colon(_) :: rest ->
        let (rest, t) = parse_type ~ind:ind_next rest in
        let param = (p_name, qual, t) in
        let params_so_far = params_so_far @ [param] in

        (rest, params_so_far)

    | TriEllipses(_) :: rest ->
        let param = ("vargs", qual, VarArgSentinel) in
        let params_so_far = params_so_far @ [param] in

        (rest, params_so_far)

    | _ :: _ -> (rest, params_so_far)

    | [] -> failwith "Unexpected EOF while parsing `fn` param declaration."
    end
  in

  let rec _parse_func_params ?(ind="") tokens params_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    let (rest, params_so_far) =
      parse_func_param ~ind:ind_next tokens params_so_far
    in

    begin match rest with
    | RParen(_) :: rest ->
        (rest, params_so_far)

    | Comma(_) :: rest ->
        _parse_func_params ~ind:ind_next rest params_so_far

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s], expected lc-identifer" fmted
        )
    | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
    end
  in

  _parse_func_params ~ind:ind_next tokens []


and parse_type ?(ind="") tokens : (token list * berk_t) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let (rest, t) = begin match tokens with
  | KWi8(_)  :: rest -> (rest, I8)
  | KWi16(_) :: rest -> (rest, I16)
  | KWi32(_) :: rest -> (rest, I32)
  | KWi64(_) :: rest -> (rest, I64)
  | KWu8(_)  :: rest -> (rest, U8)
  | KWu16(_) :: rest -> (rest, U16)
  | KWu32(_) :: rest -> (rest, U32)
  | KWu64(_) :: rest -> (rest, U64)
  | KWBool(_) :: rest -> (rest, Bool)
  | KWString(_) :: rest -> (rest, String)

  (* Static array. *)
  | LBracket(_) :: Integer(_, i) :: RBracket(_) :: rest ->
      let (rest, arr_t) = parse_type ~ind:ind_next rest in
      (rest, Array(arr_t, i))

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected lc-identifer." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing type."
  end
  in

  (rest, t)


and parse_func ?(ind="") tokens : (token list * func_def_t) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let (rest, f_decl) = parse_func_decl ~ind:ind_next tokens in
  let (rest, f_stmts) = parse_stmt_block ~ind:ind_next rest in

  (
    rest, {
      f_decl=f_decl;
      f_stmts=f_stmts;
    }
  )


and parse_stmt_block ?(ind="") tokens : (token list * stmt list) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LBrace(_) :: rest ->
      let (rest, stmts) = parse_stmts ~ind:ind_next rest in

      begin match rest with
      | RBrace(_) :: rest -> (rest, stmts)

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s], expected `}`" fmted
          )
      | [] -> failwith "Unexpected EOF while searching for closing `}`."
      end

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected `{`" fmted
      )
  | [] -> failwith "Unexpected EOF while parsing block."
  end


and parse_expr_block ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LBrace(_) :: rest ->
      let (rest, stmts) = parse_stmts ~ind:ind_next rest in
      let (rest, exp) = begin
        try parse_expr ~ind:ind_next rest
        with Backtrack ->
        (rest, ValNil)
      end in

      begin match rest with
      | RBrace(_) :: rest -> (rest, BlockExpr(Undecided, stmts, exp))

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] in expr block, expected `}`" fmted
          )
      | [] -> failwith "Unexpected EOF while searching for closing `}`."
      end

  | _ -> raise Backtrack
  end


and parse_stmts ?(ind="") tokens : (token list * stmt list) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let rec _parse_stmts ?(ind="") tokens stmts_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match (parse_stmt ~ind:ind_next tokens) with
    | Some((rest, stmt)) ->
        _parse_stmts ~ind:ind_next rest (stmts_so_far @ [stmt])

    | None ->
        (tokens, stmts_so_far)
    end
  in

  _parse_stmts ~ind:ind_next tokens []


and parse_stmt ?(ind="") tokens : (token list * stmt) option =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  try
    let (rest, stmt) =
      begin match tokens with
      | KWLet(_) :: rest -> parse_decl_stmt ~ind:ind_next rest

      (* A return with no expression is a void return. *)
      | KWReturn(_) :: ((Semicolon(_) :: _) as rest) ->
          (rest, ReturnStmt(ValNil))

      | KWReturn(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, ReturnStmt(exp))

      | _ ->
          try parse_assign_stmt ~ind:ind_next tokens
          with Backtrack ->
          parse_expr_stmt ~ind:ind_next tokens
      end
    in

    begin match (stmt, rest) with
    (* For certain block-based expression-statements, the trailing semicolon
    is optional. *)
    | (
        (
          ExprStmt(BlockExpr(_, _, _))
        | ExprStmt(IfThenElseExpr(_, _, _, _))
        | ExprStmt(WhileExpr(_, _, _, _))
        | ExprStmt(MatchExpr(_, _, _))
        ),
        (
          (Semicolon(_) :: rest)
        | rest
        )
      ) ->
        Some(rest, stmt)

    | (_, Semicolon(_) :: rest) -> Some(rest, stmt)

    | (_, _ :: _) -> None

    | (_, []) -> failwith "Unexpected EOF while parsing stmt."
    end

  with Backtrack ->
    None


and parse_var_qual ?(ind="") tokens : (token list * var_qual) =
  let _ = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | KWMut(_) :: rest -> (rest, {mut=true})

  | (_ :: _) as rest -> (rest, {mut=false})

  | [] -> failwith "Unexpected EOF while parsing let declaration."
  end


and parse_decl_stmt ?(ind="") tokens : (token list * stmt) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let (rest, qual) = parse_var_qual ~ind:ind_next tokens in

  begin match rest with
  | LowIdent(_, name) :: Equal(_) :: rest ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in
      (rest, DeclStmt(name, qual, Undecided, exp))

  | LowIdent(_, name) :: Colon(_) :: rest ->
      let (rest, t) = parse_type ~ind:ind_next rest in

      begin match rest with
      | Equal(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, DeclStmt(name, qual, t, exp))

      (* Lookahead to the semicolon, if there is one. If so, this is a
      "default declaration": `let var: bool; *)
      | (Semicolon(_) :: _) as rest ->
          (rest, DeclDefStmt([(name, qual, t)]))

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] (decl_stmt), expected `=` or `;`" fmted
          )
      | [] -> failwith "Unexpected EOF while parsing let declaration."
      end

  (* TODO: Extend to recognize DeclDeconStmt *)
  (* TODO: Extend to recognize DeclDefStmt with multiple fields. *)

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s] (decl_stmt), expected identifier." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing let declaration."
  end


and parse_assign_stmt ?(ind="") tokens : (token list * stmt) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  (* var = ... *)
  | LowIdent(_, name) :: Equal(_) :: rest ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in
      (rest, AssignStmt(ALVar(name), exp))

  (* tuple_var.1 = ... *)
  | LowIdent(_, name) :: Dot(_) :: Integer(_, i) :: Equal(_) :: rest
    ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in
      (rest, AssignStmt(ALStaticIndex(name, i), exp))

  (* array_var[i + 2] = ... *)
  | LowIdent(_, name) :: LBracket(_) :: rest ->
      let (rest, indexing_exp) = parse_expr ~ind:ind_next rest in

      begin match rest with
      | RBracket(_) :: Equal(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, AssignStmt(ALIndex(name, indexing_exp), exp))

      | _ -> failwith "Could not complete parse of indexing assignment."
      end

  (* TODO: Extend to recognize AssignDeconStmt *)

  | _ -> raise Backtrack
  end


and parse_expr_stmt ?(ind="") tokens : (token list * stmt) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let (rest, exp) = parse_expr ~ind:ind_next tokens in
  (rest, ExprStmt(exp))


and parse_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let (rest, exp) = parse_equality ~ind:ind_next tokens in
  (rest, exp)


and parse_equality ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let rec _parse_equality ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | EqualEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_relation ~ind:ind_next rest in
        let exp = BinOp(Undecided, Eq, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | BangEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_relation ~ind:ind_next rest in
        let exp = BinOp(Undecided, Ne, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_relation ~ind:ind_next tokens in
  _parse_equality ~ind:ind_next rest exp_lhs


and parse_relation ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let rec _parse_relation ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Lesser(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Lt, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | LessEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Le, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | Greater(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Gt, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | GreatEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Ge, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_sum ~ind:ind_next tokens in
  _parse_relation ~ind:ind_next rest exp_lhs


and parse_sum ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let rec _parse_sum ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Plus(_) :: rest ->
        let (rest, exp_rhs) = parse_prod ~ind:ind_next rest in
        let exp = BinOp(Undecided, Add, exp_lhs, exp_rhs) in
        _parse_sum ~ind:ind_next rest exp

    | Minus(_) :: rest ->
        let (rest, exp_rhs) = parse_prod ~ind:ind_next rest in
        let exp = BinOp(Undecided, Sub, exp_lhs, exp_rhs) in
        _parse_sum ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_prod ~ind:ind_next tokens in
  _parse_sum ~ind:ind_next rest exp_lhs


and parse_prod ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let rec _parse_prod ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Star(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Mul, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | Slash(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Div, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | Percent(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Mod, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_value ~ind:ind_next tokens in
  _parse_prod ~ind:ind_next rest exp_lhs


and parse_value ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let (rest, exp) = begin
    try parse_tuple_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_paren_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_if_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_while_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_expr_block ~ind:ind_next tokens
    with Backtrack ->
    try parse_func_call ~ind:ind_next tokens
    with Backtrack ->
    (* try *)
    parse_expr_atom ~ind:ind_next tokens
    (* with Backtrack *)
  end in

  (* There are various things that may then be done _to_ a just-evaluated
  expression, like indexing into arrays/aggregates, invoking functions pointers,
  etc, which can be arbitrarily chained. *)
  let rec _parse_value ?(ind="") rest exp_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token rest) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin
      try
        let (rest, exp_chain) =
          parse_array_index ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
      try
        let (rest, exp_chain) =
          parse_tuple_index ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
      try
        let (rest, exp_chain) =
          parse_func_var_call ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
        (rest, exp_so_far)
    end
  in

  _parse_value ~ind:ind_next rest exp


and parse_func_call ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LowIdent(_, f_name) :: LParen(_) :: RParen(_) :: rest ->
      (rest, FuncCall(Undecided, f_name, []))

  | LowIdent(_, f_name) :: LParen(_) :: rest ->
      let (rest, exps) = parse_func_call_args ~ind:ind_next rest in
      (rest, FuncCall(Undecided, f_name, exps))

  | _ -> raise Backtrack
  end


and parse_func_call_args ?(ind="") tokens : (token list * expr list) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  let rec _parse_func_call_args ?(ind="") tokens exps_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    let (rest, exp) = parse_expr ~ind:ind_next tokens in
    let exps_so_far = exps_so_far @ [exp] in

    begin match rest with
    | RParen(_) :: rest ->
        (rest, exps_so_far)

    | Comma(_) :: rest ->
        _parse_func_call_args ~ind:ind_next rest exps_so_far

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] (args), expected among `,`|`)`." fmted
        )
    | [] -> failwith "Unexpected EOF while parsing func call arg list."
    end
  in

  _parse_func_call_args ~ind:ind_next tokens []


and parse_func_var_call ?(ind="") tokens exp : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | Dot(_) :: LParen(_) :: RParen(_) :: rest ->
      (rest, ExprInvoke(Undecided, exp, []))

  | Dot(_) :: LParen(_) :: rest ->
      let (rest, args) = parse_func_call_args ~ind:ind_next rest in
      (rest, ExprInvoke(Undecided, exp, args))

  | _ -> raise Backtrack
  end


and parse_array_index ?(ind="") tokens exp : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LBracket(_) :: rest ->
      let (rest, idx_expr) = parse_expr ~ind:ind_next rest in

      begin match rest with
      | RBracket(_) :: rest ->
          (rest, IndexExpr(Undecided, idx_expr, exp))

      | _ -> raise Backtrack
      end

  | _ -> raise Backtrack
  end


and parse_tuple_index ?(ind="") tokens exp : (token list * expr) =
  let _ = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | Dot(_) :: Integer(_, i) :: rest ->
      (rest, StaticIndexExpr(Undecided, i, exp))

  | _ -> raise Backtrack
  end


and parse_tuple_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LParen(_) :: rest ->
      let (rest, init_exp) = parse_expr ~ind:ind_next rest in

      (* There must be at least one comma, if this is a tuple. There may be more
      expressions in this tuple, all comma-delimited. As a special case, it's
      valid to spell a 1-tuple via `(<expr>,)`. *)
      begin match rest with
      (* Is this a 1-tuple? *)
      | Comma(_) :: RParen(_) :: rest ->
          (rest, TupleExpr(Undecided, [init_exp]))

      (* This is at least a 2-tuple. *)
      | Comma(_) :: rest ->
          let (rest, pair_exp) = parse_expr ~ind:ind_next rest in

          (* At this point, we want to match 0 or more `, <expr>` sequences,
          followed by a final closing paren. *)
          let rec _parse_remaining_tuple rest exprs_so_far =
            begin match rest with
            | Comma(_) :: rest ->
                let (rest, next_exp) = parse_expr ~ind:ind_next rest in
                _parse_remaining_tuple rest (exprs_so_far @ [next_exp])

            | RParen(_) :: rest -> (rest, exprs_so_far)

            | tok :: _ ->
                let fmted = fmt_token tok in
                failwith (
                  Printf.sprintf
                    "Unexpected token [%s] parsing tuple expr, expected `)`."
                    fmted
                )
            | [] -> failwith "Unexpected EOF while parsing tuple expr."
            end
          in

          let (rest, remaining_tuple_exprs) = _parse_remaining_tuple rest [] in

          (
            rest,
            TupleExpr(Undecided, [init_exp; pair_exp] @ remaining_tuple_exprs)
          )

      | _ -> raise Backtrack
      end

  | _ ->
      raise Backtrack
  end


and parse_paren_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LParen(_) :: rest ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in

      begin match rest with
      | RParen(_) :: rest -> (rest, exp)

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] parsing parenthesized expr, expected `)`."
              fmted
          )
      | [] -> failwith "Unexpected EOF while parsing parenthesized expr."
      end

  | _ ->
      raise Backtrack
  end


and parse_if_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | KWIf(_) :: rest ->
      let (rest, cond_exp) = parse_expr ~ind:ind_next rest in
      let (rest, then_exp) = parse_expr_block ~ind:ind_next rest in

      begin match rest with
      | KWElse(_) :: rest ->
          let (rest, else_exp) = parse_expr_block ~ind:ind_next rest in
          (rest, IfThenElseExpr(Undecided, cond_exp, then_exp, else_exp))

      | _ :: _ ->
          (rest, IfThenElseExpr(Undecided, cond_exp, then_exp, ValNil))

      | [] -> failwith "Unexpected EOF while parsing if-expr."
      end

  | _ ->
      raise Backtrack
  end


and parse_while_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | KWWhile(_) :: LBrace(_) :: rest ->
      (* `while { <stmts> } <cond-expr> { <stmts> }` *)
      let (rest, init_stmts) = parse_stmts ~ind:ind_next rest in

      begin match rest with
      | RBrace(_) :: rest ->
          let (rest, cond_exp) = parse_expr ~ind:ind_next rest in
          let (rest, loop_exp) = parse_stmt_block ~ind:ind_next rest in

          (rest, WhileExpr(Undecided, init_stmts, cond_exp, loop_exp))

      | _ ->
          failwith "Could not find matching `}` in while-expr init-stmts"
      end

  | KWWhile(_) :: rest ->
      (* `while <cond-expr> { <stmts> }` *)
      let (rest, cond_exp) = parse_expr ~ind:ind_next rest in
      let (rest, loop_exp) = parse_stmt_block ~ind:ind_next rest in

      (rest, WhileExpr(Undecided, [], cond_exp, loop_exp))

  | _ ->
      raise Backtrack
  end


and parse_expr_atom ?(ind="") tokens : (token list * expr) =
  let _ = begin
    if ind <> "" then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind __FUNCTION__ (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end in

  begin match tokens with
  | LParen(_) :: RParen(_) :: rest -> (rest, ValNil)
  | KWTrue(_) :: rest -> (rest, ValBool(true))
  | KWFalse(_) :: rest -> (rest, ValBool(false))
  | Integer(_, num) :: rest -> (rest, ValInt(Undecided, num))
  | String(_, str) :: rest -> (rest, ValStr(str))
  | LowIdent(_, name) :: rest -> (rest, ValName(Undecided, name))

  | _ -> raise Backtrack
  end
