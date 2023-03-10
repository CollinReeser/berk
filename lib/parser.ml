open Ast
open Ir
open Lexer
open Typing


exception Backtrack


let rec parse_tokens tokens : module_decl list =
  let rec _parse_tokens tokens mod_decls_so_far =
    begin match tokens with
    | [] -> mod_decls_so_far

    | KWExtern(_) :: rest ->
        let (rest, mod_decl) = parse_extern rest in
        _parse_tokens rest (mod_decl :: mod_decls_so_far)

    | KWFn(_) :: rest ->
        let (rest, func_def) = parse_func rest in
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


and parse_extern tokens : (token list * module_decl) =
  begin match tokens with
  | KWFn(_) :: rest ->
      let (rest, f_decl) = parse_func_decl rest in
      (rest, FuncExternDecl(f_decl))

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected `fn`." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing `extern` declaration."
  end


and parse_func_decl tokens : (token list * func_decl_t) =
  begin match tokens with
  | LowIdent(_, f_name) :: LParen(_) :: rest ->
      let (rest, f_params) = parse_func_params rest in

      begin match rest with
      | Colon(_) :: rest ->
          let (rest, f_ret_t) = parse_type rest in
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


and parse_func_params tokens : (token list * f_param list) =
  let rec _parse_func_params tokens params_so_far =
    begin match tokens with
    | RParen(_) :: rest ->
        (rest, params_so_far)

    | LowIdent(_, p_name) :: Colon(_) :: rest ->
        let (rest, qual, t) = parse_qualed_type rest in

        let param = (p_name, qual, t) in
        let params_so_far = params_so_far @ [param] in

        begin match rest with
        | Comma(_) :: rest -> _parse_func_params rest params_so_far
        | _ -> _parse_func_params rest params_so_far
        end

    | TriEllipses(_) :: rest ->
        let param = ("vargs", {mut=false}, VarArgSentinel) in
        let params_so_far = params_so_far @ [param] in

        _parse_func_params rest params_so_far

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s], expected lc-identifer" fmted
        )
    | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
    end
  in

  _parse_func_params tokens []


and parse_qualed_type tokens : (token list * var_qual * berk_t) =
  begin match tokens with
  | KWMut(_) :: rest ->
      let (rest, t) = parse_type rest in
      (rest, {mut=true}, t)

  | _ ->
      let (rest, t) = parse_type tokens in
      (rest, {mut=false}, t)
  end


and parse_type tokens : (token list * berk_t) =
  begin match tokens with
  | KWi8(_)  :: rest -> (rest, I8)
  | KWi16(_) :: rest -> (rest, I16)
  | KWi32(_) :: rest -> (rest, I32)
  | KWi64(_) :: rest -> (rest, I64)
  | KWu8(_)  :: rest -> (rest, U8)
  | KWu16(_) :: rest -> (rest, U16)
  | KWu32(_) :: rest -> (rest, U32)
  | KWu64(_) :: rest -> (rest, U64)
  | KWString(_) :: rest -> (rest, String)
  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected lc-identifer." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing type."
  end


and parse_func tokens : (token list * func_def_t) =
  let (rest, f_decl) = parse_func_decl tokens in
  let (rest, f_stmts) = parse_stmt_block rest in

  (
    rest, {
      f_decl=f_decl;
      f_stmts=f_stmts;
    }
  )


and parse_stmt_block tokens : (token list * stmt list) =
  begin match tokens with
  | LBrace(_) :: rest ->
      let (rest, stmts) = parse_stmts rest in

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


and parse_expr_block tokens : (token list * expr) =
  begin match tokens with
  | LBrace(_) :: rest ->
      let (rest, stmts) = parse_stmts rest in
      let (rest, exp) = begin
        try parse_expr rest
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


and parse_stmts tokens : (token list * stmt list) =
  let rec _parse_stmts tokens stmts_so_far =
    begin match (parse_stmt tokens) with
    | Some((rest, stmt)) -> _parse_stmts rest (stmts_so_far @ [stmt])
    | None -> (tokens, stmts_so_far)
    end
  in

  _parse_stmts tokens []


and parse_stmt tokens : (token list * stmt) option =
  try
    let (rest, stmt) =
      begin match tokens with
      | KWLet(_) :: rest -> parse_decl_stmt rest

      | KWReturn(_) :: rest ->
          let (rest, exp) = parse_expr rest in
          (rest, ReturnStmt(exp))

      | _ ->
          try parse_assign_stmt tokens
          with Backtrack ->
          parse_expr_stmt tokens
      end
    in

    begin match (stmt, rest) with
    (* For certain block-based expression-statements, the trailing semicolon
    is optional. *)
    | (
        (
          ExprStmt(BlockExpr(_, _, _))
        | ExprStmt(IfThenElseExpr(_, _, _, _))
        | ExprStmt(WhileExpr(_, _, _))
        | ExprStmt(MatchExpr(_, _, _))
        ),
        (
          (Semicolon(_) :: rest)
        | rest
        )
      ) ->
        Some(rest, stmt)

    | (_, Semicolon(_) :: rest) -> Some(rest, stmt)

    | (_, tok :: _) ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] (stmt), expected `;`" fmted
        )
    | (_, []) -> failwith "Unexpected EOF while parsing stmt."
    end

  with Backtrack ->
    None


and parse_decl_stmt tokens : (token list * stmt) =
  begin match tokens with
  | LowIdent(_, name) :: ColonEqual(_) :: rest ->
      let (rest, exp) = parse_expr rest in
      (rest, DeclStmt(name, {mut=false}, Undecided, exp))

  | LowIdent(_, name) :: Colon(_) :: rest ->
      let (rest, qual, t) = parse_qualed_type rest in
      let (rest, exp) = parse_expr rest in
      (rest, DeclStmt(name, qual, t, exp))

  (* TODO: Extend to recognize DeclDeconStmt *)

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s] (decl_stmt), expected identifier." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing let declaration."
  end


and parse_assign_stmt tokens : (token list * stmt) =
  begin match tokens with
  | LowIdent(_, name) :: Equal(_) :: rest ->
      let (rest, exp) = parse_expr rest in
      (rest, AssignStmt(name, exp))

  (* TODO: Extend to recognize AssignDeconStmt *)

  | _ -> raise Backtrack
  end


and parse_expr_stmt tokens : (token list * stmt) =
  let (rest, exp) = parse_expr tokens in
  (rest, ExprStmt(exp))


and parse_expr tokens : (token list * expr) =
  let (rest, exp) = parse_sum tokens in
  (rest, exp)


and parse_sum tokens : (token list * expr) =
  let rec _parse_sum tokens exp_lhs =
    begin match tokens with
    | Plus(_) :: rest ->
        let (rest, exp_rhs) = parse_prod rest in
        let exp = BinOp(Undecided, Add, exp_lhs, exp_rhs) in
        _parse_sum rest exp

    | Minus(_) :: rest ->
        let (rest, exp_rhs) = parse_prod rest in
        let exp = BinOp(Undecided, Sub, exp_lhs, exp_rhs) in
        _parse_sum rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_prod tokens in
  _parse_sum rest exp_lhs


and parse_prod tokens : (token list * expr) =
  let rec _parse_prod tokens exp_lhs =
    begin match tokens with
    | Star(_) :: rest ->
        let (rest, exp_rhs) = parse_equality rest in
        let exp = BinOp(Undecided, Mul, exp_lhs, exp_rhs) in
        _parse_prod rest exp

    | Slash(_) :: rest ->
        let (rest, exp_rhs) = parse_equality rest in
        let exp = BinOp(Undecided, Div, exp_lhs, exp_rhs) in
        _parse_prod rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_equality tokens in
  _parse_prod rest exp_lhs


and parse_equality tokens : (token list * expr) =
  let rec _parse_equality tokens exp_lhs =
    begin match tokens with
    | EqualEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_value rest in
        let exp = BinOp(Undecided, Eq, exp_lhs, exp_rhs) in
        _parse_equality rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_value tokens in
  _parse_equality rest exp_lhs


and parse_value tokens : (token list * expr) =
  begin
    try parse_if_expr tokens
    with Backtrack ->
    try parse_expr_block tokens
    with Backtrack ->
    try parse_func_call tokens
    with Backtrack ->
    parse_expr_atom tokens
  end


and parse_func_call tokens : (token list * expr) =
  begin match tokens with
  | LowIdent(_, f_name) :: LParen(_) :: RParen(_) :: rest ->
      (rest, FuncCall(Undecided, f_name, []))

  | LowIdent(_, f_name) :: LParen(_) :: rest ->
      let (rest, exps) = parse_func_call_args rest in
      (rest, FuncCall(Undecided, f_name, exps))

  | _ -> raise Backtrack
  end


and parse_func_call_args tokens : (token list * expr list) =
  let rec _parse_func_call_args tokens exps_so_far : (token list * expr list) =
    let (rest, exp) = parse_expr tokens in
    let exps_so_far = exps_so_far @ [exp] in

    begin match rest with
    | RParen(_) :: rest -> (rest, exps_so_far)
    | Comma(_) :: rest -> _parse_func_call_args rest exps_so_far

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] (args), expected among `,`|`)`." fmted
        )
    | [] -> failwith "Unexpected EOF while parsing func call arg list."
    end
  in

  _parse_func_call_args tokens []


and parse_if_expr tokens : (token list * expr) =
  begin match tokens with
  | KWIf(_) :: LParen(_) :: rest ->
      let (rest, cond_exp) = parse_expr rest in

      begin match rest with
      | RParen(_) :: rest ->
          let (rest, then_exp) = parse_expr_block rest in

          begin match rest with
          | KWElse(_) :: rest ->
              let (rest, else_exp) = parse_expr_block rest in
              (rest, IfThenElseExpr(Undecided, cond_exp, then_exp, else_exp))

          | _ :: _ ->
              (rest, IfThenElseExpr(Undecided, cond_exp, then_exp, ValNil))

          | [] -> failwith "Unexpected EOF while parsing if-expr."
          end

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] in if-expr, expected `)`." fmted
          )
      | [] -> failwith "Unexpected EOF while parsing func call arg list."
      end

  | _ ->
      raise Backtrack
  end


and parse_expr_atom tokens : (token list * expr) =
  begin match tokens with
  | Integer(_, num) :: rest -> (rest, ValInt(Undecided, num))
  | String(_, str) :: rest -> (rest, ValStr(str))
  | LowIdent(_, name) :: rest -> (rest, ValVar(Undecided, name))

  | _ -> raise Backtrack
  end
