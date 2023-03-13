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
  | LowIdent(_, name) :: ColonEqual(_) :: rest ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in
      (rest, DeclStmt(name, qual, Undecided, exp))

  | LowIdent(_, name) :: Colon(_) :: rest ->
      let (rest, t) = parse_type ~ind:ind_next rest in

      begin match rest with
      | Equal(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, DeclStmt(name, qual, t, exp))

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] (decl_stmt), expected `=`" fmted
          )
      | [] -> failwith "Unexpected EOF while parsing let declaration."
      end

  (* TODO: Extend to recognize DeclDeconStmt *)

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
  | LowIdent(_, name) :: Equal(_) :: rest ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in
      (rest, AssignStmt(name, exp))

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

  let (rest, exp) = parse_sum ~ind:ind_next tokens in
  (rest, exp)


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
        let (rest, exp_rhs) = parse_equality ~ind:ind_next rest in
        let exp = BinOp(Undecided, Mul, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | Slash(_) :: rest ->
        let (rest, exp_rhs) = parse_equality ~ind:ind_next rest in
        let exp = BinOp(Undecided, Div, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_equality ~ind:ind_next tokens in
  _parse_prod ~ind:ind_next rest exp_lhs


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
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Eq, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | BangEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Ne, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | Lesser(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Lt, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | LessEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Le, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | Greater(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Gt, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | GreatEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_value ~ind:ind_next rest in
        let exp = BinOp(Undecided, Ge, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_value ~ind:ind_next tokens in
  _parse_equality ~ind:ind_next rest exp_lhs


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

  begin
    try parse_if_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_while_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_expr_block ~ind:ind_next tokens
    with Backtrack ->
    try parse_func_call ~ind:ind_next tokens
    with Backtrack ->
    parse_expr_atom ~ind:ind_next tokens
  end


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
  | KWIf(_) :: LParen(_) :: rest ->
      let (rest, cond_exp) = parse_expr ~ind:ind_next rest in

      begin match rest with
      | RParen(_) :: rest ->
          let (rest, then_exp) = parse_expr_block ~ind:ind_next rest in

          begin match rest with
          | KWElse(_) :: rest ->
              let (rest, else_exp) = parse_expr_block ~ind:ind_next rest in
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
  | KWWhile(_) :: rest ->
      let (rest, cond_exp) = parse_expr ~ind:ind_next rest in

      let (rest, loop_exp) = parse_stmt_block ~ind:ind_next rest in

      (rest, WhileExpr(Undecided, cond_exp, loop_exp))

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
  | Integer(_, num) :: rest -> (rest, ValInt(Undecided, num))
  | String(_, str) :: rest -> (rest, ValStr(str))
  | LowIdent(_, name) :: rest -> (rest, ValVar(Undecided, name))

  | _ -> raise Backtrack
  end
