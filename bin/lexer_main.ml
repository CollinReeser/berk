open Berk.Ast
open Berk.Ir
open Berk.Typing
open Berk.Type_check

type position = {
  beg: Lexing.position;
  fin: Lexing.position;
}

type token =
| KWExtern of position
| KWFn of position
| KWMut of position
| KWLet of position
| KWReturn of position
| KWi8 of position
| KWi16 of position
| KWi32 of position
| KWi64 of position
| KWu8 of position
| KWu16 of position
| KWu32 of position
| KWu64 of position
| KWString of position
| LParen of position
| RParen of position
| LBrace of position
| RBrace of position
| Comma of position
| ColonEqual of position
| Colon of position
| Equal of position
| Semicolon of position
| TriEllipses of position
| BiEllipses of position
| Plus of position
| Minus of position
| Star of position
| Slash of position
| LowIdent of position * string
| CapIdent of position * string
| Integer of position * int
| String of position * string


let get_pos buf =
  let (p_start, p_fin) = Sedlexing.lexing_positions buf in
  {beg=p_start; fin=p_fin}
;;


(* Start line/column-within-line of this position. *)
let lines_cols (pos : position) : (int * int * int * int) =
  let {
    beg={
      Lexing.pos_lnum=beg_pos_lnum;
      Lexing.pos_bol=beg_pos_bol;
      Lexing.pos_cnum=beg_pos_cnum;
      _
    };
    fin={
      Lexing.pos_lnum=fin_pos_lnum;
      Lexing.pos_bol=fin_pos_bol;
      Lexing.pos_cnum=fin_pos_cnum;
      _
    };
  } = pos in

  let beg_line = beg_pos_lnum in
  let beg_col = beg_pos_cnum - beg_pos_bol in

  let fin_line = fin_pos_lnum in
  let fin_col = fin_pos_cnum - fin_pos_bol in

  (beg_line, beg_col, fin_line, fin_col)
;;

let fmt_pos (pos : position) =
    let (beg_line, beg_col, fin_line, fin_col) = lines_cols pos in
    Printf.sprintf
      "[%d:%d ; %d:%d]"
      beg_line beg_col fin_line fin_col
;;


let fmt_token tok =
  match tok with
  | KWExtern(p)    -> Printf.sprintf "extern (kw)    : %s\n"   (fmt_pos p)
  | KWFn(p)        -> Printf.sprintf "fn     (kw)    : %s\n"   (fmt_pos p)
  | KWMut(p)       -> Printf.sprintf "mut    (kw)    : %s\n"   (fmt_pos p)
  | KWLet(p)       -> Printf.sprintf "let    (kw)    : %s\n"   (fmt_pos p)
  | KWReturn(p)    -> Printf.sprintf "return (kw)    : %s\n"   (fmt_pos p)
  | KWi8(p)        -> Printf.sprintf "i8     (kw)    : %s\n"   (fmt_pos p)
  | KWi16(p)       -> Printf.sprintf "i16    (kw)    : %s\n"   (fmt_pos p)
  | KWi32(p)       -> Printf.sprintf "i32    (kw)    : %s\n"   (fmt_pos p)
  | KWi64(p)       -> Printf.sprintf "i64    (kw)    : %s\n"   (fmt_pos p)
  | KWu8(p)        -> Printf.sprintf "u8     (kw)    : %s\n"   (fmt_pos p)
  | KWu16(p)       -> Printf.sprintf "u16    (kw)    : %s\n"   (fmt_pos p)
  | KWu32(p)       -> Printf.sprintf "u32    (kw)    : %s\n"   (fmt_pos p)
  | KWu64(p)       -> Printf.sprintf "u64    (kw)    : %s\n"   (fmt_pos p)
  | KWString(p)    -> Printf.sprintf "u64    (kw)    : %s\n"   (fmt_pos p)
  | LParen(p)      -> Printf.sprintf "(   (syn)      : %s\n"   (fmt_pos p)
  | RParen(p)      -> Printf.sprintf ")   (syn)      : %s\n"   (fmt_pos p)
  | LBrace(p)      -> Printf.sprintf "{   (syn)      : %s\n"   (fmt_pos p)
  | RBrace(p)      -> Printf.sprintf "}   (syn)      : %s\n"   (fmt_pos p)
  | Comma(p)       -> Printf.sprintf ",   (syn)      : %s\n"   (fmt_pos p)
  | ColonEqual(p)  -> Printf.sprintf ":=  (syn)      : %s\n"   (fmt_pos p)
  | Colon(p)       -> Printf.sprintf ":   (syn)      : %s\n"   (fmt_pos p)
  | Equal(p)       -> Printf.sprintf "=   (syn)      : %s\n"   (fmt_pos p)
  | Semicolon(p)   -> Printf.sprintf ";   (syn)      : %s\n"   (fmt_pos p)
  | TriEllipses(p) -> Printf.sprintf "... (syn)      : %s\n"   (fmt_pos p)
  | BiEllipses(p)  -> Printf.sprintf "..  (syn)      : %s\n"   (fmt_pos p)
  | Plus(p)        -> Printf.sprintf "+   (syn)      : %s\n"   (fmt_pos p)
  | Minus(p)       -> Printf.sprintf "-   (syn)      : %s\n"   (fmt_pos p)
  | Star(p)        -> Printf.sprintf "*   (syn)      : %s\n"   (fmt_pos p)
  | Slash(p)       -> Printf.sprintf "/   (syn)      : %s\n"   (fmt_pos p)
  | LowIdent(p, s) -> Printf.sprintf "%s (low-ident) : %s\n" s (fmt_pos p)
  | CapIdent(p, s) -> Printf.sprintf "%s (cap-ident) : %s\n" s (fmt_pos p)
  | Integer(p, i)  -> Printf.sprintf "%d (integer)   : %s\n" i (fmt_pos p)
  | String(p, s)   -> Printf.sprintf "%s (string)    : %s\n" s (fmt_pos p)
;;


let print_tokens tokens =
  let fmted = List.map fmt_token tokens in
  List.iter (Printf.printf "%s") fmted
;;


let tokenize buf =
  let digit = [%sedlex.regexp? '0' .. '9'] in
  let number = [%sedlex.regexp? Plus digit] in

  let str_simple_inner =
    [%sedlex.regexp?
      Star(Compl('"' | '\\'))
    ] in

  let str_escape_inner =
    [%sedlex.regexp?
      Star('\\', any, Star(str_simple_inner))
    ] in

  (* Encode this regex:
      "[^"\\]*(?:\\.[^"\\]*)*"
  *)
  let str_reg =
    [%sedlex.regexp?
      '"', str_simple_inner, str_escape_inner, '"'
    ]
  in

  let rec _tokenize buf tokens =
    begin match%sedlex buf with

    (* Keywords *)

    | "extern" ->
        let tok = KWExtern(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "fn" ->
        let tok = KWFn(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "mut" ->
        let tok = KWMut(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "let" ->
        let tok = KWLet(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "return" ->
        let tok = KWReturn(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "i8" ->
        let tok = KWi8(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "i16" ->
        let tok = KWi16(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "i32" ->
        let tok = KWi32(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "i64" ->
        let tok = KWi64(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "u8" ->
        let tok = KWu8(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "u16" ->
        let tok = KWu16(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "u32" ->
        let tok = KWu32(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "u64" ->
        let tok = KWu64(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "string" ->
        let tok = KWString(get_pos buf) in
        _tokenize buf (tok :: tokens)

    (* Syntax *)

    | "(" ->
        let tok = LParen(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ")" ->
        let tok = RParen(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "{" ->
        let tok = LBrace(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "}" ->
        let tok = RBrace(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "," ->
        let tok = Comma(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ":=" ->
        let tok = ColonEqual(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ":" ->
        let tok = Colon(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "=" ->
        let tok = Equal(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ";" ->
        let tok = Semicolon(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "..." ->
        let tok = TriEllipses(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ".." ->
        let tok = BiEllipses(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "+" ->
        let tok = Plus(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "-" ->
        let tok = Minus(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "*" ->
        let tok = Star(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "/" ->
        let tok = Slash(get_pos buf) in
        _tokenize buf (tok :: tokens)

    | 'A' .. 'Z', Star(id_continue) ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        let tok = CapIdent(get_pos buf, lexeme) in
        _tokenize buf (tok :: tokens)

    | ('_' | 'a' .. 'z'), Star(id_continue) ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        let tok = LowIdent(get_pos buf, lexeme) in
        _tokenize buf (tok :: tokens)

    | number ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        let i = int_of_string lexeme in
        let tok = Integer(get_pos buf, i) in
        _tokenize buf (tok :: tokens)

    | str_reg ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        let tok = String(get_pos buf, lexeme) in
        _tokenize buf (tok :: tokens)

    | Plus xml_blank ->
        _tokenize buf tokens

    | eof ->
        tokens

    | 128 .. 255 ->
        let pos = get_pos buf in
        let (line, col, _, _) = lines_cols pos in

        Printf.printf "Non-ASCII: L:%d, C:%d\n" line col ;

        tokens

    | _ ->
        let pos = get_pos buf in
        let (line, col, _, _) = lines_cols pos in

        Printf.printf "Unexpected character: L:%d, C:%d\n" line col ;

        tokens
    end
  in

  let tokens = _tokenize buf [] in
  List.rev tokens
;;


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

    begin match rest with
    | Semicolon(_) :: rest -> Some(rest, stmt)

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] (stmt), expected `;`" fmted
        )
    | [] -> failwith "Unexpected EOF while parsing stmt."
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
        let exp = BinOp(Undecided, Add, exp_lhs, exp_rhs) in
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
        let (rest, exp_rhs) = parse_value rest in
        let exp = BinOp(Undecided, Mul, exp_lhs, exp_rhs) in
        _parse_prod rest exp

    | Slash(_) :: rest ->
        let (rest, exp_rhs) = parse_value rest in
        let exp = BinOp(Undecided, Div, exp_lhs, exp_rhs) in
        _parse_prod rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_value tokens in
  _parse_prod rest exp_lhs


and parse_value tokens : (token list * expr) =
  try parse_func_call tokens
  with Backtrack ->
  parse_expr_atom tokens


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
    | _ -> _parse_func_call_args rest exps_so_far
    end
  in

  _parse_func_call_args tokens []


and parse_expr_atom tokens : (token list * expr) =
  begin match tokens with
  | Integer(_, num) :: rest -> (rest, ValInt(Undecided, num))
  | String(_, str) :: rest -> (rest, ValStr(str))
  | LowIdent(_, name) :: rest -> (rest, ValVar(Undecided, name))

  | _ -> raise Backtrack
  end


let () =
  let text = {|
    extern fn printf(fmt: string, ...): i32

    fn main(): i8 {
      let my_str := "Hello, world!\n";
      printf(my_str);

      return 0;
    }
  |} in
  let lexbuf = Sedlexing.Latin1.from_gen (Gen.of_string text) in
  let tokens = tokenize lexbuf in
  print_tokens tokens ;

  let mod_decls = parse_tokens tokens in

  (* Currently require declaration before use. *)
  let mod_decls = List.rev mod_decls in

  let mod_decls_tc = type_check_mod_decls mod_decls in
  let mod_decls_tc_rewritten =
    List.map (
      fun mod_decl ->
        match mod_decl with
        | FuncDef(func_def) ->
            let func_def_rewritten = rewrite_to_unique_varnames func_def in
            FuncDef(func_def_rewritten)

        | FuncExternDecl(_)
        | VariantDecl(_) -> mod_decl
    ) mod_decls_tc
  in

  let asts_fmted =
    List.map
      (fmt_mod_decl ~pretty_unbound:true ~print_typ:true)
      mod_decls_tc_rewritten
  in
  let _ = List.iter (Printf.printf "%s") asts_fmted in
  ()
;;

