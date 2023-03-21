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
| KWIf of position
| KWElse of position
| KWWhile of position
| KWi8 of position
| KWi16 of position
| KWi32 of position
| KWi64 of position
| KWu8 of position
| KWu16 of position
| KWu32 of position
| KWu64 of position
| KWBool of position
| KWTrue of position
| KWFalse of position
| KWString of position
| LParen of position
| RParen of position
| LBrace of position
| RBrace of position
| LBracket of position
| RBracket of position
| Dot of position
| Comma of position
| ColonEqual of position
| Colon of position
| EqualEqual of position
| BangEqual of position
| Equal of position
| LessEqual of position
| Lesser of position
| GreatEqual of position
| Greater of position
| Semicolon of position
| TriEllipses of position
| BiEllipses of position
| Plus of position
| Minus of position
| Star of position
| Slash of position
| Percent of position
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
  | KWExtern(p)    -> Printf.sprintf "extern (kw)    : %s"   (fmt_pos p)
  | KWFn(p)        -> Printf.sprintf "fn     (kw)    : %s"   (fmt_pos p)
  | KWMut(p)       -> Printf.sprintf "mut    (kw)    : %s"   (fmt_pos p)
  | KWLet(p)       -> Printf.sprintf "let    (kw)    : %s"   (fmt_pos p)
  | KWReturn(p)    -> Printf.sprintf "return (kw)    : %s"   (fmt_pos p)
  | KWIf(p)        -> Printf.sprintf "if     (kw)    : %s"   (fmt_pos p)
  | KWElse(p)      -> Printf.sprintf "else   (kw)    : %s"   (fmt_pos p)
  | KWWhile(p)     -> Printf.sprintf "while  (kw)    : %s"   (fmt_pos p)
  | KWi8(p)        -> Printf.sprintf "i8     (kw)    : %s"   (fmt_pos p)
  | KWi16(p)       -> Printf.sprintf "i16    (kw)    : %s"   (fmt_pos p)
  | KWi32(p)       -> Printf.sprintf "i32    (kw)    : %s"   (fmt_pos p)
  | KWi64(p)       -> Printf.sprintf "i64    (kw)    : %s"   (fmt_pos p)
  | KWu8(p)        -> Printf.sprintf "u8     (kw)    : %s"   (fmt_pos p)
  | KWu16(p)       -> Printf.sprintf "u16    (kw)    : %s"   (fmt_pos p)
  | KWu32(p)       -> Printf.sprintf "u32    (kw)    : %s"   (fmt_pos p)
  | KWu64(p)       -> Printf.sprintf "u64    (kw)    : %s"   (fmt_pos p)
  | KWBool(p)      -> Printf.sprintf "bool   (kw)    : %s"   (fmt_pos p)
  | KWTrue(p)      -> Printf.sprintf "true   (kw)    : %s"   (fmt_pos p)
  | KWFalse(p)     -> Printf.sprintf "false  (kw)    : %s"   (fmt_pos p)
  | KWString(p)    -> Printf.sprintf "u64    (kw)    : %s"   (fmt_pos p)
  | LParen(p)      -> Printf.sprintf "(   (syn)      : %s"   (fmt_pos p)
  | RParen(p)      -> Printf.sprintf ")   (syn)      : %s"   (fmt_pos p)
  | LBrace(p)      -> Printf.sprintf "{   (syn)      : %s"   (fmt_pos p)
  | RBrace(p)      -> Printf.sprintf "}   (syn)      : %s"   (fmt_pos p)
  | LBracket(p)    -> Printf.sprintf "[   (syn)      : %s"   (fmt_pos p)
  | RBracket(p)    -> Printf.sprintf "]   (syn)      : %s"   (fmt_pos p)
  | Dot(p)         -> Printf.sprintf ".   (syn)      : %s"   (fmt_pos p)
  | Comma(p)       -> Printf.sprintf ",   (syn)      : %s"   (fmt_pos p)
  | ColonEqual(p)  -> Printf.sprintf ":=  (syn)      : %s"   (fmt_pos p)
  | Colon(p)       -> Printf.sprintf ":   (syn)      : %s"   (fmt_pos p)
  | EqualEqual(p)  -> Printf.sprintf "==  (syn)      : %s"   (fmt_pos p)
  | BangEqual(p)   -> Printf.sprintf "!=  (syn)      : %s"   (fmt_pos p)
  | Equal(p)       -> Printf.sprintf "=   (syn)      : %s"   (fmt_pos p)
  | LessEqual(p)   -> Printf.sprintf "<=  (syn)      : %s"   (fmt_pos p)
  | Lesser(p)      -> Printf.sprintf "<   (syn)      : %s"   (fmt_pos p)
  | GreatEqual(p)  -> Printf.sprintf "<=  (syn)      : %s"   (fmt_pos p)
  | Greater(p)     -> Printf.sprintf ">   (syn)      : %s"   (fmt_pos p)
  | Semicolon(p)   -> Printf.sprintf ";   (syn)      : %s"   (fmt_pos p)
  | TriEllipses(p) -> Printf.sprintf "... (syn)      : %s"   (fmt_pos p)
  | BiEllipses(p)  -> Printf.sprintf "..  (syn)      : %s"   (fmt_pos p)
  | Plus(p)        -> Printf.sprintf "+   (syn)      : %s"   (fmt_pos p)
  | Minus(p)       -> Printf.sprintf "-   (syn)      : %s"   (fmt_pos p)
  | Star(p)        -> Printf.sprintf "*   (syn)      : %s"   (fmt_pos p)
  | Slash(p)       -> Printf.sprintf "/   (syn)      : %s"   (fmt_pos p)
  | Percent(p)     -> Printf.sprintf "%%  (syn)      : %s"   (fmt_pos p)
  | LowIdent(p, s) -> Printf.sprintf "%s (low-ident) : %s" s (fmt_pos p)
  | CapIdent(p, s) -> Printf.sprintf "%s (cap-ident) : %s" s (fmt_pos p)
  | Integer(p, i)  -> Printf.sprintf "%d (integer)   : %s" i (fmt_pos p)
  | String(p, s)   -> Printf.sprintf "%s (string)    : %s" s (fmt_pos p)
;;


let fmt_next_token tokens =
  match tokens with
  | tok :: _ -> fmt_token tok
  | [] -> "<nil>"
;;


let print_tokens tokens =
  let fmted = List.map fmt_token tokens in
  List.iter (Printf.printf "%s\n") fmted
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

  (* Encode this regex:
    //.*\n *)
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
    | "if" ->
        let tok = KWIf(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "else" ->
        let tok = KWElse(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "while" ->
        let tok = KWWhile(get_pos buf) in
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
    | "bool" ->
        let tok = KWBool(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "true" ->
        let tok = KWTrue(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "false" ->
        let tok = KWFalse(get_pos buf) in
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
    | "[" ->
        let tok = LBracket(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "]" ->
        let tok = RBracket(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "." ->
        let tok = Dot(get_pos buf) in
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
    | "==" ->
        let tok = EqualEqual(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "!=" ->
        let tok = BangEqual(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "=" ->
        let tok = Equal(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "<" ->
        let tok = Lesser(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "<=" ->
        let tok = LessEqual(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ">" ->
        let tok = Greater(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ">=" ->
        let tok = GreatEqual(get_pos buf) in
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
    | "%" ->
        let tok = Percent(get_pos buf) in
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
        let inside_quotes = String.sub lexeme 1 ((String.length lexeme) - 2) in
        let unescaped = Scanf.unescaped inside_quotes in
        let tok = String(get_pos buf, unescaped) in
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
