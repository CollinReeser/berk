type position = {
  beg: Lexing.position;
  fin: Lexing.position;
}

and token =
| KWExtern of position
| LParen of position
| RParen of position
| LBrace of position
| RBrace of position
| Comma of position
| ColonEqual of position
| Colon of position
| Semicolon of position
| TriEllipses of position
| BiEllipses of position
| Integer of position * string
| LowIdent of position * string
| CapIdent of position * string
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


let rec print_tokens tokens =
  let fmt_pos (pos : position) =
    let (beg_line, beg_col, fin_line, fin_col) = lines_cols pos in
    Printf.sprintf
      "[%d:%d ; %d:%d]"
      beg_line beg_col fin_line fin_col
  in

  begin match tokens with
  | [] -> ()
  | KWExtern(p) :: rest ->
      Printf.printf "extern (kw) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | LParen(p) :: rest ->
      Printf.printf "( (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | RParen(p) :: rest ->
      Printf.printf ") (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | LBrace(p) :: rest ->
      Printf.printf "{ (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | RBrace(p) :: rest ->
      Printf.printf "} (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | Comma(p) :: rest ->
      Printf.printf ", (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | ColonEqual(p) :: rest ->
      Printf.printf ":= (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | Colon(p) :: rest ->
      Printf.printf ": (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | Semicolon(p) :: rest ->
      Printf.printf "; (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | TriEllipses(p) :: rest ->
      Printf.printf "... (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | BiEllipses(p) :: rest ->
      Printf.printf ".. (syn) : %s\n" (fmt_pos p) ;
      print_tokens rest
  | Integer(p, s) :: rest ->
      Printf.printf "%s (integer) : %s\n" s (fmt_pos p) ;
      print_tokens rest
  | LowIdent(p, s) :: rest ->
      Printf.printf "%s (low-ident) : %s\n" s (fmt_pos p) ;
      print_tokens rest
  | CapIdent(p, s) :: rest ->
      Printf.printf "%s (cap-ident) : %s\n" s (fmt_pos p) ;
      print_tokens rest
  | String(p, s) :: rest ->
      Printf.printf "%s (string) : %s\n" s (fmt_pos p) ;
      print_tokens rest
  end
;;


let tokenize buf =
  let digit = [%sedlex.regexp? '0' .. '9'] in
  let number = [%sedlex.regexp? Plus digit] in
  let str_simple_inner = [%sedlex.regexp? Star(Compl('"' | '\\'))] in
  let str_escape_inner =
    [%sedlex.regexp?
      Star('\\', any, Star(str_simple_inner))
    ] in
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
    | ";" ->
        let tok = Semicolon(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | "..." ->
        let tok = TriEllipses(get_pos buf) in
        _tokenize buf (tok :: tokens)
    | ".." ->
        let tok = BiEllipses(get_pos buf) in
        _tokenize buf (tok :: tokens)

    | number ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        let tok = Integer(get_pos buf, lexeme) in
        _tokenize buf (tok :: tokens)

    | 'A' .. 'Z', Star(id_continue) ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        let tok = CapIdent(get_pos buf, lexeme) in
        _tokenize buf (tok :: tokens)

    | ('_' | 'a' .. 'z'), Star(id_continue) ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        let tok = LowIdent(get_pos buf, lexeme) in
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


let () =
  let text = {|
    extern fn printf(fmt: string, ...): i32;

    fn main(): i8 {
      let my_str := "Hello, world!\n";
      printf(my_str);

      return 0;
    }
  |} in
  let lexbuf = Sedlexing.Latin1.from_gen (Gen.of_string text) in
  let tokens = tokenize lexbuf in
  print_tokens tokens
;;

