type position = {
  beg: Lexing.position;
  fin: Lexing.position;
}

and token =
| Number of position * string
| Ident of position * string
| Op of position * string


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
      "[bL:%d, bC:%d; eL:%d, eC:%d]"
      beg_line beg_col fin_line fin_col
  in

  begin match tokens with
  | [] -> ()
  | Number(p, s) :: rest ->
      Printf.printf "Number(%s) : %s\n" s (fmt_pos p) ;
      print_tokens rest
  | Ident(p, s) :: rest ->
      Printf.printf "Indent(%s) : %s\n" s (fmt_pos p) ;
      print_tokens rest
  | Op(p, s) :: rest ->
      Printf.printf "Op(%s) : %s\n" s (fmt_pos p) ;
      print_tokens rest
  end
;;


let tokenize buf =
  let digit = [%sedlex.regexp? '0' .. '9'] in
  let number = [%sedlex.regexp? Plus digit] in
  let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z'] in

  let rec _tokenize buf tokens =
    begin match%sedlex buf with
    | number ->
        let (start, fin) = Sedlexing.loc buf in
        Printf.printf "LOC:Number(...)[%d, %d]\n" start fin ;

        let lexeme = Sedlexing.Latin1.lexeme buf in
        _tokenize buf ((Number(get_pos buf, lexeme)) :: tokens)

    | letter, Star ('A' .. 'Z' | 'a' .. 'z' | digit) ->
        let (start, fin) = Sedlexing.loc buf in
        Printf.printf "LOC:Ident(...)[%d, %d]\n" start fin ;

        let lexeme = Sedlexing.Latin1.lexeme buf in
        _tokenize buf ((Ident(get_pos buf, lexeme)) :: tokens)

    | Plus (Chars "+*-/") ->
        let (start, fin) = Sedlexing.loc buf in
        Printf.printf "LOC:Op(...)[%d, %d]\n" start fin ;

        let lexeme = Sedlexing.Latin1.lexeme buf in
        _tokenize buf ((Op(get_pos buf, lexeme)) :: tokens)

    | Plus xml_blank ->
        _tokenize buf tokens

    | eof ->
        tokens

    | 128 .. 255 ->
        failwith "Non ASCII"

    | _ -> failwith "Unexpected character"
    end
  in

  let tokens = _tokenize buf [] in
  List.rev tokens


let () =
  let text = "foobar A123Bfoo  \n  ++123Xbar/foo" in
  let lexbuf = Sedlexing.Latin1.from_gen (Gen.of_string text) in
  let tokens = tokenize lexbuf in
  print_tokens tokens
