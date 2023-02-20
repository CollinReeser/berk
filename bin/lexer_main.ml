type token =
| Number of string
| Ident of string
| Op of string


let rec print_tokens tokens =
  begin match tokens with
  | [] -> ()
  | Number(s) :: rest ->
      Printf.printf "Number(%s)\n" s ;
      print_tokens rest
  | Ident(s) :: rest ->
      Printf.printf "Indent(%s)\n" s ;
      print_tokens rest
  | Op(s) :: rest ->
      Printf.printf "Op(%s)\n" s ;
      print_tokens rest
  end


let tokenize buf =
  let digit = [%sedlex.regexp? '0' .. '9'] in
  let number = [%sedlex.regexp? Plus digit] in
  let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z'] in

  let rec _tokenize buf tokens =
    begin match%sedlex buf with
    | number ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        _tokenize buf ((Number(lexeme)) :: tokens)

    | letter, Star ('A' .. 'Z' | 'a' .. 'z' | digit) ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        _tokenize buf ((Ident(lexeme)) :: tokens)

    | Plus (Chars "+*-/") ->
        let lexeme = Sedlexing.Latin1.lexeme buf in
        _tokenize buf ((Op(lexeme)) :: tokens)

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
  let lexbuf = Sedlexing.Latin1.from_string "foobar A123Bfoo  ++123Xbar/foo" in
  let tokens = tokenize lexbuf in
  print_tokens tokens
