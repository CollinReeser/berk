
let take lst n =
  let rec _take accum remain n =
    begin match (remain, n) with
    | (_, 0)  -> accum
    | ([], _) -> failwith "Could not take remaining items: empty list"
    | (x::xs, _) -> _take (accum @ [x]) xs (n - 1)
    end
  in
  _take [] lst n
;;

let list_to_2_tuples lst =
  let rec every_pair so_far elem rest =
    begin match rest with
    | [] -> so_far
    | x::xs ->
        let so_far_up = (elem, x)::so_far in
        every_pair so_far_up elem xs
    end
  in

  let rec every_elem so_far rest =
    begin match rest with
    | [] -> so_far
    | x::xs ->
        let so_far_up = every_pair so_far x xs in
        every_elem so_far_up xs
    end
  in

  match lst with
  | []
  | [_] -> failwith "List too small to split into 2-tuples"
  | _ -> every_elem [] lst
;;

let combine3 lhs mid rhs =
  let rec _rev_combine3 so_far lhs mid rhs = begin match (lhs, mid, rhs) with
  | ([], [], []) -> so_far
  | (x::xs, y::ys, z::zs) ->
      let so_far = (x, y, z)::so_far in
      _rev_combine3 so_far xs ys zs
  | _ -> failwith "combine3 with non-matching lists"
  end in

  let rev_combined = _rev_combine3 [] lhs mid rhs in
  List.rev rev_combined

let rec fmt_join_strs delim idents : string =
  match idents with
  | [] -> ""
  | [ident] -> ident
  | ident::xs ->
      Printf.sprintf "%s%s%s"
        ident
        delim
        (fmt_join_strs delim xs)
;;
