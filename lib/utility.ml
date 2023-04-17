
let sum (lst : int list) =
  List.fold_left (+) 0 lst
;;

let replace lst n elem =
  List.mapi (fun i x -> if i = n then elem else x) lst;;
;;

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
;;

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

let cartesian_prepend (items : _ list) (products : _ list list) : _ list list =
  let _cartesian_prepend_1 item (products : _ list list) =
    List.map (fun prod -> item :: prod) products
  in

  begin match items, products with
  | [], [] -> []
  | _, [] -> List.map (fun x -> [x]) items
  | [], _ -> products
  | _, _ ->
      List.fold_left (
        fun so_far item ->
          let new_products = _cartesian_prepend_1 item products in
          let so_far = new_products @ so_far in
          so_far
      ) [] items
  end

(* This function takes an input like: [[a; b]; [c; d; e]; [f; g]] and yields an
output like:
[
  [a; c; f];
  [a; c; g];
  [a; d; f];
  [a; d; g];
  [a; e; f];
  [a; e; g];
  [b; c; f];
  [b; c; g];
  [b; d; f];
  [b; d; g];
  [b; e; f];
  [b; e; g];
]

FIXME: This is a very inefficient implementation, with no tail recursion.
 *)
let rec cartesian_product (lists : _ list list) : _ list list =
  begin match lists with
  | [] -> []
  | hs::ts -> cartesian_prepend hs (cartesian_product ts)
  end
