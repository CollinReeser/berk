
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

(* Like List.fold_left_map, but takes two input lists. *)
let fold_left_map2 f acc lhs rhs =
  let rec _fold_left_map2 acc lhs_rest rhs_rest results_rev =
    begin match (lhs_rest, rhs_rest) with
    | ([], []) -> (acc, results_rev)
    | ([], _)
    | (_, []) -> failwith "fold_left_map2: Mismatched lists!"
    | (x::lhs_rest', y::rhs_rest') ->
        let (acc', result) = f acc x y in
        _fold_left_map2 acc' lhs_rest' rhs_rest' (result::results_rev)
    end
  in

  let (acc', results_rev) = _fold_left_map2 acc lhs rhs [] in
  let results = List.rev results_rev in
  (acc', results)
;;

let map2i (f : int -> 'a -> 'b -> 'c) (lhs : 'a list) (rhs : 'b list) =
  let rec _map2i so_far_rev i lhs rhs =
    begin match (lhs, rhs) with
    | ([], []) -> so_far_rev

    | ([], _)
    | (_, []) -> failwith "map2i invoked on unequal lists"

    | (l::lhs_rest, r::rhs_rest) ->
        let elem = f i l r in
        _map2i (elem::so_far_rev) (i + 1) lhs_rest rhs_rest
    end
  in

  let elems_rev = _map2i [] 0 lhs rhs in
  List.rev elems_rev
;;

(* Split a list into a 2-tuple: (elems-before-i, elems-after-i)
where the i'th element is skipped. *)
let partition_i i ls : ('a list * 'b list) =
  let rec _partition_i idx ls_rest ls_lhs_rev ls_rhs_rev =
    begin match ls_rest with
    | [] -> (ls_lhs_rev, ls_rhs_rev)

    | cur :: ls_rest ->
        begin if idx < i then
          _partition_i (idx + 1) ls_rest (cur :: ls_lhs_rev) ls_rhs_rev
        else if idx > i then
          _partition_i (idx + 1) ls_rest ls_lhs_rev (cur :: ls_rhs_rev)
        else
          _partition_i (idx + 1) ls_rest ls_lhs_rev ls_rhs_rev
        end
    end
  in
  let (ls_lhs_rev, ls_rhs_rev) = _partition_i 0 ls [] [] in
  let ls_lhs = List.rev ls_lhs_rev in
  let ls_rhs = List.rev ls_rhs_rev in
  (ls_lhs, ls_rhs)
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
