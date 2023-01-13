
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
 *)
(* let cartesian_product list_of_lists =
  let _cartesian_product remaining_init_lists products partial_product =
    match remaining_init_lists with
    | [] -> partial_product :: products
    | [x] ->
        let partial_product = x :: partial_product in
        let products = partial_product :: products in
        _cartesian_product remaining_init_lists products []
    | x::xs ->


  let _cartesian_product remaining_init_lists partial_product =
    match remaining_init_lists with


    | x::xs ->
        let partial_product = x :: partial_product *)



let gen_products product_so_far products_so_far current_list : _ list list =
  let rec _gen_products products_so_far remaining_list =
    begin match remaining_list with
    | [] -> products_so_far
    | x::xs ->
        let product = x :: product_so_far in
        let products_so_far = product :: products_so_far in
        _gen_products products_so_far xs
    end
  in

  (* Handle the special case where the input list is empty; we still want to
  yield the products of the input product times the "empty list", ie, the input
  product itself. *)
  match current_list with
  | [] -> product_so_far :: products_so_far
  | _ -> _gen_products products_so_far current_list

let cartesian_product2 lhs rhs : _ list list =
  (* We're going to be constructing each product "backwards", so if we reverse
  the order of our inputs beforehand, the final products will be in the right
  order. *)
  let (rhs, lhs) = (lhs, rhs) in

  let rec _cartesian_product2 lhs_rest products_so_far =
    match lhs_rest with
    | [] -> products_so_far
    | x::xs ->
        let products = gen_products [x] products_so_far rhs in
        _cartesian_product2 xs products
  in
  begin match (lhs, rhs) with
  | ([], []) -> []
  (* Handle special case. *)
  | ([], _) -> List.fold_left (fun xs x -> [x]::xs) [] rhs
  | (_, _) -> _cartesian_product2 lhs []
  end

