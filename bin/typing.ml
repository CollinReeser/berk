
type berk_type =
  | I64
  | I32
  | Bool

let rec common_type_of_lr lhs rhs =
  match (lhs, rhs) with
  | (Some(I64), Some(I64)) -> Some(I64)
  | (Some(Bool), Some(Bool)) -> Some(Bool)
  | _ -> None

and common_type_of_lst lst =
  match lst with
  | [] -> None
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs
;;
