
type berk_t =
  | I64
  | I32
  | F32
  | Bool
  | Nil
  | Undecided

let rec common_type_of_lr lhs rhs =
  match (lhs, rhs) with
  | (I64, I64) -> I64
  | (I32, I64) -> I64
  | (I32, I32) -> I32
  | (F32, F32) -> F32
  | (Bool, Bool) -> Bool
  | (Nil, Nil) -> Nil
  | _ -> failwith "No common type"

and common_type_of_lst lst =
  match lst with
  | [] -> Nil
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs
;;

let type_convertible_to from_t to_t =
  match (from_t, to_t) with
  | (I64, I64) -> true
  | (I32, I32) -> true
  | (I32, I64) -> true
  | (F32, F32) -> true
  | (Bool, Bool) -> true
  | (Nil, Nil) -> true
  | _ -> failwith "Cannot convert from_t to to_t"
;;
