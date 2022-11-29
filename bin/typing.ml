
type berk_t =
  | I64
  | I32
  | F32
  | Bool
  | Nil
  | Undecided

let fmt_type berk_type =
  match berk_type with
  | I64 -> "i64"
  | I32 -> "i32"
  | F32 -> "f32"
  | Bool -> "bool"
  | Nil -> "()"
  | Undecided -> "<?undecided?>"
;;


type var_qual = {
  mut: bool;
}

let fmt_var_qual {mut} =
  if mut then "mut " else ""
;;


let def_var_qual = {mut = false}

let rec common_type_of_lr lhs rhs =
  match (lhs, rhs) with
  | (I64, I64) -> I64
  | (I32, I64) -> I64
  | (I64, I32) -> I64
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
  | _ ->
      let from_t_s = fmt_type from_t in
      let to_t_s = fmt_type to_t in
      failwith (Printf.sprintf "Cannot convert [%s] to [%s]" from_t_s to_t_s)
;;
