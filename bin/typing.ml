
type berk_t =
  | U64
  | U32
  | U16
  | U8
  | I64
  | I32
  | I16
  | I8
  | F128
  | F64
  | F32
  | Bool
  | String
  | Nil
  | Tuple of berk_t list
  | Array of berk_t * int
  | Variant of string * (string * berk_t) list
  | VarArgSentinel
  | Undecided

let rec fmt_join_types delim types =
  match types with
  | [] -> ""
  | [x] -> fmt_type x
  | x::xs ->
      let lhs = fmt_type x in
      lhs ^ delim ^ (fmt_join_types delim xs)

and fmt_type berk_type =
  match berk_type with
  | U64 -> "u64"
  | U32 -> "u32"
  | U16 -> "u16"
  | U8  -> "u8"
  | I64 -> "i64"
  | I32 -> "i32"
  | I16 -> "i16"
  | I8  -> "i8"
  | F128 -> "f128"
  | F64  -> "f64"
  | F32  -> "f32"
  | Bool -> "bool"
  | String -> "string"
  | Nil -> "()"
  | Array (typ, sz) ->
      let sz_s = Printf.sprintf "%d" sz in
      "[" ^ (fmt_type typ) ^ " x " ^ sz_s ^ "]"
  | Tuple (types) -> "(" ^ (fmt_join_types ", " types) ^ ")"
  | Variant (type_name, variants) ->
      let variant_fmts = List.map (
        fun (var_name, typ) ->
          Printf.sprintf "| %s(%s)" var_name (fmt_type typ)
      ) variants in
      let variants_fmt = List.fold_left (^) "" variant_fmts in

      Printf.sprintf "variant %s {%s}" type_name variants_fmt

  | VarArgSentinel -> "..."
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
  let _common_type_of_lr lhs rhs =
    match (lhs, rhs) with
    | (I64, I64)
    | (I32, I64)
    | (I16, I64)
    | (I8,  I64) -> Some(I64)
    | (I32, I32)
    | (I16, I32)
    | (I8,  I32) -> Some(I32)
    | (I16, I16)
    | (I8,  I16) -> Some(I16)
    | (I8,  I8)  -> Some(I8)
    | (U64, U64)
    | (U32, U64)
    | (U16, U64)
    | (U8,  U64) -> Some(U64)
    | (U32, U32)
    | (U16, U32)
    | (U8,  U32) -> Some(U32)
    | (U16, U16)
    | (U8,  U16) -> Some(U16)
    | (U8,  U8)  -> Some(U8)
    | (F128, F128)
    | (F64, F128)
    | (F32, F128) -> Some(F128)
    | (F64, F64)
    | (F32, F64)  -> Some(F64)
    | (F32, F32)  -> Some(F32)
    | (Bool, Bool) -> Some(Bool)
    | (Nil, Nil) -> Some(Nil)

    | _ -> None
  in
  match _common_type_of_lr lhs rhs with
  | Some(t) -> t
  | None ->
    match _common_type_of_lr rhs lhs with
    | Some(t) -> t
    | None -> failwith "No common type"

and common_type_of_lst lst =
  match lst with
  | [] -> Nil
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs
;;

let rec type_convertible_to from_t to_t =
  match (from_t, to_t) with
  | (I64, I64)
  | (I32, I64)
  | (I16, I64)
  | (I8,  I64)
  | (I32, I32)
  | (I16, I32)
  | (I8,  I32)
  | (I16, I16)
  | (I8,  I16)
  | (I8,  I8) -> true

  | (U64, U64)
  | (U32, U64)
  | (U16, U64)
  | (U8,  U64)
  | (U32, U32)
  | (U16, U32)
  | (U8,  U32)
  | (U16, U16)
  | (U8,  U16)
  | (U8,  U8) -> true

  | (F128, F128)
  | (F64, F128)
  | (F32, F128)
  | (F64, F64)
  | (F32, F64)
  | (F32, F32) -> true

  | (String, String) -> true
  | (Bool, Bool) -> true
  | (Nil, Nil) -> true

  | (Tuple(lhs_types), Tuple(rhs_types)) ->
      if (List.length lhs_types) != (List.length rhs_types)
        then false
        else begin
          let agreements = List.map2 type_convertible_to lhs_types rhs_types in
          List.fold_left (==) true agreements
        end

  | Variant(lhs_v_name, lhs_ctors), Variant(rhs_v_name, rhs_ctors) ->
      if lhs_v_name = rhs_v_name
      then
        if List.length lhs_ctors = List.length rhs_ctors
        then
          let agreements =
            List.map2 (
              fun (lhs_name, lhs_typ) (rhs_name, rhs_typ) ->
                if lhs_name = rhs_name
                then type_convertible_to lhs_typ rhs_typ
                else false
            ) lhs_ctors rhs_ctors
          in
          List.fold_left (==) true agreements
        else false
      else false

  | _ ->
      let from_t_s = fmt_type from_t in
      let to_t_s = fmt_type to_t in
      begin
        Printf.printf "Cannot convert [%s] to [%s]\n" from_t_s to_t_s;
        false
      end
;;


let type_extendable_to from_t to_t =
  match (from_t, to_t) with
  | (I32, I64)
  | (I16, I64)
  | (I16, I32)
  | (I8,  I64)
  | (I8,  I32)
  | (I8,  I16) -> true

  | (U32, U64)
  | (U16, U64)
  | (U16, U32)
  | (U8,  U64)
  | (U8,  U32)
  | (U8,  U16) -> true

  | (F64, F128)
  | (F32, F128)
  | (F32, F64) -> true

  | _ ->
      let from_t_s = fmt_type from_t in
      let to_t_s = fmt_type to_t in
      begin
        Printf.printf "Cannot extend [%s] to [%s]\n" from_t_s to_t_s;
        false
      end
;;


let type_truncatable_to from_t to_t =
  match (from_t, to_t) with
  | (I64, I32)
  | (I64, I16)
  | (I64, I8)
  | (I32, I16)
  | (I32, I8)
  | (I16, I8) -> true

  | (U64, U32)
  | (U64, U16)
  | (U64, U8)
  | (U32, U16)
  | (U32, U8)
  | (U16, U8) -> true

  | (F128, F64)
  | (F128, F32)
  | (F64, F32) -> true

  | _ ->
      let from_t_s = fmt_type from_t in
      let to_t_s = fmt_type to_t in
      begin
        Printf.printf "Cannot truncate [%s] to [%s]\n" from_t_s to_t_s;
        false
      end
;;


let type_bitwise_to from_t to_t =
  match (from_t, to_t) with
  | (I64, U64)
  | (U64, I64) -> true

  | (I32, U32)
  | (U32, I32) -> true

  | (I16, U16)
  | (U16, I16) -> true

  | (I8, U8)
  | (U8, I8) -> true

  | _ ->
      let from_t_s = fmt_type from_t in
      let to_t_s = fmt_type to_t in
      begin
        Printf.printf "Cannot bitwise cast [%s] to [%s]\n" from_t_s to_t_s;
        false
      end
;;


let is_index_type idx_t =
  match idx_t with
  | U64
  | U32
  | U16
  | U8 -> true
  | _ ->
      let not_idx_s = fmt_type idx_t in
      Printf.printf "Cannot index into array with type [%s]\n" not_idx_s;
      false
;;


let is_indexable_type arr_t =
  match arr_t with
  | Array(_, _) -> true
  | _ ->
      let not_arr_s = fmt_type arr_t in
      Printf.printf "Type [%s] is not indexable indexable\n" not_arr_s;
      false
;;
