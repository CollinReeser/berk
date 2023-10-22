open Typing
open Utility
open Ir

type rast_t =
  | RU64
  | RU32
  | RU16
  | RU8
  | RI64
  | RI32
  | RI16
  | RI8
  | RF128
  | RF64
  | RF32
  | RBool
  | RString
  | RNil
  | RTuple of rast_t list
  (* A superposition of multiple tuples, where only one actually exists as a
  value at any one time. The overall size of this type is the size of the
  largest superimposed tuple. Essentially an untagged union but requiring each
  "superimposed type" to itself be a tuple. *)
  | RSuperTuple of rast_t list list
  | RArray of rast_t * int
  | RPtr of rast_t
  | RFunction of rast_t * rast_t list
  | RVarArgSentinel
  (* This is not generated by the front-end, but may be generated during
  lowering to indicate "the type of this data is actually the [N x i8] raw
  form of this type. " *)
  | RByteArray of rast_t
;;

type rbin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
;;

let variant_tag_rt = RU8;;

let rec berk_t_to_rast_t (t : berk_t) : rast_t =
  begin match t with
  | U64 -> RU64
  | U32 -> RU32
  | U16 -> RU16
  | U8 -> RU8
  | I64 -> RI64
  | I32 -> RI32
  | I16 -> RI16
  | I8 -> RI8
  | F128 -> RF128
  | F64 -> RF64
  | F32 -> RF32
  | Bool -> RBool
  | String -> RString
  | Nil -> RNil
  | VarArgSentinel -> RVarArgSentinel

  | Ref(refed_t) ->
      let pointed_rt = berk_t_to_rast_t refed_t in
      RPtr(pointed_rt)

  | Tuple(elem_ts) ->
      let elem_rts = List.map berk_t_to_rast_t elem_ts in
      RTuple(elem_rts)

  | Array(elem_t, i) ->
      let elem_rt = berk_t_to_rast_t elem_t in
      RArray(elem_rt, i)

  | Variant(_, v_ctor_xs) ->
      let _ = if List.length v_ctor_xs > 255 then
        failwith "Variants with >255 constructors not implemented"
      else
        ()
      in

      let ctor_tuples = List.map v_ctor_as_tagged_type_list v_ctor_xs in

      RSuperTuple(ctor_tuples)

  | Function(ret_t, args_ts) ->
      let ret_rt = berk_t_to_rast_t ret_t in
      let args_rts = List.map berk_t_to_rast_t args_ts in
      RFunction(ret_rt, args_rts)

  (* These types should have been eliminated during AST typechecking. *)
  | UnboundType(_, _)
  | Unbound(_)
  | Undecided ->
      failwith (
        Printf.sprintf "Error: Unexpected type during RAST lowering: %s"
        (fmt_type t)
      )
  end

(* Yield the tuple type that represents the given variant constructor, including
the prefixed implicit constructor tag. *)
and v_ctor_as_tagged_type_list {fields; _} : rast_t list =
  let fields_ts = List.map (fun {t} -> berk_t_to_rast_t t) fields in
  variant_tag_rt :: fields_ts
;;

let op_to_rop (op : bin_op) : rbin_op =
  begin match op with
  | Add -> Add
  | Sub -> Sub
  | Mul -> Mul
  | Div -> Div
  | Mod -> Mod
  | Eq -> Eq
  | Ne -> Ne
  | Lt -> Lt
  | Le -> Le
  | Gt -> Gt
  | Ge -> Ge

  | LOr
  | LAnd ->
      failwith (
        Printf.sprintf "op_to_rop: No conversion for op [ %s ] to rop."
        (fmt_bin_op op)
      )
  end
;;

let fmt_rbin_op op =
  begin match op with
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%%"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  end
;;

let rec fmt_join_types delim types =
  begin match types with
  | [] -> ""
  | [x] -> fmt_rtype x
  | x::xs ->
      let lhs = fmt_rtype x in
      lhs ^ delim ^ (fmt_join_types delim xs)
  end

and fmt_rtype (rast_type : rast_t) : string =
  begin match rast_type with
  | RU64 -> "u64"
  | RU32 -> "u32"
  | RU16 -> "u16"
  | RU8  -> "u8"
  | RI64 -> "i64"
  | RI32 -> "i32"
  | RI16 -> "i16"
  | RI8  -> "i8"
  | RF128 -> "f128"
  | RF64  -> "f64"
  | RF32  -> "f32"
  | RBool -> "bool"
  | RString -> "string"
  | RNil -> "()"
  | RVarArgSentinel -> "..."

  | RArray (typ, sz) ->
      Printf.sprintf "[%s x %d]" (fmt_rtype typ) sz

  | RTuple (types) ->
      let tuple_fmt = fmt_join_types ", " types in
      Printf.sprintf "(%s)" tuple_fmt

  | RSuperTuple (tss) ->
      let tuples = List.map (fun ts -> RTuple(ts)) tss in
      let tuple_fmt_xs = List.map fmt_rtype tuples in
      let tuples_fmt = fmt_join_strs " | " tuple_fmt_xs in
      Printf.sprintf "(%s)" tuples_fmt

  | RPtr (typ) ->
      Printf.sprintf "ptr %s"
        (fmt_rtype typ)

  | RByteArray (typ) ->
      Printf.sprintf "bytesof(%s)"
        (fmt_rtype typ)

  | RFunction (ret_t, arg_t_lst) ->
      Printf.sprintf "(%s)->%s"
        (fmt_join_types ", " arg_t_lst)
        (fmt_rtype ret_t)
  end
;;

(* TODO: This is not the most appropriate place for this function, because
really the backend code generator (eg, LLVM) should be the one making decisions
about the relative sizes of types (particularly because of alignment between
fields in aggregate types). We keep this here now while we lack a sufficient
abstraction mechanism to punt this to the backend side. *)
let rec sizeof_rtype (t : rast_t) =
  begin match t with
  | RFunction(_, _) -> 16
  (* FIXME: Not true yet, but will be if/when function ptrs become fat ptrs. *)
  | RF128 -> 16

  | RPtr(_) -> 8

  | RString -> 8
  | RU64 | RI64 | RF64 -> 8
  | RU32 | RI32 | RF32 -> 4
  | RU16 | RI16 -> 2
  | RU8  | RI8 -> 1
  | RBool -> 1
  | RNil -> 0

  | RTuple(ts) -> sum (List.map sizeof_rtype ts)
  | RArray(t, sz) -> sz * (sizeof_rtype t)

  | RSuperTuple(tss) ->
      (* The size of this type is the size of the largest superimposed tuple. *)
      let tuples = List.map (fun ts -> RTuple(ts)) tss in
      let sizes = List.map sizeof_rtype tuples in
      List.fold_left max 0 sizes

  | RByteArray(_)
  | RVarArgSentinel ->
      failwith (
        Printf.sprintf "Invalid to attempt sizeof_rtype([%s])" (fmt_rtype t)
      )
  end
;;

(* Get the list of types among a list-list that yield the largest total tuple
type size. *)
let get_largest_tuple (tss : rast_t list list) : rast_t list =
  let size_to_tuple_ts =
    List.map (
      fun ts ->
        let sz = sizeof_rtype (RTuple(ts)) in
        (sz, ts)
    ) tss
  in

  let (_, largest_tuple_ts) =
    List.fold_left (
      fun (max_sz_so_far, max_tup_so_far) (cur_sz, cur_tup) ->
        begin
          if max_sz_so_far < cur_sz then
            (cur_sz, cur_tup)
          else
            (max_sz_so_far, max_tup_so_far)
        end
    ) (0, []) size_to_tuple_ts
  in

  largest_tuple_ts
;;

(* Do two types exactly match. *)
let rec is_same_type (lhs : rast_t) (rhs : rast_t) : bool =
  begin match (lhs, rhs) with
  | (RU64, RU64)
  | (RU32, RU32)
  | (RU16, RU16)
  | (RU8,  RU8)
  | (RI64, RI64)
  | (RI32, RI32)
  | (RI16, RI16)
  | (RI8,  RI8)
  | (RF128, RF128)
  | (RF64,  RF64)
  | (RF32,  RF32)
  | (RBool, RBool)
  | (RString, RString)
  | (RNil, RNil)
  | (RVarArgSentinel, RVarArgSentinel) ->
      true

  | (RPtr(lhs), RPtr(rhs))
  | (RByteArray(lhs), RByteArray(rhs)) ->
      is_same_type lhs rhs

  | (RArray(lhs_t, lhs_i), RArray(rhs_t, rhs_i)) ->
      (lhs_i = rhs_i) && (is_same_type lhs_t rhs_t)

  | (RTuple(lhs_ts), RTuple(rhs_ts)) ->
      begin if (List.compare_lengths lhs_ts rhs_ts) = 0 then
        List.for_all2 is_same_type lhs_ts rhs_ts
      else
        false
      end

  | (RSuperTuple(lhs_tss), RSuperTuple(rhs_tss)) ->
      let lhs_tuples = List.map (fun ts -> RTuple(ts)) lhs_tss in
      let rhs_tuples = List.map (fun ts -> RTuple(ts)) rhs_tss in
      begin if (List.compare_lengths lhs_tuples rhs_tuples) = 0 then
        List.for_all2 is_same_type lhs_tuples rhs_tuples
      else
        false
      end

  | (RFunction(lhs_ret_t, lhs_arg_ts), RFunction(rhs_ret_t, rhs_arg_ts)) ->
      (is_same_type lhs_ret_t rhs_ret_t) &&
      ((List.compare_lengths lhs_arg_ts rhs_arg_ts) = 0) &&
      (List.for_all2 is_same_type lhs_arg_ts rhs_arg_ts)

  | (RU64, _)
  | (RU32, _)
  | (RU16, _)
  | (RU8, _)
  | (RI64, _)
  | (RI32, _)
  | (RI16, _)
  | (RI8, _)
  | (RF128, _)
  | (RF64, _)
  | (RF32, _)
  | (RBool, _)
  | (RString, _)
  | (RNil, _)
  | (RVarArgSentinel, _)
  | (RPtr(_), _)
  | (RArray(_, _), _)
  | (RTuple(_), _)
  | (RFunction(_), _)
  | (RByteArray(_), _)
  | (RSuperTuple(_), _) ->
      false
  end
;;

(* Do two types match with respect to how bitwise casts would treat them in
practice. *)
let rec is_bitwise_same_type lhs rhs =
  begin match (lhs, rhs) with
  | (RPtr(lhs_t), RPtr(rhs_t)) ->
      is_bitwise_same_type lhs_t rhs_t

  (* Handle the edge-case where the a super-tuple can be considered the same
  type as a classic tuple if the largest superimposed tuple matches the classic
  tuple. *)
  | ((RTuple(_) as classic_tup), RSuperTuple(tss)) ->
      let quantum_tup = RTuple(get_largest_tuple tss) in
      is_same_type classic_tup quantum_tup

  | (RSuperTuple(tss), (RTuple(_) as classic_tup)) ->
      let quantum_tup = RTuple(get_largest_tuple tss) in
      is_same_type classic_tup quantum_tup

  | (_, _) ->
      is_same_type lhs rhs
  end
;;

(* Determine the common type between two. ie, if they're not the same type, but
one is convertible to the other, yield the common type. *)
let rec common_type_of_lr (lhs : rast_t) (rhs : rast_t) : rast_t =
  let _common_type_of_lr (lhs : rast_t) (rhs : rast_t) : rast_t option =
    match (lhs, rhs) with
    | (RNil,                 RNil) -> Some(RNil)
    | ((RI64|RI32|RI16|RI8), RI64) -> Some(RI64)
    | ((RI32|RI16|RI8),      RI32) -> Some(RI32)
    | ((RI16|RI8),           RI16) -> Some(RI16)
    | (RI8,                  RI8 ) -> Some(RI8)
    | ((RU64|RU32|RU16|RU8), RU64) -> Some(RU64)
    | ((RU32|RU16|RU8),      RU32) -> Some(RU32)
    | ((RU16|RU8),           RU16) -> Some(RU16)
    | (RU8,                  RU8 ) -> Some(RU8)
    | ((RF128|RF64|RF32),   RF128) -> Some(RF128)
    | ((RF64|RF32),         RF64 ) -> Some(RF64)
    | (RF32,                RF32 ) -> Some(RF32)
    | (RBool,               RBool) -> Some(RBool)
    | (RString,           RString) -> Some(RString)

    | (RTuple(lhs_typs), RTuple(rhs_typs)) ->
        let common_tup_typs = List.map2 common_type_of_lr lhs_typs rhs_typs in
        Some(RTuple(common_tup_typs))

    | (RArray(lhs_elem_typ, lhs_sz), RArray(rhs_elem_typ, rhs_sz)) ->
        if lhs_sz = rhs_sz then
          let common_elem_typ = common_type_of_lr lhs_elem_typ rhs_elem_typ in
          Some(RArray(common_elem_typ, lhs_sz))
        else
          None

    | (RSuperTuple(lhs_tss), RSuperTuple(rhs_tss)) ->
        if (List.compare_lengths lhs_tss rhs_tss) = 0 then
          let common_tss =
            let lhs_tuples = List.map (fun ts -> RTuple(ts)) lhs_tss in
            let rhs_tuples = List.map (fun ts -> RTuple(ts)) rhs_tss in
            let common_tuples : rast_t list =
              List.map2 common_type_of_lr lhs_tuples rhs_tuples
            in
            List.map (
              fun common_tuple ->
                begin match common_tuple with
                | RTuple(ts) -> ts
                | _ -> failwith "Assert: Impossible: RSuperTuple"
                end
            ) common_tuples
          in
          Some(RSuperTuple(common_tss))
        else
          None

    | _ -> None
  in
  match _common_type_of_lr lhs rhs with
  | Some(t) -> t
  | None ->
    match _common_type_of_lr rhs lhs with
    | Some(t) -> t
    | None ->
        let lhs_fmt = fmt_rtype lhs in
        let rhs_fmt = fmt_rtype rhs in
        failwith (
          "No common type between [[" ^ lhs_fmt ^ "]] [[" ^ rhs_fmt ^ "]]"
        )

and common_type_of_lst lst : rast_t =
  match lst with
  | [] -> RNil
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs
;;

let unwrap_indexable (indexable_t : rast_t) =
  match indexable_t with
  | RArray(t, _) -> t
  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-indexable type: [%s]"
          (fmt_rtype indexable_t)
      )
;;

let unwrap_indexable_pointer (indexable_t : rast_t) =
  match indexable_t with
  | RPtr(RArray(arr_elem_t, _)) ->
      RPtr(arr_elem_t)

  | RPtr(RPtr(inner_t)) ->
      RPtr(inner_t)

  | RPtr(
      (
        RU64 | RU32 | RU16 | RU8 |
        RI64 | RI32 | RI16 | RI8 |
        RF128 | RF64 | RF32 |
        RBool | RString
      ) as inner_t
    ) ->
      failwith (
        Printf.sprintf
          "unwrap_indexable_pointer: RPtr(%s) -> %s\n%!"
          (fmt_rtype inner_t)
          (fmt_rtype inner_t)
        ;
      )

  | RPtr(inner_t) ->
      failwith (
        Printf.sprintf
          "Unwrapping ptr to [ %s ] unimplemented"
          (fmt_rtype inner_t)
      )

  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-pointer type: [ %s ]"
          (fmt_rtype indexable_t)
      )
;;

let unwrap_aggregate_indexable (indexable_t : rast_t) i =
  match indexable_t with
  | RTuple(ts) ->
      if i < List.length ts then
        List.nth ts i
      else
        failwith (Printf.sprintf "Invalid index into tuple of arity [%d]" i)

  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-indexable aggregate type: [%s]"
          (fmt_rtype indexable_t)
      )
;;

let unwrap_aggregate_indexable_pointer (indexable_t : rast_t) i =
  match indexable_t with
  | RPtr(RTuple(_) as tuple_t) ->
      let inner_t = unwrap_aggregate_indexable tuple_t i in
      RPtr(inner_t)

  | RPtr(inner_t) ->
      failwith (
        Printf.sprintf
          "Unwrapping ptr to [ %s ] unimplemented"
          (fmt_rtype inner_t)
      )

  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-pointer type: [ %s ]"
          (fmt_rtype indexable_t)
      )
;;

let unwrap_ptr ptr_t =
  match ptr_t with
  | RPtr(t) -> t
  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-ptr type [%s]" (fmt_rtype ptr_t)
      )
;;
