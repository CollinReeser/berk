open Utility

module StrMap = Map.Make(String)

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
  | VarArgSentinel
  (* A ref to a type is like a pointer to a value, but the ref itself cannot be
  re-assigned, and it cannot outlive the referenced value. *)
  | Ref of berk_t
  | Tuple of berk_t list
  | Array of berk_t * int
  | Variant of string * v_ctor list
      (*
        Variant("Option", [("Some", Unbound("`a")); (None, Nil)])
      *)
  | Function of berk_t * berk_t list

  (* A user-defined type, that we're not sure what it is yet. Typically
  generated during parse and resolved during typecheck.

  The first field is the type name, and the second is the possibly-empty list of
  template instantiation parameters.
  *)
  | UnboundType of string * berk_t list

  (* A type variable, a la `t *)
  | Unbound of string

  (* An Array, but the int size is not instantiated yet, with a template
  variable instead. LHS is the type that this is an array of. RHS is an instance
  of Unbound (and any other RHS is ill-formed). *)
  | SizeTemplatedArray of berk_t * berk_t
  (* A "type" used as the RHS of a size-templated type. Value is the size of the
  type. This should only be used while instantiating templated types. *)
  | UnboundSize of int

  | Undecided

and v_ctor = {name: string; fields: v_ctor_field list}

and v_ctor_field = {t: berk_t}

let rec fmt_join_types ?(pretty_unbound=false) delim types =
  match types with
  | [] -> ""
  | [x] -> fmt_type ~pretty_unbound:pretty_unbound x
  | x::xs ->
      let lhs = fmt_type ~pretty_unbound:pretty_unbound x in
      lhs ^ delim ^ (fmt_join_types ~pretty_unbound:pretty_unbound delim xs)

and fmt_type ?(pretty_unbound=false) berk_type : string =
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
      "[" ^ (fmt_type ~pretty_unbound:pretty_unbound typ) ^ " x " ^ sz_s ^ "]"
  | Tuple (types) ->
      "(" ^ (fmt_join_types ~pretty_unbound:pretty_unbound ", " types) ^ ")"
  | Variant (type_name, variant_ctors) ->
      let ctor_fmts = List.map fmt_v_ctor variant_ctors in
      let variants_fmt = fmt_join_strs " | " ctor_fmts in

      Printf.sprintf "variant %s {%s}" type_name variants_fmt

  | Ref (typ) ->
      Printf.sprintf "ref %s"
        (fmt_type ~pretty_unbound:pretty_unbound typ)

  | Function (ret_t, arg_t_lst) ->
      Printf.sprintf "(%s)->%s"
        (fmt_join_types ~pretty_unbound:pretty_unbound ", " arg_t_lst)
        (fmt_type ~pretty_unbound:pretty_unbound ret_t)

  | VarArgSentinel -> "..."

  | UnboundType(name, ts) ->
      let ts_fmt =
        if List.length ts = 0 then
          ""
        else
          "<" ^ (fmt_join_types ~pretty_unbound:pretty_unbound ", " ts) ^ ">"
      in
      Printf.sprintf "%s:(unbound-type)%s"
        name
        ts_fmt

  | Unbound (type_var) ->
      if pretty_unbound
      then type_var
      else "<?unbound:" ^ type_var ^ "?>"

  | UnboundSize (i) ->
      if pretty_unbound
      then Printf.sprintf "%d" i
      else Printf.sprintf "<?unbound-size:%d?>" i

  | SizeTemplatedArray (typ, size_var) ->
      let typ_fmt = fmt_type ~pretty_unbound:pretty_unbound typ in
      let sz_fmt = fmt_type ~pretty_unbound:pretty_unbound size_var in
      "[" ^ typ_fmt ^ " x " ^ sz_fmt ^ "]"

  | Undecided -> "<?undecided?>"

and fmt_v_ctor ?(pretty_unbound=false) {name; fields} : string =
  let fields_fmt =
    begin match fields with
    | [] -> ""
    | _ ->
        let fields_fmt =
          List.map (
            fun {t} -> fmt_type ~pretty_unbound:pretty_unbound t
          ) fields
        in
        Printf.sprintf "(%s)" (fmt_join_strs ", " fields_fmt)
    end
  in
  Printf.sprintf "%s%s" name fields_fmt
;;

let pprint_berk_t ppf berk_type =
  Format.fprintf ppf "%s" (fmt_type ~pretty_unbound:true berk_type)
;;

type var_qual = {
  mut: bool;
}

let fmt_var_qual {mut} =
  if mut then "mut " else ""
;;

let dump_var_qual_ast {mut} =
  Printf.sprintf "var_qual{mut=%b}" mut
;;

let def_var_qual = {mut = false}


(* Return true iff this type has a deterministic default value that can be used
for variable declarations that do not include a RHS expression. *)
let rec has_default_value t =
  begin match t with
  | U64 | U32 | U16 | U8
  | I64 | I32 | I16 | I8
  | F128 | F64 | F32
  | Bool
  | String
  | Nil ->
      true

  | Array(t, _) ->
      has_default_value t

  | Tuple(ts) ->
      List.for_all has_default_value ts

  | Variant(_, _) ->
      (* Variants must always be assigned an explicit value at declaration
      time; there is no "default constructor". *)
      false

  | Ref(_) ->
      (* References must always point to something. *)
      false

  | Function(_, _) ->
      (* Function pointers must always point to a specific function. *)
      false

  | VarArgSentinel ->
      (* It should be impossible to construct a variable declaration in the
      language syntax that resolves to the var-arg sentinel type. *)
      failwith (
        "Error: Cannot determine whether VarArgSentinel has default value"
      )

  | UnboundType(_, _)
  | Unbound(_)
  | UnboundSize(_)
  | SizeTemplatedArray (_, _)
  | Undecided ->
      (* Placeholder/unresolved type variables cannot have default values. *)
      false
  end
;;


(* Do two types exactly match. *)
let rec is_same_type (lhs : berk_t) (rhs : berk_t) : bool =
  begin match (lhs, rhs) with
  | (Undecided, Undecided) -> true

  | (Unbound(lhs_name), Unbound(rhs_name)) ->
      lhs_name = rhs_name

  | (UnboundType(lhs_name, lhs_ts), UnboundType(rhs_name, rhs_ts)) ->
      lhs_name = rhs_name && List.for_all2 is_same_type lhs_ts rhs_ts

  | (UnboundSize(lhs_i), UnboundSize(rhs_i)) ->
      lhs_i = rhs_i

  | (
      SizeTemplatedArray(lhs_t, lhs_size_var),
      SizeTemplatedArray(rhs_t, rhs_size_var)
    ) ->
      is_same_type lhs_t rhs_t && is_same_type lhs_size_var rhs_size_var

  | (U64, U64)
  | (U32, U32)
  | (U16, U16)
  | (U8,  U8)
  | (I64, I64)
  | (I32, I32)
  | (I16, I16)
  | (I8,  I8)
  | (F128, F128)
  | (F64,  F64)
  | (F32,  F32)
  | (Bool, Bool)
  | (String, String)
  | (Nil, Nil)
  | (VarArgSentinel, VarArgSentinel) ->
      true

  | (Ref(lhs), Ref(rhs)) ->
      is_same_type lhs rhs

  | (Array(lhs_t, lhs_i), Array(rhs_t, rhs_i)) ->
      (lhs_i = rhs_i) && (is_same_type lhs_t rhs_t)

  | (Tuple(lhs_ts), Tuple(rhs_ts)) ->
      begin if (List.compare_lengths lhs_ts rhs_ts) = 0 then
        List.for_all2 is_same_type lhs_ts rhs_ts
      else
        false
      end

  | (Function(lhs_ret_t, lhs_arg_ts), Function(rhs_ret_t, rhs_arg_ts)) ->
      (is_same_type lhs_ret_t rhs_ret_t) &&
      ((List.compare_lengths lhs_arg_ts rhs_arg_ts) = 0) &&
      (List.for_all2 is_same_type lhs_arg_ts rhs_arg_ts)

  | (Variant(lhs_name, lhs_ctors), Variant(rhs_name, rhs_ctors)) ->
      if lhs_name = rhs_name then
        let _is_same_ctor
          {name=lhs_name; fields=lhs_fields}
          {name=rhs_name; fields=rhs_fields}
        =
          if lhs_name = rhs_name then
            List.for_all2 (
              fun {t=lhs_t} {t=rhs_t} -> is_same_type lhs_t rhs_t
            ) lhs_fields rhs_fields
          else
            false
        in
        List.for_all2 _is_same_ctor lhs_ctors rhs_ctors

      else
        false

  | (Undecided, _)
  | (Unbound(_), _)
  | (UnboundType(_, _), _)
  | (UnboundSize(_), _)
  | (SizeTemplatedArray(_, _), _)
  | (U64, _)
  | (U32, _)
  | (U16, _)
  | (U8, _)
  | (I64, _)
  | (I32, _)
  | (I16, _)
  | (I8, _)
  | (F128, _)
  | (F64, _)
  | (F32, _)
  | (Bool, _)
  | (String, _)
  | (Nil, _)
  | (VarArgSentinel, _)
  | (Ref(_), _)
  | (Array(_, _), _)
  | (Tuple(_), _)
  | (Function(_), _)
  | (Variant(_, _), _) ->
      false
  end
;;


(* Get the index of the given ctor name in the given list of variant ctors *)
let get_tag_index_by_variant_ctor v_t ctor_name =
  let v_ctors =
    begin match v_t with
    | Variant(_, v_ctors) -> v_ctors
    | _ ->
        failwith (
          Printf.sprintf "Unexpected non-variant type [%s] in [%s]"
            (fmt_type v_t)
            (__FUNCTION__)
        )
    end
  in

  let rec _get_variant_ctor_tag_index accum v_ctors_tail =
    begin match v_ctors_tail with
    | [] -> failwith ("Failed to find " ^ ctor_name ^ " within variant")
    | {name; _}::xs ->
        begin if name = ctor_name then
          accum
        else
          _get_variant_ctor_tag_index (accum + 1) xs
        end
    end
  in

  _get_variant_ctor_tag_index 0 v_ctors
;;

(* Get the index of the given ctor name in the given list of variant ctors *)
let get_variant_ctor_by_tag_index v_ctors idx =
  List.nth v_ctors idx
;;


(* Determine the common type between two. ie, if they're not the same type, but
one is convertible to the other, yield the common type. *)
let rec common_type_of_lr lhs rhs =
  let _common_type_of_lr lhs rhs =
    match (lhs, rhs) with
    | (Undecided, Undecided) -> Some(Undecided)

    | (Unbound(_), Undecided)
    | (Undecided, Unbound(_)) ->
        failwith "Nonsense mapping from unbound typevar to undecided type"

    | (_,         Undecided) -> Some(lhs)
    | (Undecided,         _) -> Some(rhs)

    | (Nil,              Nil) -> Some(Nil)
    | (Nil,                _) -> None

    | ((I64|I32|I16|I8), I64) -> Some(I64)
    | ((I32|I16|I8),     I32) -> Some(I32)
    | ((I16|I8),         I16) -> Some(I16)
    | (I8,               I8 ) -> Some(I8)
    | ((I64|I32|I16|I8),   _) -> None

    | ((U64|U32|U16|U8), U64) -> Some(U64)
    | ((U32|U16|U8),     U32) -> Some(U32)
    | ((U16|U8),         U16) -> Some(U16)
    | (U8,               U8 ) -> Some(U8)
    | ((U64|U32|U16|U8),   _) -> None

    | ((F128|F64|F32),  F128) -> Some(F128)
    | ((F64|F32),       F64 ) -> Some(F64)
    | (F32,             F32 ) -> Some(F32)
    | ((F128|F64|F32),     _) -> None

    | (Bool,            Bool) -> Some(Bool)
    | (Bool,               _) -> None

    | (String,        String) -> Some(String)
    | (String,             _) -> None

    | (Unbound(lhs_typevar), Unbound(rhs_typevar)) ->
        if lhs_typevar = rhs_typevar then Some(Unbound(lhs_typevar)) else None

    | (Unbound(_), _) -> Some(rhs)
    | (_, Unbound(_)) -> Some(lhs)

    | (UnboundSize(lhs_i), UnboundSize(rhs_i)) ->
        if lhs_i = rhs_i then Some(UnboundSize(lhs_i)) else None
    | (UnboundSize(_), _) -> None

    | (
        SizeTemplatedArray(lhs_t, lhs_size_var),
        SizeTemplatedArray(rhs_t, rhs_size_var)
      ) ->
        if is_same_type lhs_size_var rhs_size_var then
          let common_t = common_type_of_lr lhs_t rhs_t in
          Some(SizeTemplatedArray(common_t, lhs_size_var))
        else
          None
    | (SizeTemplatedArray(_, _), _) -> None

    | (Tuple(lhs_typs), Tuple(rhs_typs)) ->
        let common_tup_typs = List.map2 common_type_of_lr lhs_typs rhs_typs in
        Some(Tuple(common_tup_typs))

    | (Tuple(_), _) -> None

    | (Array(lhs_elem_typ, lhs_sz), Array(rhs_elem_typ, rhs_sz)) ->
        if lhs_sz = rhs_sz then
          let common_elem_typ = common_type_of_lr lhs_elem_typ rhs_elem_typ in
          Some(Array(common_elem_typ, lhs_sz))
        else
          None

    | (Array(_, _), _) -> None

    | (Variant(lhs_name, lhs_ctor_lst), Variant(rhs_name, rhs_ctor_lst)) ->
        if lhs_name = rhs_name then
          if (List.compare_lengths lhs_ctor_lst rhs_ctor_lst) = 0 then
            let common_ctors =
              List.map2 common_v_ctor lhs_ctor_lst rhs_ctor_lst
            in
            Some(Variant(lhs_name, common_ctors))
          else
            None
        else
          None

    | (Variant(_, _), _) -> None

    | (Ref(lhs_t), Ref(rhs_t)) ->
        begin if is_same_type lhs_t rhs_t then
          Some(Ref(lhs_t))
        else
          None
        end

    | (Ref(_), _) -> None

    | (UnboundType(_, _), _)
    | (VarArgSentinel, _)
    | (Function(_, _), _) ->
        failwith (
          Printf.sprintf
            "Unimplemented: common_type_of_lr(%s, %s)"
            (fmt_type lhs)
            (fmt_type rhs)
        )
  in
  match _common_type_of_lr lhs rhs with
  | Some(t) -> t
  | None ->
    match _common_type_of_lr rhs lhs with
    | Some(t) -> t
    | None ->
        let lhs_fmt = fmt_type lhs in
        let rhs_fmt = fmt_type rhs in
        failwith (
          "No common type between [[" ^ lhs_fmt ^ "]] [[" ^ rhs_fmt ^ "]]"
        )

(* Helper function for determining the "common" variant ctor between two. *)
and common_v_ctor_opt
  {name=lhs_name; fields=lhs_fields}
  {name=rhs_name; fields=rhs_fields} : v_ctor option
=
  if
    lhs_name <> rhs_name || List.length lhs_fields <> List.length rhs_fields
  then
    None
  else
    let common_fields =
      List.map2 (
        fun {t=lhs_t} {t=rhs_t} ->
          let common_t = common_type_of_lr lhs_t rhs_t in
          {t=common_t}
      ) lhs_fields rhs_fields
    in
    Some({name=lhs_name; fields=common_fields})

and common_v_ctor lhs_ctor rhs_ctor : v_ctor =
  let common_ctor_opt = common_v_ctor_opt lhs_ctor rhs_ctor in
  begin match common_ctor_opt with
  | Some(ctor) -> ctor
  | None ->
      failwith (
        Printf.sprintf
          "Failed to unify fields of variant ctors: [%s] vs [%s]"
          (fmt_v_ctor lhs_ctor)
          (fmt_v_ctor rhs_ctor)
      )
  end

(* Given a variant type and a constructor whose name exists within that variant,
return a new variant type whose constructor by that name has been replaced with
the given one. *)
and inject_ctor_into_variant
  v_t ({name=ctor_name; _} as new_v_ctor : v_ctor) : berk_t
=
  begin match v_t with
  | Variant(v_name, orig_v_ctors) ->
      let tag_index = get_tag_index_by_variant_ctor v_t ctor_name in
      let new_v_ctors = replace orig_v_ctors tag_index new_v_ctor in
      Variant(v_name, new_v_ctors)

  | _ ->
      failwith (
        Printf.sprintf
          "Called inject_ctor_into_variant with non-variant type [[ %s ]]\n"
          (fmt_type v_t)
      )
  end

and common_type_of_lst lst =
  match lst with
  | [] -> Nil
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs
;;

let rec type_convertible_to from_t to_t =
  (* Helper function for determining if an individual variant ctor is
  implicitly convertible to another. *)
  let _v_ctor_convertible_to
    {name=lhs_name; fields=lhs_fields}
    {name=rhs_name; fields=rhs_fields} : bool
  =
    if
      lhs_name <> rhs_name || List.length lhs_fields <> List.length rhs_fields
    then
      false
    else
      let agreements =
        List.map2 (
          fun {t=lhs_t} {t=rhs_t} ->
            type_convertible_to lhs_t rhs_t
        ) lhs_fields rhs_fields
      in
      List.fold_left (&&) true agreements
  in

  match (from_t, to_t) with
  | (_, Unbound(_)) -> true
  | (Unbound(_), _) -> true

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

  | (Function(lhs_ret_t, lhs_args_ts), Function(rhs_ret_t, rhs_args_ts)) ->
      let ret_t_convertible = type_convertible_to lhs_ret_t rhs_ret_t in
      let args_ts_convertible =
        List.fold_left (=) true (
          List.map2 type_convertible_to lhs_args_ts rhs_args_ts
        )
      in
      if ret_t_convertible && args_ts_convertible then true else false

  | (Tuple(lhs_types), Tuple(rhs_types)) ->
      if (List.length lhs_types) <> (List.length rhs_types)
        then false
        else begin
          let agreements = List.map2 type_convertible_to lhs_types rhs_types in
          List.fold_left (&&) true agreements
        end

  | Array(lhs_elem_typ, lhs_sz), Array(rhs_elem_typ, rhs_sz) ->
      lhs_sz = rhs_sz &&
      type_convertible_to lhs_elem_typ rhs_elem_typ

  | Variant(lhs_v_name, lhs_ctors), Variant(rhs_v_name, rhs_ctors) ->
      if lhs_v_name = rhs_v_name
      then
        if List.length lhs_ctors = List.length rhs_ctors
        then
          let agreements =
            List.map2 _v_ctor_convertible_to lhs_ctors rhs_ctors
          in
          List.fold_left (&&) true agreements
        else false
      else false

  | (Ref(lhs_t), Ref(rhs_t)) ->
      type_convertible_to lhs_t rhs_t

  (* A type is implicitly convertible to a reference to that type. *)
  | (lhs_t, Ref(rhs_t)) ->
      type_convertible_to lhs_t rhs_t

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


(* Retrieve a variant constructor by name from the given variant type. *)
let get_v_ctor_opt v_t ctor_name : v_ctor option =
  begin match v_t with
  | Variant(_, v_ctors) ->
      List.find_opt (
        fun {name; _} -> name = ctor_name
      ) v_ctors
  | _ -> None
  end
;;


let has_v_ctor v_t ctor_name : bool =
  let ctor_opt = get_v_ctor_opt v_t ctor_name in
  begin match ctor_opt with
  | Some(_) -> true
  | None -> false
  end
;;


(* Retrieve a variant constructor by name from the given variant type. *)
let get_v_ctor v_t ctor_name : v_ctor =
  let ctor_opt = get_v_ctor_opt v_t ctor_name in
  begin match ctor_opt with
  | Some(v_ctor) -> v_ctor
  | None ->
      failwith (
        Printf.sprintf "Variant type [%s] has no constructor [%s]"
          (fmt_type v_t)
          ctor_name
      )
  end
;;


let get_v_ctor_fields v_t ctor_name : v_ctor_field list =
  let {fields; _} = get_v_ctor v_t ctor_name in
  fields
;;


let get_v_ctor_fields_ts v_t ctor_name : berk_t list =
  let fields = get_v_ctor_fields v_t ctor_name in
  let ts = List.map (fun {t} -> t) fields in
  ts
;;


(* Returns true if the given type is a variant such that all of its constructors
have zero fields (ie, a C-style enum). Returns false otherwise. *)
let rec is_zero_field_variant t : bool =
  begin match t with
  | Variant(_, v_ctors) ->
      let each_ctor_empty = List.map is_zero_field_v_ctor v_ctors in
      let all_ctors_empty = List.fold_left (&&) true each_ctor_empty in
      all_ctors_empty

  | _ -> false
  end

and is_zero_field_v_ctor {fields; _} =
  match fields with
  | [] -> true
  | _ -> false
;;


(* Return true if the two variant ctors approximately match.  *)
let v_ctors_match lhs_ctor rhs_ctor =
  (* TODO: This is broken. This can lead to a superset type apparently matching
  a subset type. *)
  let common_ctor_opt = common_v_ctor_opt lhs_ctor rhs_ctor in
  begin match common_ctor_opt with
  | Some(_) -> true
  | None -> false
  end
;;


(* Build a bare-bones variant constructor record, based on the name and the
possibly-empty list of raw types that constitute the constructor fields. *)
let build_ctor_from_ts name ts : v_ctor =
  let fields = List.map (fun t -> {t}) ts in
  {name; fields}
;;


let get_tuple_of_ctor {fields; _} : berk_t =
  let ts = List.map (fun {t} -> t) fields in
  Tuple(ts)
;;


let is_index_type idx_t =
  match idx_t with
  | I64
  | I32
  | I16
  | I8
  | U64
  | U32
  | U16
  | U8 -> true
  | _ ->
      let not_idx_s = fmt_type idx_t in
      Printf.printf "Cannot index into array with type [%s]\n" not_idx_s;
      false
;;


let rec is_indexable_type arr_t =
  match arr_t with
  | Array(_, _) -> true
  | Ref(inner_indexable_t) -> is_indexable_type inner_indexable_t
  | _ ->
      let not_arr_s = fmt_type arr_t in
      Printf.printf "Type [%s] is not indexable\n" not_arr_s;
      false
;;


let rec unwrap_indexable indexable_t =
  match indexable_t with
  | Array(t, _) -> t
  | Ref(inner_indexable_t) -> unwrap_indexable inner_indexable_t
  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-indexable type: [%s]"
          (fmt_type indexable_t)
      )
;;


let rec unwrap_aggregate_indexable indexable_t i =
  match indexable_t with
  | Tuple(ts) ->
      if i < List.length ts then
        List.nth ts i
      else
        failwith (Printf.sprintf "Invalid index into tuple of arity [%d]" i)
  | Ref(inner_indexable_t) ->
      unwrap_aggregate_indexable inner_indexable_t i
  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-indexable aggregate type: [%s]"
          (fmt_type indexable_t)
      )
;;


let unwrap_aggregate_indexable_reference (indexable_t : berk_t) i =
  match indexable_t with
  | Ref(Tuple(_) as tuple_t) ->
      let inner_t = unwrap_aggregate_indexable tuple_t i in
      Ref(inner_t)

  | Ref(inner_t) ->
      failwith (
        Printf.sprintf
          "Unwrapping ref to [ %s ] unimplemented"
          (fmt_type inner_t)
      )

  | _ ->
      failwith (
        Printf.sprintf "Cannot unwrap non-reference type: [ %s ]"
          (fmt_type indexable_t)
      )
;;


(* Unwrap a reference around a type, if there is one. If there are multiple
layers of reference around a type, errors, to detect improper reference handling
elsewhere. *)
let unwrap_ref t =
  match t with
  | Ref(Ref(_)) ->
      failwith (
        Printf.sprintf "Found double-wrapped reference type: [%s]" (fmt_type t)
      )
  | Ref(inner_t) -> inner_t
  | _ ->
      failwith (
        Printf.sprintf
          "Unexpectedly attempting to unwrap non-ref: [%s]"
          (fmt_type t)
      )
;;

(* Wrap the given type as a reference to that type. This is primarily useful
for avoiding "double-wrapping" a type, as at most only one layer of reference to
a type ever makes sense. *)
let wrap_ref t =
  begin match t with
  | Ref(_) -> t
  | _ -> Ref(t)
  end
;;


(* Make concrete the given type, to the extent possible, via the mappings in the
given string-type-variable-to-type mapping. *)
let rec concretify_unbound_types (tvar_to_t : berk_t StrMap.t) typ =
  (* Helper function for concretifying an individual variant ctor. Types that
  concretify to Nil are excised. *)
  let _concretify_v_ctor (tvar_to_t : berk_t StrMap.t) {name; fields} : v_ctor =
    let concrete_fields =
      List.filter_map (
        fun {t} ->
          let concrete_t = concretify_unbound_types tvar_to_t t in
          if is_same_type concrete_t Nil then
            None
          else
            Some {t=concrete_t}
      ) fields
    in
    {name; fields=concrete_fields}
  in

  match typ with
  | U64  | U32 | U16 | U8
  | I64  | I32 | I16 | I8
  | F128 | F64 | F32
  | Bool
  | String
  | Nil
  | VarArgSentinel
  | Undecided -> typ

  | Unbound(tvar) ->
      begin match (StrMap.find_opt tvar tvar_to_t) with
      | None -> Unbound(tvar)
      | Some(t) -> t
      end

  | UnboundType(name, ts) ->
      let ts_concrete = List.map (concretify_unbound_types tvar_to_t) ts in
      UnboundType(name, ts_concrete)

  | UnboundSize(i) ->
      failwith (
        Printf.sprintf
          "Error: concretify_unbound_types called on UnboundSize(%d)"
          i
      )

  | Ref(refed_t) ->
      let refed_concretified_t =
        concretify_unbound_types tvar_to_t refed_t
      in

      Ref(refed_concretified_t)

  | Tuple(tuple_typs) ->
      let typs_concretified =
        List.map (concretify_unbound_types tvar_to_t) tuple_typs
      in

      Tuple(typs_concretified)

  | Array(arr_typ, sz) ->
      let arr_typ_concretified = concretify_unbound_types tvar_to_t arr_typ in
      Array(arr_typ_concretified, sz)

  | SizeTemplatedArray(typ, Unbound(tvar)) ->
      begin match (StrMap.find_opt tvar tvar_to_t) with
      | Some(UnboundSize(i)) ->
          concretify_unbound_types tvar_to_t (Array(typ, i))

      | _ -> Unbound(tvar)
      end
  | SizeTemplatedArray(typ, _) ->
      failwith (
        Printf.sprintf "Error: Ill-formed type: [[ %s ]]" (fmt_type typ)
      )

  | Variant(v_name, v_ctors) ->
      let v_ctors_concretified =
        List.map (_concretify_v_ctor tvar_to_t) v_ctors
      in
      Variant(v_name, v_ctors_concretified)

  | Function(ret_t, args_t_lst) ->
      let ret_t = concretify_unbound_types tvar_to_t ret_t in
      let args_t_lst =
        List.map (concretify_unbound_types tvar_to_t) args_t_lst
      in

      Function(ret_t, args_t_lst)
;;

(* Returns true if the type is entirely resolved to a concrete (instantiable)
type, else false. *)
let rec is_concrete_type ?(verbose=false) typ =
  (* Helper function for determining if all fields in a variant ctor are
  concrete. *)
  let _is_concrete_v_ctor ({fields; _} : v_ctor) =
    let each_field =
      List.map (
        fun {t} -> is_concrete_type t
      ) fields
    in
    let all_fields = List.fold_left (&&) true each_field in
    all_fields
  in

  let _is_concrete_type typ = is_concrete_type ~verbose:verbose typ in

  let res = begin match typ with
  | Undecided  -> false
  | Unbound(_) -> false
  | UnboundType(_, _) -> false
  | UnboundSize(_) -> false
  | SizeTemplatedArray(_, _) -> false

  | U64  | U32 | U16 | U8
  | I64  | I32 | I16 | I8
  | F128 | F64 | F32
  | Bool
  | String
  | Nil -> true

  | Ref(t) -> _is_concrete_type t

  | VarArgSentinel -> true

  | Tuple(tuple_typs) ->
      List.fold_left (&&) true (List.map _is_concrete_type tuple_typs)

  | Array(elem_typ, _) ->
      _is_concrete_type elem_typ

  | Variant(_, v_ctors) ->
      let each_ctor = List.map _is_concrete_v_ctor v_ctors in
      let all_ctors = List.fold_left (&&) true each_ctor in
      all_ctors

  | Function(ret_t, args_t_lst) ->
      let ret_concrete = _is_concrete_type ret_t in
      let args_concrete =
        List.fold_left (&&) true (List.map _is_concrete_type args_t_lst)
      in
      if ret_concrete && args_concrete then true else false

  end in

  let _ = if verbose then
    Printf.printf "is_concrete_type[[ %s ]] == %B\n%!" (fmt_type typ) res
  else
    ()
  in

  res
;;

(* Given two types that are expected to be structurally "symmetric", attempt to
"merge" the types. This means if an element of one type is undecided, but an
element of the other type is concrete, then the resultant type reflects the
concrete side. *)
let rec merge_types lhs_orig_t rhs_orig_t : berk_t =
  (* Helper function for merge two individual variant constructors. *)
  let _merge_v_ctors
    ({name=lhs_name; fields=lhs_fields} as lhs)
    ({name=rhs_name; fields=rhs_fields} as rhs)
  =
    if
      lhs_name <> rhs_name || List.length lhs_fields <> List.length rhs_fields
    then
      failwith (
        Printf.sprintf "Cannot merge variant constructors: [%s] vs [%s]"
          (fmt_v_ctor lhs)
          (fmt_v_ctor rhs)
      )
    else
      let merged_fields =
        List.map2 (
          fun {t=lhs_t} {t=rhs_t} ->
            let merged_field = merge_types lhs_t rhs_t in
            {t=merged_field}
        ) lhs_fields rhs_fields
      in
      {name=lhs_name; fields=merged_fields}
  in

  let rec _merge_types lhs_t rhs_t : berk_t =
    begin match (lhs_t, rhs_t) with
    | (Undecided, Undecided) ->
        Undecided

    (* Sanity check that unbound typevars agree with each other. *)
    | (Unbound(a), Unbound(b)) ->
        begin if a = b then
          Unbound(a)
        else
          failwith (
            Printf.sprintf "Cannot merge types: [%s] vs [%s]"
              (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
          )
        end

    (* We're not in the business of assigning types to unbound typevars. *)
    | (Unbound(_), _)
    | (_, Unbound(_)) ->
        failwith (
          Printf.sprintf
            "Unimplemented: Merging unbound vs bound types: [%s] vs [%s]"
            (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
        )

    (* The critical case: Defer to the concrete side if only one side is
    undecided. *)
    | (Undecided, _) -> rhs_t
    | (_, Undecided) -> lhs_t

    | (UnboundType(lhs_name, lhs_ts), UnboundType(rhs_name, rhs_ts)) ->
        if lhs_name = rhs_name then
          let merged_ts = List.map2 _merge_types lhs_ts rhs_ts in
          UnboundType(lhs_name, merged_ts)
        else
          failwith (
            Printf.sprintf
              "Cannot merge user types: [%s] vs [%s]"
              (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
          )

    | (
        SizeTemplatedArray(lhs_t, Unbound(lhs_tvar)),
        SizeTemplatedArray(rhs_t, Unbound(rhs_tvar))
      ) ->
        if lhs_tvar = rhs_tvar then
          let merged_t = _merge_types lhs_t rhs_t in
          SizeTemplatedArray(merged_t, Unbound(lhs_tvar))
        else
          failwith (
            Printf.sprintf
              "Cannot merge size-templated array types: [%s] vs [%s]"
              (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
          )

    | (UnboundSize(lhs_i), UnboundSize(rhs_i)) ->
        if lhs_i = rhs_i then
          UnboundSize(lhs_i)
        else
          failwith (
            Printf.sprintf
              "Cannot merge unbound sizes: [%s] vs [%s]"
              (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
          )

    (* Base cases. *)
    | (U64, U64)   -> U64
    | (U32, U32)   -> U32
    | (U16, U16)   -> U16
    | (U8,  U8)    -> U8
    | (I64, I64)   -> I64
    | (I32, I32)   -> I32
    | (I16, I16)   -> I16
    | (I8,  I8)    -> I8
    | (F128, F128) -> F128
    | (F64,  F64)  -> F64
    | (F32,  F32)  -> F32
    | (Bool, Bool) -> Bool
    | (Nil,  Nil)  -> Nil
    | (String, String) -> String
    | (VarArgSentinel, VarArgSentinel) -> VarArgSentinel

    | (Tuple(lhs_ts), Tuple(rhs_ts)) ->
        let merged_ts = List.map2 _merge_types lhs_ts rhs_ts in
        Tuple(merged_ts)

    | (Array(lhs_t, lhs_sz), Array(rhs_t, rhs_sz)) ->
        begin if lhs_sz = rhs_sz then
          let merged_t = _merge_types lhs_t rhs_t in
          Array(merged_t, lhs_sz)
        else
          failwith (
            Printf.sprintf
              "Cannot merge types: [%s] vs [%s]"
              (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
          )
        end

    | (Function(lhs_ret_t, lhs_arg_ts), Function(rhs_ret_t, rhs_arg_ts)) ->
        let merged_ret_t = _merge_types lhs_ret_t rhs_ret_t in
        let merged_arg_ts = List.map2 _merge_types lhs_arg_ts rhs_arg_ts in
        Function(merged_ret_t, merged_arg_ts)

    | (
        Variant(lhs_name, lhs_ctors),
        Variant(rhs_name, rhs_ctors)
      ) ->
        begin if
          lhs_name <> rhs_name ||
          List.length lhs_ctors <> List.length rhs_ctors
        then
          failwith (
            Printf.sprintf
              "Cannot merge types: [%s] vs [%s]"
              (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
          )
        else
          let merged_v_ctors = List.map2 _merge_v_ctors lhs_ctors rhs_ctors in
          Variant(lhs_name, merged_v_ctors)
        end

    | (Ref(lhs_refed_t), Ref(rhs_refed_t)) ->
        let merged_t = _merge_types lhs_refed_t rhs_refed_t in
        Ref(merged_t)

    | (
        (
            U64 | U32 | U16 | U8
          | I64 | I32 | I16 | I8
          | F128 | F64 | F32
          | Bool
          | Nil
          | String
          | VarArgSentinel
          | Tuple(_)
          | Array(_, _)
          | Function(_, _)
          | Variant(_, _)
          | Ref(_)
          | UnboundType(_, _)
          | SizeTemplatedArray(_, _)
          | UnboundSize(_)
        ),
        _
      ) ->
        failwith (
          Printf.sprintf
            "Unimplemented: Merging dissimilar types: [%s] vs [%s]"
            (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
        )

    (* | _ ->
        failwith (
          Printf.sprintf
            "Cannot merge types: [%s] vs [%s]"
            (fmt_type lhs_orig_t) (fmt_type rhs_orig_t)
        ) *)
    end
  in

  _merge_types lhs_orig_t rhs_orig_t
;;


(* Given two types, each possibly some degree short of concrete, return a
mapping from the string-type-variables in one to their corresponding concrete
types in the other.

Fails if the given types are not structurally identical, ie, matching aggregrate
structure and component types at least one-way convertible. *)
let map_tvars_to_types
  ?(init_map=StrMap.empty) lhs_typ rhs_typ : berk_t StrMap.t
=
  (* Helper function for extracting the type variables referenced in variant
  constructors. *)
  let rec _map_tvars_to_types_in_v_ctor
    map_so_far {fields=lhs_fields; _} {fields=rhs_fields; _}
  =
    List.fold_left2 (
      fun so_far {t=lhs_t} {t=rhs_t} ->
        _map_tvars_to_types so_far lhs_t rhs_t
    ) map_so_far lhs_fields rhs_fields

  and _map_tvars_to_types map_so_far lhs_typ rhs_typ =
    match lhs_typ, rhs_typ with
    | (Unbound(lhs_tvar), Unbound(rhs_tvar)) ->
        (* Sanity check: These mappings from type-variable to concrete type are
        only sane if there is agreement between the two types on structurally
        _where_ specific type variables could exist. *)
        if lhs_tvar = rhs_tvar then
          map_so_far
        else
          failwith "Types disagree on structural location of tvars"

    | (UnboundType(lhs_name, lhs_ts), UnboundType(rhs_name, rhs_ts)) ->
        if lhs_name = rhs_name then
          List.fold_left2 _map_tvars_to_types map_so_far lhs_ts rhs_ts
        else
          failwith (
            Printf.sprintf
              "Called with non-structurally-identical types:  %s  vs  %s\n"
              (fmt_type lhs_typ)
              (fmt_type rhs_typ)
          )

    | (UnboundSize(lhs_i), UnboundSize(rhs_i)) ->
        if lhs_i = rhs_i then
          map_so_far
        else
          failwith (
            Printf.sprintf
              "Called with non-structurally-identical types:  %s  vs  %s\n"
              (fmt_type lhs_typ)
              (fmt_type rhs_typ)
          )

    | (
        SizeTemplatedArray(lhs_arr_t, lhs_sz_t),
        SizeTemplatedArray(rhs_arr_t, rhs_sz_t)
      ) ->
        let map_so_far = _map_tvars_to_types map_so_far lhs_arr_t rhs_arr_t in
        let map_so_far = _map_tvars_to_types map_so_far lhs_sz_t rhs_sz_t in
        map_so_far

    | (
        (
          SizeTemplatedArray(lhs_arr_t, Unbound(tvar_sz)), Array(rhs_arr_t, sz)
        ) |
        (
          Array(rhs_arr_t, sz), SizeTemplatedArray(lhs_arr_t, Unbound(tvar_sz))
        )
      ) ->
        let map_so_far = _map_tvars_to_types map_so_far lhs_arr_t rhs_arr_t in
        let map_so_far = StrMap.add tvar_sz (UnboundSize(sz)) map_so_far in
        map_so_far

    | (Unbound(_), Undecided)
    | (Undecided, Unbound(_)) ->
        (* Don't record a mapping from a type variable to an undecided type. *)
        map_so_far

    | (Unbound(tvar), concrete_t)
    | (concrete_t, Unbound(tvar)) ->
        (*  The critical pattern: If one type has an unbound type variable and
        the other has a concrete type, then we can add that mapping to our
        collection. *)
        begin if is_concrete_type concrete_t then
          match (StrMap.find_opt tvar map_so_far) with
          | None -> StrMap.add tvar concrete_t map_so_far
          | Some(already_concrete_t) ->
              let common_concrete_t =
                common_type_of_lr concrete_t already_concrete_t
              in
              StrMap.add tvar common_concrete_t map_so_far
        else
          map_so_far
        end

    (* Nothing to be gleaned when we don't know what the type is expected to
    be at all, let alone mapping to a type variable. *)
    | (Undecided, Undecided) ->
        map_so_far

    (* If one side or the other is undecided, then assume that the other side
    is the correct type. Since neither side is unbound, just return the map. *)
    | (Undecided, _)
    | (_, Undecided) ->
        map_so_far

    | ( (U64|U32|U16|U8), (U64|U32|U16|U8))
    | ( (I64|I32|I16|I8), (I64|I32|I16|I8))
    | ((F128|F64|F32),   (F128|F64|F32))
    | (Bool, Bool)
    | (String, String)
    | (Nil, Nil)
    | (VarArgSentinel, VarArgSentinel) ->
        map_so_far

    | (Ref(lhs_t), Ref(rhs_t)) ->
        _map_tvars_to_types map_so_far lhs_t rhs_t

    (* A reference to a type can be transparently treated as the type itself. *)
    | (lhs_t, Ref(rhs_t))
    | (Ref(lhs_t), rhs_t) ->
        _map_tvars_to_types map_so_far lhs_t rhs_t

    | (Function(lhs_ret_t, lhs_args_ts), Function(rhs_ret_t, rhs_args_ts)) ->
        let map_so_far = _map_tvars_to_types map_so_far lhs_ret_t rhs_ret_t in
        List.fold_left2 _map_tvars_to_types map_so_far lhs_args_ts rhs_args_ts

    | (Tuple(lhs_typs), Tuple(rhs_typs)) ->
        List.fold_left2 _map_tvars_to_types map_so_far lhs_typs rhs_typs

    | (Array(lhs_typ, _), Array(rhs_typ, _)) ->
        _map_tvars_to_types map_so_far lhs_typ rhs_typ

    | (Variant(_, lhs_ctors), Variant(_, rhs_ctors)) ->
        List.fold_left2
          _map_tvars_to_types_in_v_ctor map_so_far lhs_ctors rhs_ctors

    | (
        (
          U64 | U32 | U16 | U8 | I64 | I32 | I16 | I8 | F128 | F64 | F32
          | Bool | String | Nil | VarArgSentinel
          | Function(_, _) | Tuple(_) | Array(_, _) | Variant(_, _)
          | UnboundType(_, _) | UnboundSize(_) | SizeTemplatedArray(_, _)
        ),
        _
      ) ->
        let lhs_fmt = fmt_type lhs_typ in
        let rhs_fmt = fmt_type rhs_typ in
        failwith (
          "Called with non-structurally-identical types: [[ " ^
          lhs_fmt ^ " ]] vs [[ " ^ rhs_fmt ^ " ]]"
        )
  in
  _map_tvars_to_types init_map lhs_typ rhs_typ
;;

(* Given a type, return a list of all of the string type variables. *)
let get_tvars typ =
  (* Helper function for extracting the type variables out of an individual
  variant constructor *)
  let rec _get_tvars_in_v_ctor so_far {fields; _} =
    List.fold_left (
      fun so_far {t} ->
        _get_tvars so_far t
    ) so_far fields

  and _get_tvars so_far typ =
    match typ with
    | Unbound(tvar) -> tvar :: so_far

    | UnboundType(_, ts) ->
        List.fold_left _get_tvars so_far ts

    | UnboundSize(i) ->
        failwith (
          Printf.sprintf "Error: Called get_tvars on UnboundSize(%d)" i
        )

    | U64  | U32 | U16 | U8
    | I64  | I32 | I16 | I8
    | F128 | F64 | F32
    | Bool
    | String
    | Nil
    | VarArgSentinel
    | Undecided -> so_far

    | Ref(t) -> _get_tvars so_far t

    | Tuple(tuple_typs) ->
        List.fold_left _get_tvars so_far tuple_typs

    | Array(typ, _) ->
        _get_tvars so_far typ

    | SizeTemplatedArray(typ, size_var) ->
        let so_far = _get_tvars so_far typ in
        let so_far = _get_tvars so_far size_var in
        so_far

    | Variant(_, ctors) ->
        List.fold_left _get_tvars_in_v_ctor so_far ctors

    | Function(ret_t, args_t_lst) ->
        let so_far = _get_tvars so_far ret_t in
        let so_far =
          List.fold_left (
            fun so_far arg_t -> _get_tvars so_far arg_t
          ) so_far args_t_lst
        in
        so_far
  in

  let tvars = _get_tvars [] typ in

  List.sort_uniq compare tvars
;;
