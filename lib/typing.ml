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
  | Tuple of berk_t list
  | Array of berk_t * int
  | Variant of string * (string * berk_t) list
      (*
        Variant("Option", [("Some", Unbound("`a")); (None, Nil)])
      *)
  | VarArgSentinel
  | Unbound of string
  | Undecided

let rec fmt_join_types delim types =
  match types with
  | [] -> ""
  | [x] -> fmt_type x
  | x::xs ->
      let lhs = fmt_type x in
      lhs ^ delim ^ (fmt_join_types delim xs)

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
  | Unbound (type_var) ->
      if pretty_unbound
      then type_var
      else "<?unbound:" ^ type_var ^ "?>"
  | Undecided -> "<?undecided?>"
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


let def_var_qual = {mut = false}

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
    | ((I64|I32|I16|I8), I64) -> Some(I64)
    | ((I32|I16|I8),     I32) -> Some(I32)
    | ((I16|I8),         I16) -> Some(I16)
    | (I8,               I8 ) -> Some(I8)
    | ((U64|U32|U16|U8), U64) -> Some(U64)
    | ((U32|U16|U8),     U32) -> Some(U32)
    | ((U16|U8),         U16) -> Some(U16)
    | (U8,               U8 ) -> Some(U8)
    | ((F128|F64|F32),  F128) -> Some(F128)
    | ((F64|F32),       F64 ) -> Some(F64)
    | (F32,             F32 ) -> Some(F32)
    | (Bool,            Bool) -> Some(Bool)
    | (String,        String) -> Some(String)

    | (Unbound(lhs_typevar), Unbound(rhs_typevar)) ->
        if lhs_typevar = rhs_typevar then
          Some(Unbound(lhs_typevar))
        else
          None

    | (Unbound(_), _) -> Some(rhs)
    | (_, Unbound(_)) -> Some(lhs)

    | (Tuple(lhs_typs), Tuple(rhs_typs)) ->
        let common_tup_typs = List.map2 common_type_of_lr lhs_typs rhs_typs in
        Some(Tuple(common_tup_typs))

    | (Array(lhs_elem_typ, lhs_sz), Array(rhs_elem_typ, rhs_sz)) ->
        if lhs_sz = rhs_sz then
          let common_elem_typ = common_type_of_lr lhs_elem_typ rhs_elem_typ in
          Some(Array(common_elem_typ, lhs_sz))
        else
          None

    | (Variant(lhs_name, lhs_ctor_lst), Variant(rhs_name, rhs_ctor_lst)) ->
        if lhs_name = rhs_name then
          if (List.compare_lengths lhs_ctor_lst rhs_ctor_lst) = 0 then
            let common_ctors = List.map2 (
                fun (lhs_ctor_name, lhs_typ) (rhs_ctor_name, rhs_typ) ->
                  if lhs_ctor_name = rhs_ctor_name then
                    let common_ctor_typ = common_type_of_lr lhs_typ rhs_typ in
                    (lhs_ctor_name, common_ctor_typ)
                  else
                    failwith "Mismatched ctor names"
              ) lhs_ctor_lst rhs_ctor_lst
            in
            Some(Variant(lhs_name, common_ctors))
          else
            None
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
        let lhs_fmt = fmt_type lhs in
        let rhs_fmt = fmt_type rhs in
        failwith (
          "No common type between [[" ^ lhs_fmt ^ "]] [[" ^ rhs_fmt ^ "]]"
        )

and common_type_of_lst lst =
  match lst with
  | [] -> Nil
  | [x] -> x
  | x::xs -> List.fold_left common_type_of_lr x xs
;;

let rec type_convertible_to from_t to_t =
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

  | (Tuple(lhs_types), Tuple(rhs_types)) ->
      if (List.length lhs_types) <> (List.length rhs_types)
        then false
        else begin
          let agreements = List.map2 type_convertible_to lhs_types rhs_types in
          List.fold_left (==) true agreements
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

(* Make concrete the given type, to the extent possible, via the mappings in the
given string-type-variable-to-type mapping. *)
let rec concretify_unbound_types (tvar_to_t : berk_t StrMap.t) typ =
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

  | Tuple(tuple_typs) ->
      let typs_concretified =
        List.map (concretify_unbound_types tvar_to_t) tuple_typs
      in

      Tuple(typs_concretified)

  | Array(arr_typ, sz) ->
      let arr_typ_concretified = concretify_unbound_types tvar_to_t arr_typ in
      Array(arr_typ_concretified, sz)

  | Variant(v_name, v_ctors) ->
      let v_ctors_concretified =
        List.map (
          fun (ctor_name, ctor_typ) ->
            let ctor_typ_concretified =
              concretify_unbound_types tvar_to_t ctor_typ
            in
            (ctor_name, ctor_typ_concretified)
        ) v_ctors
      in

      Variant(v_name, v_ctors_concretified)
;;

(* Returns true if the type is entirely resolved to a concrete (instantiable)
type, else false. *)
let rec is_concrete_type ?(verbose=false) typ =
  let _is_concrete_type typ = is_concrete_type ~verbose:verbose typ in

  let res = begin match typ with
  | Undecided  -> false
  | Unbound(_) -> false

  | U64  | U32 | U16 | U8
  | I64  | I32 | I16 | I8
  | F128 | F64 | F32
  | Bool
  | String
  | Nil -> true

  | VarArgSentinel -> true

  | Tuple(tuple_typs) ->
      List.fold_left (&&) true (List.map _is_concrete_type tuple_typs)

  | Array(elem_typ, _) ->
      _is_concrete_type elem_typ

  | Variant(_, v_ctors) ->
      List.fold_left (&&) true (
        List.map (
          fun (_, typ) -> _is_concrete_type typ
        ) v_ctors
      )
  end in

  let _ = if verbose then
    Printf.printf "is_concrete_type[[ %s ]] == %B\n%!" (fmt_type typ) res
  else
    ()
  in

  res
;;

(* Given two types, each possibly some degree short of concrete, return a
mapping from the string-type-variables in one to their corresponding concrete
types in the other.

Fails if the given types are not structurally identical, ie, matching aggregrate
structure and component types at least one-way convertible. *)
let map_tvars_to_types ?(init_map=StrMap.empty) lhs_typ rhs_typ =
  let rec _map_tvars_to_types map_so_far lhs_typ rhs_typ =
    match lhs_typ, rhs_typ with
    | (Unbound(lhs_tvar), Unbound(rhs_tvar)) ->
        (* Sanity check: These mappings from type-variable to concrete type are
        only sane if there is agreement between the two types on structurally
        _where_ specific type variables could exist. *)
        if lhs_tvar = rhs_tvar then
          map_so_far
        else
          failwith "Types disagree on structural location of tvars"

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

    | ( (U64|U32|U16|U8), (U64|U32|U16|U8))
    | ( (I64|I32|I16|I8), (I64|I32|I16|I8))
    | ((F128|F64|F32),   (F128|F64|F32))
    | (Bool, Bool)
    | (String, String)
    | (Nil, Nil)
    | (VarArgSentinel, VarArgSentinel)
    | (Undecided, Undecided) -> map_so_far

    | (Tuple(lhs_typs), Tuple(rhs_typs)) ->
        List.fold_left2 _map_tvars_to_types map_so_far lhs_typs rhs_typs

    | (Array(lhs_typ, _), Array(rhs_typ, _)) ->
        _map_tvars_to_types map_so_far lhs_typ rhs_typ

    | (Variant(_, lhs_ctors), Variant(_, rhs_ctors)) ->
        List.fold_left2 (
          fun so_far (_, lhs_typ) (_, rhs_typ) ->
            _map_tvars_to_types so_far lhs_typ rhs_typ
        ) map_so_far lhs_ctors rhs_ctors

    | _ ->
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
  let rec _get_tvars so_far typ =
    match typ with
    | Unbound(tvar) -> tvar :: so_far

    | U64  | U32 | U16 | U8
    | I64  | I32 | I16 | I8
    | F128 | F64 | F32
    | Bool
    | String
    | Nil
    | VarArgSentinel
    | Undecided -> so_far

    | Tuple(tuple_typs) ->
        List.fold_left _get_tvars so_far tuple_typs

    | Array(typ, _) ->
        _get_tvars so_far typ

    | Variant(_, ctors) ->
        List.fold_left (
          fun so_far (_, typ) ->
            _get_tvars so_far typ
        ) so_far ctors
  in

  let tvars = _get_tvars [] typ in

  List.sort_uniq compare tvars
;;

(* Get the index of the given ctor name in the given list of variant ctors *)
let get_variant_ctor_tag_index v_ctors ctor_name =
  let rec _get_variant_ctor_tag_index accum v_ctors_tail =
    begin match v_ctors_tail with
    | [] -> failwith ("Failed to find " ^ ctor_name ^ " within variant")
    | (v_ctor_name, _)::xs ->
        if v_ctor_name = ctor_name then
          accum
        else
          _get_variant_ctor_tag_index (accum + 1) xs
    end
  in

  _get_variant_ctor_tag_index 0 v_ctors
;;
