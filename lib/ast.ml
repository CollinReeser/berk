open Typing
open Ir
open Utility


(*
AST for the berk language.
*)

type ident_t = string

and expr =
  | ValNil
  | ValF128 of string
  | ValF64 of float
  | ValF32 of float
  | ValBool of bool
  | ValStr of string
  | ValInt of berk_t * int

  (* These three expression types are really two:
  - ValVar represents a known, declared/named variable.
  - ValFunc represents a known function, containing its literal function name.
  - ValName represents a pre-resolved value of either of the above two.
  *)
  | ValVar of berk_t * ident_t
  | ValFunc of berk_t * ident_t
  | ValName of berk_t * ident_t

  (* This is used during lower-level passes as part of allocation/initialization
  of static arrays and is not generated directly from source. It differs from
  the ByteArray type in that ByteArrays are sized in bytes, but ValRawArrays are
  sized by the given inner type of the top-level array type. They are the way
  for the compiler to represent unitialized generic array data.

  The top-level type is the array type.
  *)
  | ValRawArray of berk_t

  | ValCast of berk_t * cast_op * expr
  | UnOp of berk_t * un_op * expr
  | BinOp of berk_t * bin_op * expr * expr
  (* Sequence of statements followed by an expression, where if the expression
  is None, then the BlockExpr resolves to a nil value. *)
  | BlockExpr of berk_t * stmt list * expr
  (* if expr, then expr, else expr *)
  | IfThenElseExpr of berk_t * expr * expr * expr
  (* while expr, init stmts, cond expr, then stmts *)
  | WhileExpr of berk_t * stmt list * expr * stmt list
  (* A direct call to an in-scope named function. *)
  | FuncCall of berk_t * ident_t * expr list
  (* An indirect invocation of a function resolved from an expression. *)
  | ExprInvoke of berk_t * expr * expr list
  (* An expression representing a statically-sized array. *)
  | ArrayExpr of berk_t * expr list
  (* First expr is index, second is array *)
  | IndexExpr of berk_t * expr * expr
  (* Represents static-integer indexing into a tuple expression, ie:

    ```
    let tup = (1, "hello", true);
    let val1: bool = tup.2;
    let val2: i32 = (21, "example", "index", "tuple", "expr", 21).0;
    ```

    int is index, expr is expected to be type tuple.
  *)
  | TupleIndexExpr of berk_t * int * expr
  | TupleExpr of berk_t * expr list
  (* Top-level variant type, ctor name, ctor expr,  *)
  | VariantCtorExpr of berk_t * string * expr
  (* Match/pattern expression. First expr is value to match on. Remainder are
  pairs of patterns and their resultant expressions *)
  | MatchExpr of berk_t * expr * (pattern * expr) list

and pattern =
  (* ie: _ -> ... *)
  | Wild of berk_t
  (* ie: x -> ... *)
  | VarBind of berk_t * ident_t

  (* Placeholder pattern for, eg, variants with no associated values. Should not
  be generated via input source, but is used internally. *)
  | PNil

  (* ie: true -> ... *)
  | PBool of bool

  (* ie: (x, y, z) -> ...  *)
  | PTuple of berk_t * pattern list
  (* ie: Some(_) -> ... *)
  | Ctor of berk_t * ident_t * pattern
  (*
  (* ie: [_, _, _] -> ... *)
  | DeconArray of berk_t * pattern list
  (* ie: (North | West) -> ... *)
  | Or of berk_t * pattern list
  (* ie: 5 -> ... *)
  | IntLiteral of berk_t * int
  (* ie: 1.23 -> ... *)
  | FloatLiteral of berk_t * string
  *)
  (* ie: <pattern> as x -> ... *)
  | PatternAs of berk_t * pattern * ident_t

and assign_idx_lval =
  (* An index into a tuple. *)
  | ALStaticIndex of int
  (* TODO: Add ALRecordIndex for indexing to access a record field:
  | ALRecordIndex of string *)
  (* An index into a static or dynamic array. *)
  | ALIndex of expr

and stmt =
  | DeclStmt of ident_t * var_qual * berk_t * expr
  (* A `let` stmt that only declares variables, taking the default value for
  each. No expression is associated with this stmt. *)
  | DeclDefStmt of (ident_t * var_qual * berk_t) list
  (* A "deconstructing" stmt that takes a deconstructable expression (like a
  tuple) and deconstructs it into the newly-named variable components.
  eg, `let (a, b, c) = (1, 2, 3);` *)
  (* TODO: This should be normalized a bit with DeclDefStmt and instead have
  the type be per-variable, rather than define a post-deconstruction tuple type.
  *)
  | DeclDeconStmt of (ident_t * var_qual) list * berk_t * expr
  (* Assignment to a LHS lvalue. Could be assignment directly to a named
  variable, where the idx list is empty, or could be arbitrarily-deep indexing
  to the _real_ target of assignment, starting at that named variable. *)
  | AssignStmt of ident_t * assign_idx_lval list * expr
  | AssignDeconStmt of (ident_t * assign_idx_lval list) list * expr
  | ExprStmt of expr
  | ReturnStmt of expr
;;

let expr_type exp =
  match exp with
  | ValNil -> Nil
  | ValF128(_) -> F128
  | ValF64(_)  -> F64
  | ValF32(_)  -> F32
  | ValBool(_) -> Bool
  | ValStr(_) -> String
  | ValInt(typ, _) -> typ
  | ValVar(typ, _) -> typ
  | ValFunc(typ, _) -> typ
  | ValName(typ, _) -> typ
  | ValRawArray(typ) -> typ
  | ValCast(typ, _, _) -> typ
  | UnOp(typ, _, _) -> typ
  | BinOp(typ, _, _, _) -> typ
  | BlockExpr(typ, _, _) -> typ
  | IfThenElseExpr(typ, _, _, _) -> typ
  | WhileExpr(typ, _, _, _) -> typ
  | FuncCall(typ, _, _) -> typ
  | ExprInvoke(typ, _, _) -> typ
  | ArrayExpr(typ, _) -> typ
  | IndexExpr(typ, _, _) -> typ
  | TupleIndexExpr(typ, _, _) -> typ
  | TupleExpr(typ, _) -> typ
  | VariantCtorExpr(typ, _, _) -> typ
  | MatchExpr(typ, _, _) -> typ
;;

let fmt_cast_op op =
  match op with
  | Truncate -> "trunc"
  | Bitwise -> "bitwise"
  | Extend -> "extend"
;;

let fmt_un_op op =
  match op with
  | LNot -> "!"
;;

let fmt_bin_op op =
  match op with
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
  | LOr -> "||"
  | LAnd -> "&&"

let rec fmt_join_exprs ?(ind = "")?(print_typ = false) delim exprs : string =
  match exprs with
  | [] -> ""
  | [x] -> fmt_expr ~ind:ind ~print_typ:print_typ x
  | x::xs ->
      (fmt_expr ~ind:ind ~print_typ:print_typ x) ^ delim ^
      (fmt_join_exprs ~ind:ind ~print_typ:print_typ delim xs)

and fmt_expr ?(init_ind = false) ?(ind = "") ?(print_typ = false) ex : string =
  let init_ind = if init_ind then ind else "" in
  let (typ_s, typ_s_rev) =
    if print_typ
    then
      let typ_formatted = expr_type ex |> fmt_type in
      (Printf.sprintf ":%s" typ_formatted, Printf.sprintf "%s:" typ_formatted)
    else ("", "")
  in
  match ex with
  | ValNil -> Printf.sprintf "%s()%s" init_ind typ_s

  | ValF128(str) -> Printf.sprintf "%s%s%s" init_ind str typ_s

  | ValF64(value) | ValF32(value) ->
      Printf.sprintf "%s%f%s" init_ind value typ_s

  | ValBool(value) -> Printf.sprintf "%s%B%s" init_ind value typ_s

  | ValStr(str) ->
      (* The string we have here is the raw parsed string, so `\n` is still
      "\n". Nevertheless sprintf will try to helpfully replace the escape code
      with the actual newline, so we escape it deliberately before printing. *)
      Printf.sprintf "%s\"%s\"%s" init_ind (String.escaped str) typ_s

  | ValInt(_, value) ->
      Printf.sprintf "%s%d%s" init_ind value typ_s

  | ValVar(_, id) -> Printf.sprintf "%s%s%s" init_ind id typ_s

  | ValFunc(_, func_name) ->
      Printf.sprintf "%sfn<%s%s>" init_ind func_name typ_s

  | ValName(_, name) ->
      Printf.sprintf "%s<unresolved><%s%s>" init_ind name typ_s

  | ValRawArray(t) ->
      Printf.sprintf "%s<uninitialized of %s>%s"
        init_ind (fmt_type t) typ_s

  | ValCast(target_t, op, exp) ->
      let op_fmt = fmt_cast_op op in
      Printf.sprintf "%scast_%s<%s>(%s)%s"
        init_ind
        op_fmt
        (fmt_type target_t)
        (fmt_expr ~print_typ:print_typ exp)
        typ_s

  | UnOp (_, op, exp) ->
      Printf.sprintf "%s(%s %s)%s"
        init_ind
        (fmt_un_op op)
        (fmt_expr ~print_typ:print_typ exp)
        typ_s

  | BinOp (_, op, lh, rh) ->
      Printf.sprintf "%s(%s %s %s)%s"
        init_ind
        (fmt_expr ~print_typ:print_typ lh)
        (fmt_bin_op op)
        (fmt_expr ~print_typ:print_typ rh)
        typ_s

  | BlockExpr (_, stmts, exp) ->
      let formatted_stmts =
        List.fold_left (^) "" (
          List.map (fmt_stmt ~print_typ:print_typ (ind ^ "  ")) stmts
        )
      in
      Printf.sprintf "%s%s{\n%s%s\n%s}"
        init_ind
        typ_s_rev
        formatted_stmts
        (fmt_expr ~init_ind:true ~ind:(ind ^ "  ") ~print_typ:print_typ exp)
        ind
  | IfThenElseExpr (_, if_cond, then_expr, else_expr) ->
      Printf.sprintf "%s%sif (%s) {\n%s\n%s} else {\n%s\n%s}"
        init_ind
        typ_s_rev
        (fmt_expr ~print_typ:print_typ if_cond)
        (
          fmt_expr
            ~init_ind:true ~ind:(ind ^ "  ") ~print_typ:print_typ then_expr
        )
        ind
        (
          fmt_expr
            ~init_ind:true ~ind:(ind ^ "  ") ~print_typ:print_typ else_expr
        )
        ind

  | WhileExpr (_, init_stmts, while_cond, then_stmts) ->
      let formatted_init_stmts = begin
        let (open_brace, close_brace, ind) =
          if List.length init_stmts = 0
          then ("", "", "")
          else if List.length init_stmts = 1
          then ("{ ", " } in ", "")
          else ("{\n", Printf.sprintf "%s} in " ind, ind ^ "  ")
        in
        let formatted_stmts =
          List.fold_left (^) "" (
            List.map (fmt_stmt ~print_typ:print_typ (ind)) init_stmts
          )
        in
        Printf.sprintf "%s%s%s" open_brace formatted_stmts close_brace
      end in

      let formatted_then_stmts =
        List.fold_left (^) "" (
          List.map (fmt_stmt ~print_typ:print_typ (ind ^ "  ")) then_stmts
        )
      in

      Printf.sprintf "%s%swhile %s%s {\n%s%s}"
        init_ind
        typ_s_rev
        formatted_init_stmts
        (fmt_expr ~print_typ:print_typ while_cond)
        formatted_then_stmts
        ind

  | FuncCall(_, id, exprs) ->
      Printf.sprintf "%s%s%s(%s)"
        init_ind
        typ_s_rev
        id
        (fmt_join_exprs ~ind:ind ~print_typ:print_typ ", " exprs)

  | ExprInvoke(_, exp, exprs) ->
      Printf.sprintf "%s%s%s(%s)"
        init_ind
        typ_s_rev
        (fmt_expr ~print_typ:print_typ exp)
        (fmt_join_exprs ~ind:ind ~print_typ:print_typ ", " exprs)

  | ArrayExpr(_, exprs) ->
      Printf.sprintf "%s[%s]%s"
        init_ind
        (fmt_join_exprs ~ind:ind ~print_typ:print_typ ", " exprs)
        typ_s

  | TupleIndexExpr(_, idx, arr) ->
      Printf.sprintf "%s%s.%d:%s"
        init_ind
        (fmt_expr ~print_typ:print_typ arr)
        idx
        typ_s

  | IndexExpr(_, idx, arr) ->
      Printf.sprintf "%s%s[%s]:%s"
        init_ind
        (fmt_expr ~print_typ:print_typ arr)
        (fmt_expr ~print_typ:print_typ idx)
        typ_s

  | TupleExpr(_, exprs) ->
      Printf.sprintf "%s(%s)%s"
        init_ind
        (fmt_join_exprs ~ind:ind ~print_typ:print_typ ", " exprs)
        typ_s

  | VariantCtorExpr(_, ctor_name, expr) ->
      Printf.sprintf "%s%s(%s)%s"
        init_ind
        ctor_name
        (fmt_expr ~print_typ:print_typ expr)
        typ_s

  | MatchExpr(_, matched_exp, pattern_exp_pairs) ->
      let pattern_exprs_fmt =
        List.fold_left (^) "" (
          List.map (
            fun (pattern, exp) ->
              let pattern_fmt =
                fmt_pattern ~print_typ:print_typ (ind) pattern
              in
              let exp_fmt =
                fmt_expr
                  ~init_ind:false ~ind:(ind ^ "  ") ~print_typ:print_typ exp
              in
              Printf.sprintf "%s -> %s\n" pattern_fmt exp_fmt
          ) pattern_exp_pairs
        )
      in
      Printf.sprintf "%s%smatch %s {\n%s%s}"
        init_ind
        typ_s_rev
        (fmt_expr ~print_typ:print_typ matched_exp)
        pattern_exprs_fmt
        ind


and fmt_pattern ?(print_typ=false) init_ind pattern =
  let open Printf in

  let _maybe_fmt_type t =
    if print_typ then
      sprintf ":%s" (fmt_type t)
    else
      ""
  in

  let rec _fmt_pattern pattern =
    begin match pattern with
    | PNil ->
        sprintf "<nil>"
    | Wild(t) ->
        sprintf "_%s" (_maybe_fmt_type t)
    | VarBind(t, var_name) ->
        sprintf "%s%s" var_name (_maybe_fmt_type t)
    | PBool(b) ->
        sprintf "%b%s" b (_maybe_fmt_type Bool)
    | PTuple(t, patterns) ->
        let patterns_fmt = List.map _fmt_pattern patterns in
        sprintf "(%s)%s" (fmt_join_strs ", " patterns_fmt) (_maybe_fmt_type t)
    | Ctor(t, ctor_name, pattern) ->
        sprintf "%s(%s)%s" ctor_name (_fmt_pattern pattern) (_maybe_fmt_type t)
    | PatternAs(t, pattern, var_name) ->
        sprintf "%s%s as %s" (_fmt_pattern pattern) (_maybe_fmt_type t) var_name
    end
  in
  let pattern_fmt = _fmt_pattern pattern in

  sprintf "%s| %s" init_ind pattern_fmt

and pprint_pattern ppf patt =
  Format.fprintf ppf "%s" (fmt_pattern ~print_typ:true "" patt)

and fmt_join_idents_quals delim idents_quals : string =
  match idents_quals with
  | [] -> ""
  | [(ident, qual)] -> Printf.sprintf "%s%s" (fmt_var_qual qual) ident
  | (ident, qual)::xs ->
      Printf.sprintf "%s%s%s%s"
        (fmt_var_qual qual)
        ident
        delim
        (fmt_join_idents_quals delim xs)

and fmt_join_idents_quals_types
  delim (idents_quals_types : (ident_t * var_qual * berk_t) list) : string =
  match idents_quals_types with
  | [] -> ""

  | [(ident, qual, t)] ->
      Printf.sprintf "%s%s: %s" (fmt_var_qual qual) ident (fmt_type t)

  | (ident, qual, t)::xs ->
      Printf.sprintf "%s%s: %s%s%s"
        (fmt_var_qual qual)
        ident
        (fmt_type t)
        delim
        (fmt_join_idents_quals_types delim xs)

and fmt_assign_lval_idxs ?(print_typ = false) lval_idxs =
  let rec _fmt_assign_lval_idxs lval_idxs_rem fmt_so_far =
    begin match lval_idxs_rem with
    | [] -> fmt_so_far
    | idx :: rest ->
        let fmt = fmt_assign_lval_idx ~print_typ:print_typ idx in
        _fmt_assign_lval_idxs rest (fmt_so_far ^ fmt)
    end
  in
  _fmt_assign_lval_idxs lval_idxs ""

and fmt_assign_lval_idx ?(print_typ = false) lval_idx =
  begin match lval_idx with
  | ALStaticIndex(i) ->
      Printf.sprintf ".%d" i

  | ALIndex(exp) ->
      Printf.sprintf "[%s]" (fmt_expr ~print_typ:print_typ exp)
  end

and fmt_stmt ?(print_typ = false) ind stmt =
  match stmt with
  | DeclStmt (ident, qual, btype, ex) ->
      let typ_s = match btype with
        | Undecided -> ""
        | x -> fmt_type x |> Printf.sprintf ": %s"
      in
      Printf.sprintf "%slet %s%s%s = %s;\n"
        ind
        (fmt_var_qual qual)
        ident
        typ_s
        (fmt_expr ~ind:ind ~print_typ:print_typ ex)

  | DeclDefStmt (idents_quals_ts) ->
      Printf.sprintf "%slet %s;\n"
        ind
        (fmt_join_idents_quals_types ", " idents_quals_ts)

  | DeclDeconStmt (idents_quals, btype, ex) ->
      let typ_s = match btype with
        | Undecided -> ""
        | x -> fmt_type x |> Printf.sprintf ": %s"
      in
      Printf.sprintf "%slet (%s)%s = %s;\n"
        ind
        (fmt_join_idents_quals ", " idents_quals)
        typ_s
        (fmt_expr ~ind:ind ~print_typ:print_typ ex)

  | AssignStmt (ident, lval_idxs, ex) ->
      Printf.sprintf "%s%s%s = %s;\n"
        ind
        ident
        (fmt_assign_lval_idxs ~print_typ:print_typ lval_idxs)
        (fmt_expr ~ind:ind ~print_typ:print_typ ex)

  | AssignDeconStmt (ident_lval_idxs, ex) ->
      let lhs_exprs =
        List.map (
          fun (ident, lval_idxs) ->
            Printf.sprintf "%s%s" ident (fmt_assign_lval_idxs lval_idxs)
        ) ident_lval_idxs
      in
      Printf.sprintf "%s(%s) = %s;\n"
        ind
        (fmt_join_strs ", " lhs_exprs)
        (fmt_expr ~ind:ind ~print_typ:print_typ ex)

  | ExprStmt (ex) ->
      Printf.sprintf "%s%s;\n"
        ind
        (fmt_expr ~ind:ind ~print_typ:print_typ ex)

  | ReturnStmt (ex) ->
      Printf.sprintf "%sreturn %s;\n"
        ind
        (fmt_expr ~ind:ind ~print_typ:print_typ ex)
;;

let pprint_expr ppf exp =
  Format.fprintf ppf "%s" (fmt_expr ~print_typ:true exp)
;;


(* Get a "default value" expr for the given type. *)
let rec default_expr_for_t t =
  begin match t with
  | Undecided
  | Unbound(_)
  | UnboundType(_, _)
  | VarArgSentinel
  | Ptr(_)
  | Variant(_, _)
  | ByteArray(_)
  | Function(_, _) ->
      failwith (
        Printf.sprintf
          "Nonsense attempt to generate default expr value for type [%s]"
          (fmt_type t)
      )

  | Nil  -> ValNil

  | Bool -> ValBool(false)

  | U64  -> ValInt(U64, 0)
  | U32  -> ValInt(U32, 0)
  | U16  -> ValInt(U16, 0)
  | U8   -> ValInt(U8,  0)
  | I64  -> ValInt(I64, 0)
  | I32  -> ValInt(I32, 0)
  | I16  -> ValInt(I16, 0)
  | I8   -> ValInt(I8,  0)
  | F32  -> ValF32 (0.0)
  | F64  -> ValF64 (0.0)
  | F128 -> ValF128("0.0")

  | String -> ValStr("")

  | Tuple(tuple_ts) ->
      let default_ts_exprs = List.map default_expr_for_t tuple_ts in
      TupleExpr(t, default_ts_exprs)

  | Array(_, _) ->
      failwith (
        Printf.sprintf (
          "Error: Do not attempt to generate default array. " ^^
          "Array declarations must be initialized: [%s]"
        ) (fmt_type t)
      )
  end
;;


(* Force-apply a top-level type to the given expression, recursively. *)
let rec inject_type_into_expr ?(ind="") injected_t exp =
  let exp_t = expr_type exp in
  let tvars_to_t = map_tvars_to_types injected_t exp_t in

  (* Shadow the old `injected_t`; we now have a possibly-more-concrete type. *)
  let injected_t = concretify_unbound_types tvars_to_t injected_t in

  if not (type_convertible_to exp_t injected_t) then
    failwith (
      "Injection type [[" ^ (fmt_type injected_t) ^
      "]] disagrees with existing " ^ "type [[" ^ (fmt_type exp_t) ^ "]]"
    )
  else
    match (injected_t, exp) with
    | (Undecided, _) -> failwith "Refuse to inject undecided type into expr"

    | (UnboundType(_, _), _) ->
        failwith "Unimplemented: Type injection with unbound types."

    | (Unbound(a), _) ->
        begin match exp_t with
        | Unbound(b) ->
            if a = b then
              exp
            else
              failwith "Refuse to bind typevar to dissimilar typevar"
        | _ ->
            exp
        end

    | (
        Function(inj_ret_t, inj_args_t_lst), (
          ValFunc(Function(has_ret_t, has_args_t_lst), _) |
          ExprInvoke(Function(has_ret_t, has_args_t_lst), _, _)
        )
      ) ->
        let args_match =
          List.fold_left (=) true (
            List.map2 (=) inj_args_t_lst has_args_t_lst
          )
        in

        (* TODO: This is probably overly restrictive, but it's unclear
        how to handle non-matching argument types. *)
        if args_match then
          if has_ret_t = inj_ret_t then
            exp
          else if type_extendable_to has_ret_t inj_ret_t then
            ValCast(inj_ret_t, Extend, exp)
          else
            failwith "Cannot extend func ret type to injected"
        else
          failwith "Cannot inject function type with non-matching args"

    | (_, ValCast(t, op, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCast(injected_t, Extend, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into [%s] type [[ %s ]]"
              (fmt_type injected_t)
              (fmt_cast_op op)
              (fmt_type t)
          )

    | (_, ValVar(t, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCast(injected_t, Extend, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into var type [[ %s ]]"
              (fmt_type injected_t)
              (fmt_type t)
          )

    | (_, FuncCall(t, _, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCast(injected_t, Extend, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into func ret_t [[ %s ]]"
              (fmt_type injected_t)
              (fmt_type t)
          )

    | (_, ExprInvoke(t, _, _)) ->
        if t = injected_t then
          exp
        else if type_extendable_to t injected_t then
          ValCast(injected_t, Extend, exp)
        else
          failwith (
            Printf.sprintf "Cannot inject [[ %s ]] into invoke ret_t [[ %s ]]"
              (fmt_type injected_t)
              (fmt_type t)
          )

    | (_, BlockExpr(_, stmts, exp_res)) ->
        (* We're not smart enough yet to influence the types of any expressions
        within the statements within the block. So, just make sure the trailing
        expression is type-injected. *)
        let exp_res_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") injected_t exp_res
        in

        BlockExpr(injected_t, stmts, exp_res_injected)

    | (_, IndexExpr(_, idx_exp, arr_exp)) ->
        (* We can't use our injection type info to assist with typechecking the
        index expression, but we _can_ use it to assist in typechecking the
        indexed array itself, by assuming the array expression type is expected
        to be an "array of" the target type. *)
        let arr_t = expr_type arr_exp in
        let arr_injection_type = begin match arr_t with
          | Array(_, sz) -> Array(injected_t, sz)
          | _ -> failwith ("Unexpected non-array type: " ^ (fmt_type arr_t))
        end in
        let arr_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") arr_injection_type arr_exp
        in
        IndexExpr(injected_t, idx_exp, arr_exp_injected)

    | (_, TupleIndexExpr(_, idx, tup_exp)) ->
        let tuple_t = expr_type tup_exp in

        (* For the given tuple, assume the element at the given static index
        must be the injection type, yielding an injected overall tuple type.
        *)
        let tuple_injection_type = begin match tuple_t with
          | Tuple(ts) ->
              let new_ts = replace ts idx injected_t in
              Tuple(new_ts)
          | _ -> failwith ("Unexpected non-tuple type: " ^ (fmt_type tuple_t))
        end in

        (* Inject the expected tuple type into the actual tuple exp. *)
        let tup_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") tuple_injection_type tup_exp
        in
        TupleIndexExpr(injected_t, idx, tup_exp_injected)

    | (Array(elem_t, sz), ArrayExpr(_, elem_lst)) ->
        let elem_t_lst = List.init sz (fun _ -> elem_t) in
        let elem_exp_injected_lst =
          List.map2
            (inject_type_into_expr ~ind:(ind ^ "  ")) elem_t_lst elem_lst
        in
        ArrayExpr(injected_t, elem_exp_injected_lst)

    | (Tuple(exp_t_lst), TupleExpr(_, exp_lst)) ->
        let exp_injected_lst =
          List.map2 (inject_type_into_expr ~ind:(ind ^ "  ")) exp_t_lst exp_lst
        in
        TupleExpr(injected_t, exp_injected_lst)

    (* It only makes sense to inject bools into logical negation. *)
    | (Bool as t, UnOp(Bool, LNot, exp)) ->
        let exp_injected = inject_type_into_expr ~ind:(ind ^ "  ") t exp in
        UnOp(t, LNot, exp_injected)

    (* BinOps are an interesting case because they can "switch types"
    arbitrarily deep into a nested bin-op tree, we don't want to eg
    propagate the expectation of a bool due to an eg LessEq op into the
    arithmetic branches, and in general we expect the bottom-up typecheck to
    have correctly inferred everything (or failed eagerly due to type
    mismatch.) *)
    | (_, BinOp(t, bin_op, lhs, rhs)) -> BinOp(t, bin_op, lhs, rhs)

    | (_, IfThenElseExpr(_, cond_exp, then_exp, else_exp)) ->
        (* The injected type into an if-expr should be the common type that
        all branches agree on, but that is still convertible to the injected
        type itself. Put another way, the "most concrete" type to use is the one
        that combines the possibly-incomplete information shared between the
        injected type, the then-branch type, and the else-branch type, but this
        common type must not be a superset of the injected type. *)

        let then_t = expr_type then_exp in
        let else_t = expr_type else_exp in
        let common_then_else_t = common_type_of_lr then_t else_t in
        let common_t = common_type_of_lr injected_t common_then_else_t in

        (* The common type of the then/else/expected types, if it exists, may be
        a superset of the injected type, but the injected type is expected to
        dominate. *)
        let common_t = if type_convertible_to common_t injected_t then
          common_t
        else
          failwith (
            Printf.sprintf
              (
                "then/else branches do not agree on type that is compatible " ^^
                "with injected type: then [[ %s ]], else [[ %s ]], " ^^
                "common then/else [[ %s ]], common all [[ %s ]], " ^^
                "injected [[ %s ]]"
              )
              (fmt_type then_t)
              (fmt_type else_t)
              (fmt_type common_then_else_t)
              (fmt_type common_t)
              (fmt_type injected_t)
          )
        in

        let then_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") common_t then_exp
        in
        let else_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") common_t else_exp
        in

        IfThenElseExpr(common_t, cond_exp, then_exp_injected, else_exp_injected)

    | (_, WhileExpr(_, init_stmts, cond_expr, stmts)) ->
        if injected_t <> Nil then
          failwith "Type of while-expr must be nil."
        else
          WhileExpr(Nil, init_stmts, cond_expr, stmts)

    | (Variant(_, ctors), VariantCtorExpr(_, ctor_name, ctor_exp)) ->
        let (_, ctor_exp_t) = List.find (
            fun (name, _) -> name = ctor_name
          ) ctors
        in
        let ctor_exp_injected =
          inject_type_into_expr ~ind:(ind ^ "  ") ctor_exp_t ctor_exp
        in

        VariantCtorExpr(injected_t, ctor_name, ctor_exp_injected)

    | (_, MatchExpr(_, matched_exp, patt_exp_pairs)) ->
        let patt_exp_pairs_injected =
          List.map (
            fun (patt, exp) ->
              let exp_injected =
                inject_type_into_expr ~ind:(ind ^ "  ") injected_t exp
              in

              (patt, exp_injected)
          ) patt_exp_pairs
        in

        MatchExpr(injected_t, matched_exp, patt_exp_pairs_injected)

    | (U8,  ValInt(U8,  _)) -> exp
    | (U16, ValInt(U16, _)) -> exp
    | (U32, ValInt(U32, _)) -> exp
    | (U64, ValInt(U64, _)) -> exp
    | (U16, ValInt(U8, _)) ->                    ValCast(U16, Extend, exp)
    | (U32, (ValInt(U8, _) | ValInt(U16, _))) -> ValCast(U32, Extend, exp)
    | (U64, (ValInt(U8, _) | ValInt(U16, _) | ValInt(U32, _))) ->
                                                 ValCast(U64, Extend, exp)

    | (I8,  ValInt(I8,  _)) -> exp
    | (I16, ValInt(I16, _)) -> exp
    | (I32, ValInt(I32, _)) -> exp
    | (I64, ValInt(I64, _)) -> exp
    | (I16, ValInt(I8, _)) ->                    ValCast(I16, Extend, exp)
    | (I32, (ValInt(I8, _) | ValInt(I16, _))) -> ValCast(I32, Extend, exp)
    | (I64, (ValInt(I8, _) | ValInt(I16, _) | ValInt(I32, _))) ->
                                                 ValCast(I64, Extend, exp)

    | (F32,  ValF32 (_)) -> exp
    | (F64,  ValF64 (_)) -> exp
    | (F128, ValF128(_)) -> exp

    | (F64,   ValF32(_))              -> ValCast(F64,  Extend, exp)
    | (F128, (ValF32(_) | ValF64(_))) -> ValCast(F128, Extend, exp)

    | (Nil,    ValNil)
    | (Bool,   ValBool(_))
    | (String, ValStr(_)) -> exp

    | ((U64 | U32 | U16 | U8 | I64 | I32 | I16 | I8 | F128 | F64 | F32), _)
    | ((Nil | Bool | String), _)
    | (VarArgSentinel, _) ->
        let _ =
          Printf.printf "%sGiven expr: [[ %s ]]\n"
            ind
            (fmt_expr ~print_typ:true exp)
        in
        failwith (
          Printf.sprintf "Cannot inject type [[ %s ]] into expr [[ %s ]]"
            (fmt_type injected_t)
            (fmt_expr ~print_typ:true exp)
        )

    | (Tuple(_), _)
    | (_, TupleExpr(_, _))
    | (Array(_, _), _)
    | (_, ArrayExpr(_, _)) ->
        failwith (
          Printf.sprintf
            "Cannot inject incompatible aggregate types: [[ %s ]] into [[ %s ]] given [[ %s ]]"
            (fmt_type injected_t)
            (fmt_type exp_t)
            (fmt_expr exp)
        )

    | (Variant(_, _), _)
    | (_, VariantCtorExpr(_, _, _)) ->
        failwith (
          "Unexpectedly encountered mismatch in variant typing: " ^
          "[[ " ^ (fmt_type injected_t) ^ " ]]"
        )

    | (Function(_, _), _) ->
        failwith (
          Printf.sprintf
            "Cannot inject function type into non-func value: [[ %s ]]"
            (fmt_expr ~print_typ:true exp)
        )

    | (Ptr(_), _) -> failwith "Unimplemented"
    | (ByteArray(_), _) -> failwith "Unimplemented"
;;

type v_ctor = (string * berk_t)

and variant_decl_t = {
  v_name: string;
  v_ctors: v_ctor list;
  v_typ_vars: string list;
}

type f_param = (ident_t * var_qual * berk_t)

and func_decl_t = {
  f_name: string;
  f_params: f_param list;
  f_ret_t: berk_t;
}

and func_def_t = {
  f_decl: func_decl_t;
  f_stmts: stmt list;
}

type module_decl =
  | FuncExternDecl of func_decl_t
  | FuncDef of func_def_t
  | VariantDecl of variant_decl_t

let rec fmt_func_decl ?(print_typ = false) ?(extern = false) f_decl : string =
  let maybe_extern =
    if extern
      then "extern "
      else ""
  in
  Printf.sprintf "%s%s;\n"
    maybe_extern
    (fmt_func_signature ~print_typ:print_typ f_decl)

and fmt_func_signature
  ?(print_typ = false) {f_name; f_params; f_ret_t;} : string
=
  let ret_t_s = begin match f_ret_t with
    | Nil
    | Undecided ->
        if print_typ
        then Printf.sprintf ": %s" (fmt_type f_ret_t)
        else ""
    | _ -> Printf.sprintf ": %s" (fmt_type f_ret_t)
  end in

  Printf.sprintf "fn %s(%s)%s"
    f_name
    (fmt_join_func_params "," f_params)
    ret_t_s

and fmt_func_param (p_name, p_qual, p_type) : string =
  Printf.sprintf "%s%s: %s"
    (fmt_var_qual p_qual)
    p_name
    (fmt_type p_type)

and fmt_join_func_params delim params : string =
  match params with
  | [] -> ""
  | [x] -> fmt_func_param x
  | x::xs ->
      Printf.sprintf "%s%s %s"
        (fmt_func_param x)
        delim
        (fmt_join_func_params delim xs)

let fmt_func_ast ?(print_typ = false) {f_decl; f_stmts;} : string =
  let formatted_stmts =
    List.fold_left (^) "" (
      List.map (fmt_stmt ~print_typ:print_typ "  ") f_stmts
    )
  in

  Printf.sprintf "%s {\n%s}\n"
    (fmt_func_signature ~print_typ:print_typ f_decl)
    formatted_stmts
;;

let fmt_variant_ctor ?(pretty_unbound=false) (ctor_name, ctor_typ) : string =
  let fmt_typ = begin
    match ctor_typ with
    | Nil -> ""
    | _ ->
        Printf.sprintf " of %s"
          (fmt_type ~pretty_unbound:pretty_unbound ctor_typ)
  end in

  Printf.sprintf " | %s%s\n" ctor_name fmt_typ
;;

let fmt_variant_decl
  ?(pretty_unbound=false) {v_name; v_ctors; v_typ_vars} : string
=
  let formatted_type_vars = begin
    match v_typ_vars with
    | [] -> ""
    | xs ->
        Printf.sprintf "<%s>"
          (fmt_join_strs ", " xs)
  end in

  let formatted_ctors =
    List.fold_left (^) "" (
      List.map (fmt_variant_ctor ~pretty_unbound:pretty_unbound) v_ctors
    )
  in

  Printf.sprintf "%s %s {\n%s}\n"
    v_name
    formatted_type_vars
    formatted_ctors
;;

let fmt_mod_decl
  ?(pretty_unbound=false) ?(print_typ = false) mod_decl : string
=
  begin match mod_decl with
  | FuncExternDecl(f_decl) ->
      Printf.sprintf "%s"(fmt_func_decl ~print_typ:true ~extern:true f_decl)

  | FuncDef(f_ast) ->
      Printf.sprintf "%s"(fmt_func_ast ~print_typ:print_typ f_ast)

  | VariantDecl(v_ast) ->
      Printf.sprintf "%s"(fmt_variant_decl ~pretty_unbound:pretty_unbound v_ast)
  end

(* Return the pair of all the non-variadic function parameter types, and whether
the parameter list ends with a variadic-args sentinel. Fails if ill-formed. *)
let rec get_static_f_params f_params =
  begin match f_params with
  | [] -> ([], false)
  | [(_, _, VarArgSentinel)] -> ([], true)
  | (_, _, VarArgSentinel)::_ ->
      failwith "Variadic arguments may exist only once, at end of param list"
  | (_, _, x)::xs ->
      let (rest, is_vararg) = get_static_f_params xs in
      (x::rest, is_vararg)
  end

(* Rewrites variable names in the function so that all are unique, ie, none
appear to shadow each other. *)
let rewrite_to_unique_varnames {f_decl={f_name; f_params; f_ret_t}; f_stmts} =
  (* Yields a uniquified variable name, and the updated mapping containing a
  binding from the original varname to its new uniquified name. *)
  let get_unique_varname varname unique_varnames =
    let _get_unique_varname varname uniquified =
      (* If the given variable name is already known, then yield a new name
      that is the old name but uniquified.

      FIXME: This doesn't quite work, if the "uniquified" name is also already
      in the known set. *)
      if StrMap.mem varname unique_varnames then
        let uniquified = (StrMap.find varname unique_varnames) ^ "a" in
        let unique_varnames = StrMap.add varname uniquified unique_varnames in
        (uniquified, unique_varnames)
      (* If this variable name is not yet known, simply add it to the known
      set and return it. *)
      else
        let unique_varnames = StrMap.add varname uniquified unique_varnames in
        (uniquified, unique_varnames)
    in
    _get_unique_varname varname varname
  in

  (* Seed the unique_varnames map with the function parameters. *)
  let unique_varnames =
    List.fold_left (
      fun unique_varnames (param_name, _, _) ->
        let (_, unique_varnames) =
          get_unique_varname param_name unique_varnames
        in
        unique_varnames
    ) StrMap.empty f_params
  in

  let rec _rewrite_stmt stmt unique_varnames =
    begin match stmt with
    | DeclStmt(varname, varqual, t, exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        let (uniq_varname, unique_varnames) =
          get_unique_varname varname unique_varnames
        in
        (DeclStmt(uniq_varname, varqual, t, exp_rewritten), unique_varnames)

    | DeclDefStmt(idents_quals_ts) ->
        let (uniq_idents_quals_ts_rev, unique_varnames) =
          List.fold_left (
            fun
              (new_varname_varquals_rev, unique_varnames)
              (varname, varqual, t)
            ->
              let (uniq_varname, unique_varnames) =
                get_unique_varname varname unique_varnames
              in
              (
                (uniq_varname, varqual, t)::new_varname_varquals_rev,
                unique_varnames
              )
          ) ([], unique_varnames) idents_quals_ts
        in
        let uniq_idents_quals_ts = List.rev uniq_idents_quals_ts_rev in

        (DeclDefStmt(uniq_idents_quals_ts), unique_varnames)

    | DeclDeconStmt(varname_varquals, t, exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        let (uniq_varname_varquals_rev, unique_varnames) =
          List.fold_left (
            fun
              (new_varname_varquals_rev, unique_varnames)
              (varname, varqual)
            ->
              let (uniq_varname, unique_varnames) =
                get_unique_varname varname unique_varnames
              in
              ((uniq_varname, varqual)::new_varname_varquals_rev, unique_varnames)
          ) ([], unique_varnames) varname_varquals
        in
        let uniq_varname_varquals = List.rev uniq_varname_varquals_rev in
        (
          DeclDeconStmt(uniq_varname_varquals, t, exp_rewritten),
          unique_varnames
        )

    | AssignStmt(varname, lval_idxs, exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        (AssignStmt(varname, lval_idxs, exp_rewritten), unique_varnames)

    | AssignDeconStmt(varnames, exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        (AssignDeconStmt(varnames, exp_rewritten), unique_varnames)

    | ExprStmt(exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        (ExprStmt(exp_rewritten), unique_varnames)

    | ReturnStmt(exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        (ReturnStmt(exp_rewritten), unique_varnames)
    end

  and _rewrite_exp exp unique_varnames =
    begin match exp with
    | ValF32(_) | ValF64(_) | ValF128(_)
    | ValBool(_)
    | ValStr(_)
    | ValNil
    | ValInt(_, _)
    | ValFunc(_, _) ->
        exp

    | ExprInvoke(t, exp, exps) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        let exps_rewritten =
          List.map (
            fun exp -> _rewrite_exp exp unique_varnames
          ) exps
        in
        ExprInvoke(t, exp_rewritten, exps_rewritten)

    | ValVar(t, varname) ->
        let uniq_varname = StrMap.find varname unique_varnames in
        ValVar(t, uniq_varname)

    | ValName(_, _) ->
        failwith "Cannot rewrite ValName(): Should have been resolved"

    | ValRawArray(_) ->
        failwith "Cannot rewrite ValRawArray(): Should not be present"

    | ValCast(t, op, exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        ValCast(t, op, exp_rewritten)

    | TupleIndexExpr(t, idx, tup_exp) ->
        let tup_exp_rewritten = _rewrite_exp tup_exp unique_varnames in
        TupleIndexExpr(t, idx, tup_exp_rewritten)

    | IndexExpr(t, idx_exp, arr_exp) ->
        let idx_exp_rewritten = _rewrite_exp idx_exp unique_varnames in
        let arr_exp_rewritten = _rewrite_exp arr_exp unique_varnames in
        IndexExpr(t, idx_exp_rewritten, arr_exp_rewritten)

    | UnOp(t, op, exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        UnOp(t, op, exp_rewritten)

    | BinOp(t, op, exp_lhs, exp_rhs) ->
        let exp_lhs_rewritten = _rewrite_exp exp_lhs unique_varnames in
        let exp_rhs_rewritten = _rewrite_exp exp_rhs unique_varnames in
        BinOp(t, op, exp_lhs_rewritten, exp_rhs_rewritten)

    | IfThenElseExpr(t, exp_cond, exp_then, exp_else) ->
        let exp_cond_rewritten = _rewrite_exp exp_cond unique_varnames in
        let exp_then_rewritten = _rewrite_exp exp_then unique_varnames in
        let exp_else_rewritten = _rewrite_exp exp_else unique_varnames in
        IfThenElseExpr(
          t, exp_cond_rewritten, exp_then_rewritten, exp_else_rewritten
        )

    | TupleExpr(t, exps) ->
        let exps_rewritten =
          List.map (
            fun exp -> _rewrite_exp exp unique_varnames
          ) exps
        in
        TupleExpr(t, exps_rewritten)

    | ArrayExpr(t, exps) ->
        let exps_rewritten =
          List.map (
            fun exp -> _rewrite_exp exp unique_varnames
          ) exps
        in
        ArrayExpr(t, exps_rewritten)

    | FuncCall(t, func_name, exps) ->
        let exps_rewritten =
          List.map (
            fun exp -> _rewrite_exp exp unique_varnames
          ) exps
        in
        FuncCall(t, func_name, exps_rewritten)

    | BlockExpr(t, stmts, exp) ->
        let (stmts_rewritten_rev, unique_varnames) =
          List.fold_left (
            fun (stmts_rewritten_rev, unique_varnames) stmt ->
              let (rewritten_stmt, unique_varnames) =
                _rewrite_stmt stmt unique_varnames
              in
              (rewritten_stmt :: stmts_rewritten_rev, unique_varnames)
          ) ([], unique_varnames) stmts
        in
        let stmts_rewritten = List.rev stmts_rewritten_rev in
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        BlockExpr(t, stmts_rewritten, exp_rewritten)

    | VariantCtorExpr(t, ctor_name, exp) ->
        let exp_rewritten = _rewrite_exp exp unique_varnames in
        VariantCtorExpr(t, ctor_name, exp_rewritten)

    | MatchExpr(t, exp_match, patt_exp_pairs) ->
        let exp_match_rewritten = _rewrite_exp exp_match unique_varnames in

        let (patt_exp_pairs_rewritten_rev, _) =
          List.fold_left (
            fun (patt_exp_pairs_rewritten_rev, unique_varnames) (patt, exp) ->
              let (patt_rewritten, unique_varnames) =
                _rewrite_patt_exp patt unique_varnames
              in
              let exp_rewritten = _rewrite_exp exp unique_varnames in
              (
                (patt_rewritten, exp_rewritten)::patt_exp_pairs_rewritten_rev,
                unique_varnames
              )
          ) ([], unique_varnames) patt_exp_pairs
        in
        let patt_exp_pairs_rewritten =
          List.rev patt_exp_pairs_rewritten_rev
        in
        MatchExpr(t, exp_match_rewritten, patt_exp_pairs_rewritten)

    | WhileExpr(t, init_stmts, exp_cond, then_stmts) ->
        let rewrite_stmts varnames stmts =
          List.fold_left (
            fun (stmts_rewritten_rev, varnames) stmt ->
              let (rewritten_stmt, varnames) =
                _rewrite_stmt stmt varnames
              in
              (rewritten_stmt :: stmts_rewritten_rev, varnames)
          ) ([], varnames) stmts
        in

        let (init_stmts_rewritten_rev, unique_varnames) =
          rewrite_stmts unique_varnames init_stmts
        in
        let (then_stmts_rewritten_rev, unique_varnames) =
          rewrite_stmts unique_varnames then_stmts
        in

        let init_stmts_rewritten = List.rev init_stmts_rewritten_rev in
        let then_stmts_rewritten = List.rev then_stmts_rewritten_rev in
        let exp_cond_rewritten = _rewrite_exp exp_cond unique_varnames in
        WhileExpr(
          t, init_stmts_rewritten, exp_cond_rewritten, then_stmts_rewritten
        )

    end

  and _rewrite_patt_exp patt unique_varnames =
    begin match patt with
    | PNil
    | Wild(_)
    | PBool(_) ->
        (patt, unique_varnames)

    | VarBind(t, varname) ->
        let (uniq_varname, unique_varnames) =
          get_unique_varname varname unique_varnames
        in
        (VarBind(t, uniq_varname), unique_varnames)

    | PTuple(t, patts) ->
        let (patts_rewritten_rev, unique_varnames) =
          List.fold_left (
            fun (patts_rewritten_rev, unique_varnames) patt ->
              let (patt_rewritten, unique_varnames) =
                _rewrite_patt_exp patt unique_varnames
              in
              (patt_rewritten :: patts_rewritten_rev, unique_varnames)
          ) ([], unique_varnames) patts
        in
        let patts_rewritten = List.rev patts_rewritten_rev in
        (PTuple(t, patts_rewritten), unique_varnames)

    | Ctor(t, ctor_name, patt) ->
        let (patt_rewritten, unique_varnames) =
          _rewrite_patt_exp patt unique_varnames
        in
        (Ctor(t, ctor_name, patt_rewritten), unique_varnames)

    | PatternAs(t, patt, varname) ->
        let (uniq_varname, unique_varnames) =
          get_unique_varname varname unique_varnames
        in
        let (patt_rewritten, unique_varnames) =
          _rewrite_patt_exp patt unique_varnames
        in
        (PatternAs(t, patt_rewritten, uniq_varname), unique_varnames)
    end
  in

  let (stmts_rewritten_rev, _) =
    List.fold_left (
      fun (stmts_rewritten_rev, unique_varnames) stmt ->
        let (stmt_rewritten, unique_varnames) =
          _rewrite_stmt stmt unique_varnames
        in
        (stmt_rewritten :: stmts_rewritten_rev, unique_varnames)
    ) ([], unique_varnames) f_stmts
  in

  let rewritten_stmts = List.rev stmts_rewritten_rev in

  {f_decl={f_name; f_params; f_ret_t}; f_stmts=rewritten_stmts}
