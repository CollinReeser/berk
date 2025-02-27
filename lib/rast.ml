open Ir
open Rast_typing
open Utility

(*
Reduced-complexity AST.

Various elements of the full AST, generated by parse and used for typechecking,
can be rewritten in a more explicit but simpler form. This allows for easier
further analysis once the input is deemed well-formed, and easier generation
of MIR.

This reduced form of the AST deliberately loses certain information, like:

  - Modifiers on variables, like mutability.

as it is assumed that the input AST was already verified as being well-formed.
*)

type rexpr =
  | RValNil
  | RValF128 of string
  | RValF64 of float
  | RValF32 of float
  | RValBool of bool
  | RValStr of string
  | RValInt of rast_t * int

  (* A typical variable. *)
  | RValVar of rast_t * string

  (* A variable that represents a function as a first-class value. *)
  | RValFunc of rast_t * string

  | RValRawArray of rast_t

  | RValCast of rast_t * cast_op * rexpr

  (* Get the address of a value as a pointer. *)
  | RAddressOf of rast_t * rexpr
  (* Dereference an address to get the pointed-to value. *)
  | RDerefAddr of rast_t * rexpr

  | RUnOp of rast_t * un_op * rexpr
  | RBinOp of rast_t * rbin_op * rexpr * rexpr

  | RBlockExpr of rast_t * rstmt * rexpr

  | RExprInvoke of rast_t * rexpr * rexpr list

  | RArrayExpr of rast_t * rexpr list
  | RIndexExpr of rast_t * rexpr * rexpr

  | RTupleIndexExpr of rast_t * int * rexpr
  | RTupleExpr of rast_t * rexpr list

  | RMatchExpr of rast_t * rexpr * (rpattern * rexpr) list

  (* TODO: This can almost certainly be simplified into being in terms of
  a series of init stmts, a bare loop construct (that we could re-use elsewhere
  as well, eg `for-loop` constructs), and an initial check at the beginning
  of the loop for whether or not to break to the end. *)
  | RWhileExpr of rast_t * rstmt list * rexpr * rstmt list

and rpattern =
  (* The LHS type in each case, when relevant, is the type of the source value
  being matched by the pattern. *)

  | RWild of rast_t
  | RVarBind of rast_t * string
  | RPNil
  | RPBool of bool
  | RPIntLit of rast_t * int
  | RPIntFrom of rast_t * int
  | RPIntUntil of rast_t * int
  | RPIntRange of rast_t * int * int
  | RPTuple of rast_t * rpattern list
  (* Reinterpret the matchee as the given type (the second given type), and then
  apply the given pattern. *)
  | RPCastThen of rast_t * rast_t * cast_op * rpattern
  (* Match the matchee against the given pattern, but also bind a variable of
  the given name to the matchee. *)
  | RPatternAs of rast_t * rpattern * string

and rstmt =
  | RDeclStmt of string * rast_t * rexpr

  | RDeclDefaultStmt of (string * rast_t) list

  (*
  The string is the name of the lvalue variable. The first expr is either the
  variable itself, or a series of indexing operations on top of the variable.
  The second (RHS) expression is the value to assign to the lvalue.

  Type is the type of the RHS expression. Note that this may not be exactly
  the type of the actual target variable, but prior typechecking implies it's
  at least implicitly convertible. *)
  | RAssignStmt of string * rast_t * rexpr * rexpr

  | RExprStmt of rexpr

  (* The expression is the value to yield. The int is _which_ yield stmt this
  is in the function. Each yield is uniquely numbered, starting with 0. *)
  | RYieldStmt of rexpr * int

  | RReturnStmt of rexpr

  (* A convenience container for when a stmt needs to be rewritten using
  multiple rstmt. *)
  | RStmts of rstmt list

and r_param = (string * rast_t)

and rfunc_decl_t = {
  rf_name: string;
  rf_params: r_param list;
  rf_ret_t: rast_t;
}

and rfunc_def_t = {
  rf_decl: rfunc_decl_t;
  rf_stmts: rstmt list;
}

and rgenerator_decl_t = {
  rg_name: string;
  rg_params: r_param list;
  rg_yield_t: rast_t;
  rg_ret_t: rast_t;
}

and rgenerator_deg_t = {
  rg_decl: rgenerator_decl_t;
  rg_stmts: rstmt list;
}
;;

let rexpr_type exp : rast_t =
  begin match exp with
  | RValNil -> RNil
  | RValF128(_) -> RF128
  | RValF64(_)  -> RF64
  | RValF32(_)  -> RF32
  | RValBool(_) -> RBool
  | RValStr(_) -> RString
  | RValInt(typ, _) -> typ
  | RValVar(typ, _) -> typ
  | RValFunc(typ, _) -> typ
  | RValRawArray(typ) -> typ
  | RValCast(typ, _, _) -> typ
  | RAddressOf(typ, _) -> typ
  | RDerefAddr(typ, _) -> typ
  | RUnOp(typ, _, _) -> typ
  | RBinOp(typ, _, _, _) -> typ
  | RBlockExpr(typ, _, _) -> typ
  | RWhileExpr(typ, _, _, _) -> typ
  | RExprInvoke(typ, _, _) -> typ
  | RArrayExpr(typ, _) -> typ
  | RIndexExpr(typ, _, _) -> typ
  | RTupleIndexExpr(typ, _, _) -> typ
  | RTupleExpr(typ, _) -> typ
  | RMatchExpr(typ, _, _) -> typ
  end
;;

let rpattern_type patt : rast_t =
  begin match patt with
  | RWild(t) -> t
  | RVarBind(t, _) -> t
  | RPNil -> RNil
  | RPBool(_) -> RBool
  | RPIntLit(t, _) -> t
  | RPIntFrom(t, _) -> t
  | RPIntUntil(t, _) -> t
  | RPIntRange(t, _, _) -> t
  | RPTuple(t, _) -> t
  | RPCastThen(t, _, _, _) -> t
  | RPatternAs(t, _, _) -> t
  end
;;

let rec fmt_rexpr ?(init_ind=false) ?(ind="") ?(print_typ = false) re : string =
  let init_ind = if init_ind then ind else "" in
  let (typ_s, typ_s_rev) =
    if print_typ
    then
      let typ_formatted = rexpr_type re |> fmt_rtype in
      (Printf.sprintf ":%s" typ_formatted, Printf.sprintf "%s:" typ_formatted)
    else ("", "")
  in
  begin match re with
  | RValNil -> Printf.sprintf "%sRValNil()%s" init_ind typ_s

  | RValF128(str) -> Printf.sprintf "%sRValF128(%s)%s" init_ind str typ_s

  | RValF64(value) -> Printf.sprintf "%sRValF64(%f)%s" init_ind value typ_s
  | RValF32(value) -> Printf.sprintf "%sRValF32(%f)%s" init_ind value typ_s

  | RValBool(value) -> Printf.sprintf "%sRValBool(%B)%s" init_ind value typ_s

  | RValStr(str) ->
      (* The string we have here is the raw parsed string, so `\n` is still
      "\n". Nevertheless sprintf will try to helpfully replace the escape code
      with the actual newline, so we escape it deliberately before printing. *)
      Printf.sprintf "%sRValStr(\"%s\")%s" init_ind (String.escaped str) typ_s

  | RValInt(_, value) ->
      Printf.sprintf "%sRValInt(%d)%s" init_ind value typ_s

  | RValVar(_, id) -> Printf.sprintf "%sRValVar(%s)%s" init_ind id typ_s

  | RValFunc(_, func_name) ->
      Printf.sprintf "%sfn<%s%s>" init_ind func_name typ_s

  | RValRawArray(rt) ->
      Printf.sprintf "%s<uninitialized of %s>%s"
        init_ind (fmt_rtype rt) typ_s

  | RValCast(target_rt, op, exp) ->
      let op_fmt = fmt_cast_op op in
      Printf.sprintf "%scast_%s<%s>(%s)%s"
        init_ind
        op_fmt
        (fmt_rtype target_rt)
        (fmt_rexpr ~print_typ:print_typ exp)
        typ_s

  | RAddressOf (_, exp) ->
      Printf.sprintf "%s(addressof %s)%s"
        init_ind
        (fmt_rexpr ~print_typ:print_typ exp)
        typ_s

  | RDerefAddr (_, exp) ->
      Printf.sprintf "%s(derefaddr %s)%s"
        init_ind
        (fmt_rexpr ~print_typ:print_typ exp)
        typ_s

  | RUnOp (_, op, exp) ->
      Printf.sprintf "%s(%s %s)%s"
        init_ind
        (fmt_un_op op)
        (fmt_rexpr ~print_typ:print_typ exp)
        typ_s

  | RBinOp (_, op, lh, rh) ->
      Printf.sprintf "%s(%s %s %s)%s"
        init_ind
        (fmt_rexpr ~print_typ:print_typ lh)
        (fmt_rbin_op op)
        (fmt_rexpr ~print_typ:print_typ rh)
        typ_s

  | RBlockExpr (_, stmt, exp) ->
      let formatted_stmt = fmt_rstmt ~print_typ:print_typ (ind ^ "  ") stmt in
      Printf.sprintf "%sRBlockExpr(%s{\n%s%s\n%s})"
        init_ind
        typ_s_rev
        formatted_stmt
        (fmt_rexpr ~init_ind:true ~ind:(ind ^ "  ") ~print_typ:print_typ exp)
        ind

  | RWhileExpr (_, init_stmts, while_cond, then_stmts) ->
      let formatted_init_stmts = begin
        let (open_brace, close_brace, ind) =
          if List.length init_stmts = 0
          then ("", "", "")
          else ("{\n", Printf.sprintf "%s} in " ind, ind ^ "  ")
        in
        let formatted_stmts =
          List.fold_left (^) "" (
            List.map (fmt_rstmt ~print_typ:print_typ (ind)) init_stmts
          )
        in
        Printf.sprintf "%s%s%s" open_brace formatted_stmts close_brace
      end in

      let formatted_then_stmts =
        List.fold_left (^) "" (
          List.map (fmt_rstmt ~print_typ:print_typ (ind ^ "  ")) then_stmts
        )
      in

      Printf.sprintf "%s%swhile %s%s {\n%s%s}"
        init_ind
        typ_s_rev
        formatted_init_stmts
        (fmt_rexpr ~print_typ:print_typ while_cond)
        formatted_then_stmts
        ind

  | RExprInvoke(_, exp, exprs) ->
      Printf.sprintf "%s%sRExprInvoke(%s(%s))"
        init_ind
        typ_s_rev
        (fmt_rexpr ~print_typ:print_typ exp)
        (fmt_join_rexprs ~ind:ind ~print_typ:print_typ ", " exprs)

  | RArrayExpr(_, exprs) ->
      Printf.sprintf "%s[%s]%s"
        init_ind
        (fmt_join_rexprs ~ind:ind ~print_typ:print_typ ", " exprs)
        typ_s

  | RTupleIndexExpr(_, idx, arr) ->
      Printf.sprintf "%s%s.%d:%s"
        init_ind
        (fmt_rexpr ~print_typ:print_typ arr)
        idx
        typ_s

  | RIndexExpr(_, idx, arr) ->
      Printf.sprintf "%s%s[%s]:%s"
        init_ind
        (fmt_rexpr ~print_typ:print_typ arr)
        (fmt_rexpr ~print_typ:print_typ idx)
        typ_s

  | RTupleExpr(_, exprs) ->
      Printf.sprintf "%s(%s)%s"
        init_ind
        (fmt_join_rexprs ~ind:ind ~print_typ:print_typ ", " exprs)
        typ_s

  | RMatchExpr(_, matched_exp, pattern_exp_pairs) ->
      let pattern_exprs_fmt =
        List.fold_left (^) "" (
          List.map (
            fun (pattern, exp) ->
              let pattern_fmt =
                fmt_rpattern ~print_typ:print_typ ~init_ind:ind pattern
              in
              let exp_fmt =
                fmt_rexpr
                  ~init_ind:false ~ind:(ind ^ "  ") ~print_typ:print_typ exp
              in
              Printf.sprintf "%s -> %s\n" pattern_fmt exp_fmt
          ) pattern_exp_pairs
        )
      in
      Printf.sprintf "%s%smatch %s {\n%s%s}"
        init_ind
        typ_s_rev
        (fmt_rexpr ~print_typ:print_typ matched_exp)
        pattern_exprs_fmt
        ind
  end

and fmt_join_rexprs ?(ind = "") ?(print_typ = false) delim exprs : string =
  match exprs with
  | [] -> ""
  | [x] -> fmt_rexpr ~ind:ind ~print_typ:print_typ x
  | x::xs ->
      (fmt_rexpr ~ind:ind ~print_typ:print_typ x) ^ delim ^
      (fmt_join_rexprs ~ind:ind ~print_typ:print_typ delim xs)

and fmt_rpattern ?(print_typ=false) ?(init_ind="") rpatt =
  let open Printf in

  let _maybe_fmt_rtype rt =
    if print_typ then
      sprintf ":%s" (fmt_rtype rt)
    else
      ""
  in

  let rec _fmt_rpattern rpatt =
    begin match rpatt with
    | RPNil ->
        sprintf "<nil>"
    | RWild(rt) ->
        sprintf "_%s" (_maybe_fmt_rtype rt)
    | RVarBind(rt, var_name) ->
        sprintf "%s%s" var_name (_maybe_fmt_rtype rt)
    | RPBool(b) ->
        sprintf "%b%s" b (_maybe_fmt_rtype RBool)
    | RPIntLit(_, i) ->
        sprintf "(%d)" i
    | RPIntFrom(_, i) ->
        sprintf "(%d..)" i
    | RPIntUntil(_, i) ->
        sprintf "(..%d)" i
    | RPIntRange(_, i, j) ->
        sprintf "(%d..%d)" i j
    | RPTuple(rt, patterns) ->
        let patterns_fmt = List.map _fmt_rpattern patterns in
        sprintf "(%s)%s" (fmt_join_strs ", " patterns_fmt) (_maybe_fmt_rtype rt)
    | RPCastThen(_, target_rt, op, patt) ->
        let target_rt_fmt = fmt_rtype target_rt in
        let op_fmt = fmt_cast_op op in
        let patt_fmt = _fmt_rpattern patt in
        sprintf "<%s_cast<%s>, then match %s>" op_fmt target_rt_fmt patt_fmt
    | RPatternAs(t, pattern, var_name) ->
        sprintf
          "%s%s as %s"
          (_fmt_rpattern pattern)
          (_maybe_fmt_rtype t)
          var_name
    end
  in
  let rpattern_fmt = _fmt_rpattern rpatt in

  sprintf "%s| %s" init_ind rpattern_fmt

and fmt_join_idents_types
  delim (idents_types : (string * rast_t) list) : string =
  match idents_types with
  | [] -> ""

  | [(ident, rt)] ->
      Printf.sprintf "%s: %s" ident (fmt_rtype rt)

  | (ident, rt)::xs ->
      Printf.sprintf "%s: %s%s%s"
        ident
        (fmt_rtype rt)
        delim
        (fmt_join_idents_types delim xs)

and fmt_rstmt ?(print_typ = false) ind rstmt =
  begin match rstmt with
  | RDeclStmt (ident, rt, ex) ->
      let typ_s = fmt_rtype rt |> Printf.sprintf ":%s" in
      Printf.sprintf "%slet %s%s = %s;\n"
        ind
        ident
        typ_s
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RDeclDefaultStmt (idents_ts) ->
      Printf.sprintf "%slet %s;\n"
        ind
        (fmt_join_idents_types ", " idents_ts)

  | RAssignStmt (ident, rt, idxs, ex) ->
      Printf.sprintf "%s%s:%s (%s) = %s;\n"
        ind
        ident
        (fmt_rtype rt)
        (fmt_rexpr idxs)
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RExprStmt (ex) ->
      Printf.sprintf "%s%s;\n"
        ind
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RYieldStmt (ex, i) ->
      Printf.sprintf "%syield %s; # %d\n"
        ind
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)
        i

  | RReturnStmt (ex) ->
      Printf.sprintf "%sreturn %s;\n"
        ind
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RStmts(stmts) ->
      let formatted_stmts = List.map (fmt_rstmt ind) stmts in
      Printf.sprintf "%s"
        (fmt_join_strs "" formatted_stmts)
  end

let rec fmt_rfunc_decl_t
  ?(print_typ = false) ?(extern = false) f_decl : string
=
  let maybe_extern =
    if extern
      then "extern "
      else ""
  in
  Printf.sprintf "%s%s;\n"
    maybe_extern
    (fmt_rfunc_decl_t_signature ~print_typ:print_typ f_decl)

and fmt_rret_t ?(print_typ = false) r_ret_t : string =
  begin match r_ret_t with
  | RNil ->
      if print_typ
      then Printf.sprintf ": %s" (fmt_rtype r_ret_t)
      else ""
  | _ -> Printf.sprintf ": %s" (fmt_rtype r_ret_t)
  end

and fmt_rfunc_decl_t_signature
  ?(print_typ = false) {rf_name; rf_params; rf_ret_t} : string
=
  Printf.sprintf "fn %s(%s)%s"
    rf_name
    (fmt_join_func_params "," rf_params)
    (fmt_rret_t ~print_typ:print_typ rf_ret_t)

and fmt_rgenerator_decl_t_signature
  ?(print_typ = false) {rg_name; rg_params; rg_yield_t; rg_ret_t} : string
=
  let yield_t_s = begin match rg_yield_t with
    | RNil ->
        if print_typ
        then Printf.sprintf " yield %s " (fmt_rtype rg_yield_t)
        else ""
    | _ -> Printf.sprintf " yield %s " (fmt_rtype rg_yield_t)
  end in

  Printf.sprintf "fn %s(%s)%s%s"
    rg_name
    (fmt_join_func_params "," rg_params)
    yield_t_s
    (fmt_rret_t ~print_typ:print_typ rg_ret_t)

and fmt_r_param (p_name, p_type) : string =
  Printf.sprintf "%s: %s"
    p_name
    (fmt_rtype p_type)

and fmt_join_func_params delim params : string =
  match params with
  | [] -> ""
  | [x] -> fmt_r_param x
  | x::xs ->
      Printf.sprintf "%s%s %s"
        (fmt_r_param x)
        delim
        (fmt_join_func_params delim xs)

and fmt_rstmts ?(print_typ = false) r_stmts : string =
  List.fold_left (^) "" (
    List.map (fmt_rstmt ~print_typ:print_typ "  ") r_stmts
  )

and fmt_rfunc_def_t ?(print_typ = false) {rf_decl; rf_stmts;} : string =
  Printf.sprintf "%s {\n%s}\n"
    (fmt_rfunc_decl_t_signature ~print_typ:print_typ rf_decl)
    (fmt_rstmts ~print_typ:print_typ rf_stmts)

and fmt_rgenerator_def_t ?(print_typ = false) {rg_decl; rg_stmts;} : string =
  Printf.sprintf "%s {\n%s}\n"
    (fmt_rgenerator_decl_t_signature ~print_typ:print_typ rg_decl)
    (fmt_rstmts ~print_typ:print_typ rg_stmts)
;;


(* Return true if and only if the given expression does not evaluate to a value
that is pointed to by a variable or the datastructure a variable owns.

ie, returns true if the evaluated value is not reachable from a named variable.
*)
let rec is_true_temporary (e : rexpr) : bool =
  begin match e with
  (* A named variable is not a true temporary by definition. *)
  | RValVar(_, _) -> false

  | RAddressOf(t, e_inner) ->
      let descend_check =
        is_true_temporary e_inner
      in

      (* FIXME: It's unclear what it means to attempt to take the address of a
      value that is not reachable from a named variable. Maybe involved in
      complex referencing and dereferencing of temporaries in a single expr? *)
      begin if descend_check then
        failwith (
          Printf.sprintf
            "is_true_temporary: RAddressOf(%s, %s): Unimplemented."
            (fmt_rtype t)
            (fmt_rexpr e_inner)
        )
      else
        false
      end

  | RDerefAddr(t, e_inner) ->
      let descend_check =
        is_true_temporary e_inner
      in

      (* FIXME: It's unclear what it means to attempt to dereference a value
      that is not reachable from a named variable. Maybe dereferencing a
      reference to a temporary all in one expression? *)
      begin if descend_check then
        failwith (
          Printf.sprintf
            "is_true_temporary: RDerefAddr(%s, %s): Unimplemented."
            (fmt_rtype t)
            (fmt_rexpr e_inner)
        )
      else
        false
      end

  (* Raw basic datatypes are true temporaries. *)
  | RValNil
  | RValBool(_)
  | RValStr(_)
  | RValInt(_, _)
  | RValF128(_)
  | RValF64(_)
  | RValF32(_) -> true

  | RBlockExpr(_, _, e_inner) ->
      let descend_check =
        is_true_temporary e_inner
      in

      begin if descend_check then
        true
      else
        (* FIXME: I am 80% sure that if a block expr returns a basic type,
        then that's sufficient to return true for this function, regardless of
        the arm of the op depending on named variables, because a _new_ value
        is being generated. *)
        failwith (
          "is_true_temporary: Determining temporariness on block expr " ^
          "with expr that depends on named variables is not implemented."
        )
      end

  (* A unary op that yields a basic type is a true temporary, even if the arm
  of the operation makes use of named variables, because a new value is being
  generated by the op itself. *)
  | RUnOp(
      (
          RU64 | RU32 | RU16 | RU8
        | RI64 | RI32 | RI16 | RI8
        | RF128 | RF64 | RF32
        | RBool
      ), _, _
    ) ->
      true

  | RUnOp(t, op, e_inner) ->
      failwith (
        Printf.sprintf
          "is_true_temporary: RUnOp(%s, %s, %s): Unimplemented."
          (fmt_rtype t)
          (fmt_un_op op)
          (fmt_rexpr e_inner)
      )

  (* A binary op that yields a basic type is a true temporary, even if the arms
  of the operation make use of named variables, because a new value is being
  generated by the op itself. *)
  | RBinOp(
      (
          RU64 | RU32 | RU16 | RU8
        | RI64 | RI32 | RI16 | RI8
        | RF128 | RF64 | RF32
        | RBool
      ), _, _, _
    ) ->
      true

  | RBinOp(t, op, e_lhs, e_rhs) ->
      failwith (
        Printf.sprintf
          "is_true_temporary: RBinOp(%s, %s, %s, %s): Unimplemented."
          (fmt_rtype t)
          (fmt_rbin_op op)
          (fmt_rexpr e_lhs)
          (fmt_rexpr e_rhs)
      )

  (* The index value is irrelevant; only the array itself is relevant, as it's
  from there that the value is being pulled. *)
  | RIndexExpr(_, _, e_array) ->
      is_true_temporary e_array

  | RTupleIndexExpr(_, _, e_tuple) ->
      is_true_temporary e_tuple

  (* FIXME: Some of these are probably able to be concretely answered for. *)
  | RValRawArray(_)
  | RValFunc(_, _)
  | RValCast(_, _, _)
  | RArrayExpr(_, _)
  | RTupleExpr(_, _)
  | RExprInvoke(_, _, _)
  | RMatchExpr(_, _, _)
  | RWhileExpr(_, _, _, _) ->
      failwith (
        Printf.sprintf
          "is_true_temporary: %s : Unimplemented"
          (fmt_rexpr e)
      )
  end
;;
