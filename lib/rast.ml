open Ast
open Typing
open Ir
open Utility

(*
Reduced-complexity AST.

Various elements of the full AST, generated by parse and used for typechecking,
can be rewritten in a more explicit but simpler form. This allows for easier
further analysis once the input is deemed well-formed, and easier generation
of MIR.

This reduced form of the AST deliberately loses certain information, like:

  - Limited scoping of variables.
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
  | RValInt of berk_t * int

  | RValVar of berk_t * string
  | RValFunc of berk_t * string

  | RValRawArray of berk_t

  | RValCast of berk_t * cast_op * rexpr
  | RUnOp of berk_t * un_op * rexpr
  | RBinOp of berk_t * bin_op * rexpr * rexpr

  | RBlockExpr of berk_t * rstmt * rexpr

  | RExprInvoke of berk_t * rexpr * rexpr list

  | RArrayExpr of berk_t * rexpr list
  | RIndexExpr of berk_t * rexpr * rexpr

  | RTupleIndexExpr of berk_t * int * rexpr
  | RTupleExpr of berk_t * rexpr list

  | RVariantCtorExpr of berk_t * string * rexpr list

  | RMatchExpr of berk_t * rexpr * (rpattern * rexpr) list

  (* TODO: This can almost certainly be simplified into being in terms of
  a series of init stmts, a bare loop construct (that we could re-use elsewhere
  as well, eg `for-loop` constructs), and an initial check at the beginning
  of the loop for whether or not to break to the end. *)
  | RWhileExpr of berk_t * rstmt list * rexpr * rstmt list

and rpattern =
  | RWild of berk_t
  | RVarBind of berk_t * string
  | RPNil
  | RPBool of bool
  | RPIntLit of berk_t * int
  | RPIntFrom of berk_t * int
  | RPIntUntil of berk_t * int
  | RPIntRange of berk_t * int * int
  | RPTuple of berk_t * rpattern list
  | RCtor of berk_t * string * rpattern list
  | RPatternAs of berk_t * rpattern * string

and rassign_idx_lval =
  (* An index into a tuple. The type is of the result, after the index. *)
  | RALStaticIndex of berk_t * int
  (* An index into a static or dynamic array. The type is of the result, after
  the index.*)
  | RALIndex of berk_t * rexpr

and rstmt =
  | RDeclStmt of string * berk_t * rexpr

  | RDeclDefStmt of (string * berk_t) list

  (* Type is the type of the RHS expression. Note that this may not be exactly
  the type of the actual target variable, but prior typechecking implies it's
  at least implicitly convertible. *)
  | RAssignStmt of string * berk_t * rassign_idx_lval list * rexpr

  | RExprStmt of rexpr
  | RReturnStmt of rexpr

  (* A convenience container for when a stmt needs to be rewritten using
  multiple rstmt. *)
  | RStmts of rstmt list

and rf_param = (ident_t * berk_t)

and rfunc_decl_t = {
  rf_name: string;
  rf_params: rf_param list;
  rf_ret_t: berk_t;
}

and rfunc_def_t = {
  rf_decl: rfunc_decl_t;
  rf_stmts: rstmt list;
}
;;

let rexpr_type exp =
  begin match exp with
  | RValNil -> Nil
  | RValF128(_) -> F128
  | RValF64(_)  -> F64
  | RValF32(_)  -> F32
  | RValBool(_) -> Bool
  | RValStr(_) -> String
  | RValInt(typ, _) -> typ
  | RValVar(typ, _) -> typ
  | RValFunc(typ, _) -> typ
  | RValRawArray(typ) -> typ
  | RValCast(typ, _, _) -> typ
  | RUnOp(typ, _, _) -> typ
  | RBinOp(typ, _, _, _) -> typ
  | RBlockExpr(typ, _, _) -> typ
  | RWhileExpr(typ, _, _, _) -> typ
  | RExprInvoke(typ, _, _) -> typ
  | RArrayExpr(typ, _) -> typ
  | RIndexExpr(typ, _, _) -> typ
  | RTupleIndexExpr(typ, _, _) -> typ
  | RTupleExpr(typ, _) -> typ
  | RVariantCtorExpr(typ, _, _) -> typ
  | RMatchExpr(typ, _, _) -> typ
  end
;;

let rec expr_to_rexpr expr : rexpr =
  begin match expr with
  | ValName(_, name) ->
      failwith (
        Printf.sprintf
          "Error: Cannot convert ValName(%s) to rexpr: must be pre-resolved"
          name
      )

  | ValNil -> RValNil
  | ValF128(s) -> RValF128(s)
  | ValF64(f) -> RValF64(f)
  | ValF32(f) -> RValF32(f)
  | ValBool(b) -> RValBool(b)
  | ValStr(s) -> RValStr(s)
  | ValInt(t, i) -> RValInt(t, i)

  | ValVar(t, name) -> RValVar(t, name)
  | ValFunc(t, name) -> RValFunc(t, name)

  | ValRawArray(t) -> RValRawArray(t)

  | ValCast(t, op, e) ->
      let re = expr_to_rexpr e in
      RValCast(t, op, re)

  | UnOp(t, op, e) ->
      let re = expr_to_rexpr e in
      RUnOp(t, op, re)

  | BinOp(t, op, e_lhs, e_rhs) ->
      let re_lhs = expr_to_rexpr e_lhs in
      let re_rhs = expr_to_rexpr e_rhs in
      RBinOp(t, op, re_lhs, re_rhs)

  | BlockExpr(t, stmts, e) ->
      let re = expr_to_rexpr e in
      let rstmts = List.map stmt_to_rstmt stmts in
      let wrapped_rstmts = RStmts(rstmts) in
      RBlockExpr(t, wrapped_rstmts, re)

  | ExprInvoke(t, e_func, e_args) ->
      let re_func = expr_to_rexpr e_func in
      let re_args = List.map expr_to_rexpr e_args in
      RExprInvoke(t, re_func, re_args)

  | FuncCall(t, name, e_args) ->
      let args_ts = List.map expr_type e_args in
      let func_t = Function(t, args_ts) in
      let re_func = RValFunc(func_t, name) in

      let re_args = List.map expr_to_rexpr e_args in

      RExprInvoke(t, re_func, re_args)

  | UfcsCall(t, e_arg_first, name, e_args_rest) ->
      let e_args_all = e_arg_first :: e_args_rest in

      let args_ts = List.map expr_type e_args_all in
      let func_t = Function(t, args_ts) in
      let re_func = RValFunc(func_t, name) in

      let re_args = List.map expr_to_rexpr e_args_all in

      RExprInvoke(t, re_func, re_args)

  | ArrayExpr(t, e_elems) ->
      let re_elems = List.map expr_to_rexpr e_elems in
      RArrayExpr(t, re_elems)

  | IndexExpr(t, e_idx, e_arr) ->
      let re_idx = expr_to_rexpr e_idx in
      let re_arr = expr_to_rexpr e_arr in
      RIndexExpr(t, re_idx, re_arr)

  | TupleIndexExpr(t, i, e_tuple) ->
      let re_tuple = expr_to_rexpr e_tuple in
      RTupleIndexExpr(t, i, re_tuple)

  | TupleExpr(t, e_elems) ->
      let re_elems = List.map expr_to_rexpr e_elems in
      RTupleExpr(t, re_elems)

  (* TODO: Could we turn this into an explicit struct of certain elements to
  make reasoning about RAST -> MIR generation and MIR -> LLVM generation easier?
  *)
  | VariantCtorExpr(t, name_ctor, e_fields) ->
      let re_fields = List.map expr_to_rexpr e_fields in
      RVariantCtorExpr(t, name_ctor, re_fields)

  | IfThenElseExpr(t, e_cond, e_then, e_else) ->
      let re_cond = expr_to_rexpr e_cond in
      let re_then = expr_to_rexpr e_then in
      let re_else = expr_to_rexpr e_else in
      RMatchExpr(t, re_cond, [(RPBool(true), re_then); (RWild(Bool), re_else)])

  | WhileExpr(t, stmts_init, e_cond, stmts_block) ->
      let rstmts_init = List.map stmt_to_rstmt stmts_init in
      let rstmts_block = List.map stmt_to_rstmt stmts_block in
      let re_cond = expr_to_rexpr e_cond in
      RWhileExpr(t, rstmts_init, re_cond, rstmts_block)

  | MatchExpr(t, e_cond, patts_to_exprs) ->
      let re_cond = expr_to_rexpr e_cond in
      let rpatts_to_rexprs =
        List.map (
          fun (patt, expr) ->
            let rpatt = pattern_to_rpattern patt in
            let rexpr = expr_to_rexpr expr in
            (rpatt, rexpr)
        ) patts_to_exprs
      in
      RMatchExpr(t, re_cond, rpatts_to_rexprs)
  end

and pattern_to_rpattern patt : rpattern =
  begin match patt with
  | PNil -> RPNil

  | Wild(t) -> RWild(t)

  | VarBind(t, name) -> RVarBind(t, name)

  | PBool(b) -> RPBool(b)

  | PInt(t, IRangeLiteral(i)) -> RPIntLit(t, i)

  | PInt(t, IRangeAllFrom(i)) -> RPIntFrom(t, i)

  | PInt(t, IRangeAllUntil(i)) -> RPIntUntil(t, i)

  | PInt(t, IRangeFromUntil(i, j)) -> RPIntRange(t, i, j)

  | PInt(_, IRangeAll) -> failwith "IRangeAll should not survive typecheck"

  | PTuple(t, patts) ->
      let rpatts = List.map pattern_to_rpattern patts in
      RPTuple(t, rpatts)

  | Ctor(t, name_ctor, patts) ->
      let rpatts = List.map pattern_to_rpattern patts in
      RCtor(t, name_ctor, rpatts)

  | PatternAs(t, patt, name) ->
      let rpatt = pattern_to_rpattern patt in
      RPatternAs(t, rpatt, name)
  end

and assign_idx_lval_to_rassign_idx_lval idx : rassign_idx_lval =
  begin match idx with
  | ALStaticIndex(indexed_t, i) ->
      RALStaticIndex(indexed_t, i)

  | ALIndex(indexed_t, e) ->
      let re = expr_to_rexpr e in
      RALIndex(indexed_t, re)
  end

and stmt_to_rstmt stmt : rstmt =
  begin match stmt with
  | ExprStmt(_, e) ->
      let re = expr_to_rexpr e in
      RExprStmt(re)

  | ReturnStmt(e) ->
      let re = expr_to_rexpr e in
      RReturnStmt(re)

  | DeclStmt(name, _, t, e) ->
      let re = expr_to_rexpr e in
      RDeclStmt(name, t, re)

  | DeclDefStmt(names_quals_ts) ->
      let names_ts = List.map (fun (name, _, t) -> (name, t)) names_quals_ts in
      RDeclDefStmt(names_ts)

  | AssignStmt(name, named_t, idxs, e) ->
      let ridxs = List.map assign_idx_lval_to_rassign_idx_lval idxs in
      let re = expr_to_rexpr e in
      RAssignStmt(name, named_t, ridxs, re)

  (* Deconstructing `let` stmts can be described as first assigning the
  result of the expr-to-be-deconstructed to a placeholder named variable, and
  then performing a series of indexes onto that variable into the target
  "real" deconstructed variable names. *)
  | DeclDeconStmt(names_quals, t, e) ->
      let names = List.map (fun (name, _) -> name) names_quals in
      let re = expr_to_rexpr e in

      let placeholder_name = Printf.sprintf "__%s" (fmt_join_strs "_" names) in

      let init_rstmt = RDeclStmt(placeholder_name, t, re) in
      let decon_rstmts =
        begin match t with
        | Tuple(ts) ->
            map2i (
              fun i name t_elem ->
                RDeclStmt(
                  name, t_elem,
                  RTupleIndexExpr(t_elem, i, RValVar(t, placeholder_name))
                )
            ) names ts

        | _ ->
            failwith "Cannot rewrite deconstruction of non-tuple decl."
        end
      in
      RStmts(init_rstmt :: decon_rstmts)
  end

and f_param_to_rf_param (name, _, t) = (name, t)

and func_decl_t_to_rfunc_decl_t {f_name; f_params; f_ret_t} =
  let rf_params = List.map f_param_to_rf_param f_params in
  {rf_name=f_name; rf_params=rf_params; rf_ret_t=f_ret_t}

and func_def_t_to_rfunc_def_t {f_decl; f_stmts} =
  let rf_decl = func_decl_t_to_rfunc_decl_t f_decl in
  let rf_stmts = List.map stmt_to_rstmt f_stmts in
  {rf_decl=rf_decl; rf_stmts=rf_stmts}
;;

let rec fmt_rexpr ?(init_ind=false) ?(ind="") ?(print_typ = false) re : string =
  let init_ind = if init_ind then ind else "" in
  let (typ_s, typ_s_rev) =
    if print_typ
    then
      let typ_formatted = rexpr_type re |> fmt_type in
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

  | RValRawArray(t) ->
      Printf.sprintf "%s<uninitialized of %s>%s"
        init_ind (fmt_type t) typ_s

  | RValCast(target_t, op, exp) ->
      let op_fmt = fmt_cast_op op in
      Printf.sprintf "%scast_%s<%s>(%s)%s"
        init_ind
        op_fmt
        (fmt_type target_t)
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
        (fmt_bin_op op)
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

  | RVariantCtorExpr(_, ctor_name, exprs) ->
      let exprs_fmt =
        begin match exprs with
        | [] -> ""
        | _ ->
            let exprs_fmt = fmt_join_rexprs ", " exprs in
            Printf.sprintf "(%s)" exprs_fmt
        end
      in

      Printf.sprintf "%s%s%s%s"
        init_ind
        ctor_name
        exprs_fmt
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

  let _maybe_fmt_type t =
    if print_typ then
      sprintf ":%s" (fmt_type t)
    else
      ""
  in

  let rec _fmt_rpattern rpatt =
    begin match rpatt with
    | RPNil ->
        sprintf "<nil>"
    | RWild(t) ->
        sprintf "_%s" (_maybe_fmt_type t)
    | RVarBind(t, var_name) ->
        sprintf "%s%s" var_name (_maybe_fmt_type t)
    | RPBool(b) ->
        sprintf "%b%s" b (_maybe_fmt_type Bool)
    | RPIntLit(_, i) ->
        sprintf "(%d)" i
    | RPIntFrom(_, i) ->
        sprintf "(%d..)" i
    | RPIntUntil(_, i) ->
        sprintf "(..%d)" i
    | RPIntRange(_, i, j) ->
        sprintf "(%d..%d)" i j
    | RPTuple(t, patterns) ->
        let patterns_fmt = List.map _fmt_rpattern patterns in
        sprintf "(%s)%s" (fmt_join_strs ", " patterns_fmt) (_maybe_fmt_type t)
    | RCtor(t, ctor_name, patterns) ->
        let patterns_fmt =
          begin match patterns with
          | [] -> ""
          | _ ->
              let patterns_fmt = List.map _fmt_rpattern patterns in
              sprintf "(%s)%s"
                (fmt_join_strs ", " patterns_fmt)
                (_maybe_fmt_type t)
          end
        in
        sprintf "%s%s%s" ctor_name patterns_fmt (_maybe_fmt_type t)
    | RPatternAs(t, pattern, var_name) ->
        sprintf "%s%s as %s" (_fmt_rpattern pattern) (_maybe_fmt_type t) var_name
    end
  in
  let rpattern_fmt = _fmt_rpattern rpatt in

  sprintf "%s| %s" init_ind rpattern_fmt

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

and fmt_join_idents_types
  delim (idents_types : (ident_t * berk_t) list) : string =
  match idents_types with
  | [] -> ""

  | [(ident, t)] ->
      Printf.sprintf "%s: %s" ident (fmt_type t)

  | (ident, t)::xs ->
      Printf.sprintf "%s: %s%s%s"
        ident
        (fmt_type t)
        delim
        (fmt_join_idents_types delim xs)

and fmt_rassign_lval_idxs ?(print_typ = false) lval_idxs =
  let rec _fmt_rassign_lval_idxs lval_idxs_rem fmt_so_far =
    begin match lval_idxs_rem with
    | [] -> fmt_so_far
    | idx :: rest ->
        let fmt = fmt_rassign_lval_idx ~print_typ:print_typ idx in
        _fmt_rassign_lval_idxs rest (fmt_so_far ^ fmt)
    end
  in
  _fmt_rassign_lval_idxs lval_idxs ""

and fmt_rassign_lval_idx ?(print_typ = false) lval_idx =
  begin match lval_idx with
  | RALStaticIndex(t, i) ->
      let t_fmt = if print_typ then ":" ^ (fmt_type t) else "" in
      Printf.sprintf ".%d%s" i t_fmt

  | RALIndex(t, exp) ->
      let t_fmt = if print_typ then ":" ^ (fmt_type t) else "" in
      Printf.sprintf "[%s]%s" (fmt_rexpr ~print_typ:print_typ exp) t_fmt
  end

and fmt_rstmt ?(print_typ = false) ind rstmt =
  begin match rstmt with
  | RDeclStmt (ident, btype, ex) ->
      let typ_s = match btype with
        | Undecided -> ""
        | x -> fmt_type x |> Printf.sprintf ": %s"
      in
      Printf.sprintf "%slet %s%s = %s;\n"
        ind
        ident
        typ_s
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RDeclDefStmt (idents_ts) ->
      Printf.sprintf "%slet %s;\n"
        ind
        (fmt_join_idents_types ", " idents_ts)

  | RAssignStmt (ident, btype, lval_idxs, ex) ->
      Printf.sprintf "%s%s:%s %s = %s;\n"
        ind
        ident
        (fmt_type btype)
        (fmt_rassign_lval_idxs ~print_typ:print_typ lval_idxs)
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RExprStmt (ex) ->
      Printf.sprintf "%s%s;\n"
        ind
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RReturnStmt (ex) ->
      Printf.sprintf "%sreturn %s;\n"
        ind
        (fmt_rexpr ~ind:ind ~print_typ:print_typ ex)

  | RStmts(stmts) ->
      let formatted_stmts = List.map (fmt_rstmt ind) stmts in
      Printf.sprintf "%s"
        (fmt_join_strs "" formatted_stmts)
  end

let rec fmt_rfunc_decl_t ?(print_typ = false) ?(extern = false) f_decl : string =
  let maybe_extern =
    if extern
      then "extern "
      else ""
  in
  Printf.sprintf "%s%s;\n"
    maybe_extern
    (fmt_rfunc_decl_t_signature ~print_typ:print_typ f_decl)

and fmt_rfunc_decl_t_signature
  ?(print_typ = false) {rf_name; rf_params; rf_ret_t} : string
=
  let ret_t_s = begin match rf_ret_t with
    | Nil
    | Undecided ->
        if print_typ
        then Printf.sprintf ": %s" (fmt_type rf_ret_t)
        else ""
    | _ -> Printf.sprintf ": %s" (fmt_type rf_ret_t)
  end in

  Printf.sprintf "fn %s(%s)%s"
    rf_name
    (fmt_join_func_params "," rf_params)
    ret_t_s

and fmt_rf_param (p_name, p_type) : string =
  Printf.sprintf "%s: %s"
    p_name
    (fmt_type p_type)

and fmt_join_func_params delim params : string =
  match params with
  | [] -> ""
  | [x] -> fmt_rf_param x
  | x::xs ->
      Printf.sprintf "%s%s %s"
        (fmt_rf_param x)
        delim
        (fmt_join_func_params delim xs)

and fmt_rfunc_def_t ?(print_typ = false) {rf_decl; rf_stmts;} : string =
  let formatted_stmts =
    List.fold_left (^) "" (
      List.map (fmt_rstmt ~print_typ:print_typ "  ") rf_stmts
    )
  in

  Printf.sprintf "%s {\n%s}\n"
    (fmt_rfunc_decl_t_signature ~print_typ:print_typ rf_decl)
    formatted_stmts
;;
