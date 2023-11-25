open Ast
open Ir
open Lexer
open Typing


exception Backtrack


let print_trace ?(start_trace=false) ind func_name tokens : string =
  begin
    if ind <> "" || start_trace then
      begin
        Printf.printf "%sParsing: [%s] with [%s]\n"
          ind func_name (fmt_next_token tokens) ;
        (ind ^ " ")
      end
    else ind
  end
;;


let rec parse_tokens ?(trace=false) tokens : module_decl list =
  let ind_next = print_trace ~start_trace:trace "" __FUNCTION__ tokens in

  let rec _parse_tokens tokens mod_decls_so_far =
    begin match tokens with
    | [] -> mod_decls_so_far

    | KWExtern(_) :: rest ->
        let (rest, mod_decl) = parse_extern ~ind:ind_next rest in
        _parse_tokens rest (mod_decl :: mod_decls_so_far)

    | KWVariant(_) :: rest ->
        let (rest, mod_decl) = parse_variant ~ind:ind_next rest in
        _parse_tokens rest (mod_decl :: mod_decls_so_far)

    | KWFn(_) :: rest ->
        let (rest, mod_decl) = parse_func ~ind:ind_next rest in
        _parse_tokens rest (mod_decl :: mod_decls_so_far)

    | KWGn(_) :: rest ->
        let (rest, func_def) = parse_generator ~ind:ind_next rest in
        let mod_decl = GeneratorDef(func_def) in
        _parse_tokens rest (mod_decl :: mod_decls_so_far)

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s], expected among `fn`|`variant`|`extern`"
            fmted
        )
    end
  in

  _parse_tokens tokens []


and parse_extern ?(ind="") tokens : (token list * module_decl) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | KWFn(_) :: rest ->
      let (rest, f_decl, f_template_params) =
        parse_func_decl ~ind:ind_next rest
      in
      begin match f_template_params with
      | [] ->
          (rest, FuncExternDecl(f_decl))

      | _ ->
          (
            rest,
            FuncExternTemplateDecl({f_template_params; f_template_decl=f_decl})
          )
      end

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s] parsing extern, expected `fn`." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing `extern` declaration."
  end

(* Parse everything after the `variant` keyword in a variant decl, eg:

variant <`a, `b> {
  | Some(i32, i64)
  | None
}

*)
and parse_variant ?(ind="") tokens : (token list * module_decl) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  (* Parse eg:
    `a, `b, `c
  *)
  let _parse_variant_typ_vars ?(ind="") tokens =
    let ind_next = print_trace ind __FUNCTION__ tokens in

    let rec __parse_variant_type_vars ?(ind="") tokens t_vars_so_far_rev =
      let _ = print_trace ind __FUNCTION__ tokens in

      begin match tokens with
      | TickIdent(_, typ_var_name) :: Comma(_) :: rest ->
          let t_vars_so_far_rev' = (typ_var_name :: t_vars_so_far_rev) in
          __parse_variant_type_vars ~ind:ind rest t_vars_so_far_rev'

      | TickIdent(_, typ_var_name) :: rest ->
          (rest, (typ_var_name :: t_vars_so_far_rev))

      | _ ->
          (tokens, t_vars_so_far_rev)
      end
    in

    let (rest, t_vars_rev) =
      __parse_variant_type_vars ~ind:ind_next tokens []
    in
    let t_vars = List.rev t_vars_rev in
    (rest, t_vars)
  in

  (* Parse eg:
    | Some(i32, i64, bool)
    | Other(bool)
    | Thing
  *)
  let _parse_variant_constructors ?(ind="") tokens =
    let ind_next = print_trace ind __FUNCTION__ tokens in

    let rec __parse_variant_constructors ?(ind="") tokens v_ctors_so_far_rev =
      let ind_next = print_trace ind __FUNCTION__ tokens in

      (* Parse an individual field of an individual variant constructor. *)
      let _parse_variant_field ?(ind="") tokens : (token list * v_ctor_field) =
        let _ = print_trace ind __FUNCTION__ tokens in

        let (rest, field_t) = parse_type tokens in
        (rest, {t=field_t})
      in

      begin match tokens with
      | Bar(_) :: CapIdent(_, v_ctor_name) :: LParen(_) :: rest ->
          let (rest, first_field) = _parse_variant_field rest in

          let rec _parse_variant_ctor_fields
            ?(ind="") tokens collected_fields_rev
          =
            let _ = print_trace ind __FUNCTION__ tokens in

            begin match tokens with
            | Comma(_) :: rest ->
                let (rest, next_field) = _parse_variant_field rest in
                let collected_fields_rev' =
                  (next_field :: collected_fields_rev)
                in
                _parse_variant_ctor_fields ~ind:ind rest collected_fields_rev'

            | _ ->
                (tokens, collected_fields_rev)
            end
          in

          let (rest, collected_fields_rev) =
            _parse_variant_ctor_fields ~ind:ind_next rest []
          in
          let collected_fields = List.rev collected_fields_rev in

          let all_fields = first_field :: collected_fields in

          begin match rest with
          | RParen(_) :: rest ->
              let v_ctor = {name=v_ctor_name; fields=all_fields} in
              let v_ctors_so_far_rev' = v_ctor :: v_ctors_so_far_rev in
              __parse_variant_constructors ~ind:ind rest v_ctors_so_far_rev'

          | _ ->
              failwith "Could not find matching `)` in variant ctor decl"
          end

      | Bar(_) :: CapIdent(_, v_ctor_name) :: rest ->
          let v_ctor = {name=v_ctor_name; fields=[]} in
          let v_ctors_so_far_rev' = v_ctor :: v_ctors_so_far_rev in
          __parse_variant_constructors ~ind:ind rest v_ctors_so_far_rev'

      | _ ->
          (tokens, v_ctors_so_far_rev)
      end
    in

    let (rest, v_ctors_rev) =
      __parse_variant_constructors ~ind:ind_next tokens []
    in
    let v_ctors = List.rev v_ctors_rev in
    (rest, v_ctors)
  in

  (* Parse the closing brace at the end of the variant decl. *)
  let _parse_variant_end ?(ind="") tokens v_name v_ctors v_typ_vars =
    let _ = print_trace ind __FUNCTION__ tokens in

    begin match tokens with
    | RBrace(_) :: rest ->
        (
          rest,
          VariantDecl({v_name=v_name; v_ctors=v_ctors; v_typ_vars=v_typ_vars})
        )

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] parsing variant decl, expected `}`." fmted
        )

    | [] -> failwith "Unexpected EOF while parsing `variant` declaration."
    end
  in

  (* Parse everything after the `variant` keyword. *)
  begin match tokens with
  | CapIdent(_, v_name) :: Lesser(_) :: rest ->
      let (rest, v_typ_vars) = _parse_variant_typ_vars ~ind:ind_next rest in

      let rest =
        begin match rest with
        | Greater(_) :: LBrace(_) :: rest -> rest

        | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] parsing variant decl, expected `>`." fmted
          )

        | [] -> failwith "Unexpected EOF while parsing `variant` declaration."
        end
      in

      let (rest, v_ctors) = _parse_variant_constructors ~ind:ind_next rest in
      _parse_variant_end ~ind:ind_next rest v_name v_ctors v_typ_vars

  | CapIdent(_, v_name) :: LBrace(_) :: rest ->
      let (rest, v_ctors) = _parse_variant_constructors ~ind:ind_next rest in
      _parse_variant_end ~ind:ind_next rest v_name v_ctors []


  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s] parsing variant, expected identifier." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing `variant` declaration."
  end


and parse_func_decl
  ?(ind="") tokens : (token list * func_decl_t * f_template_param list)
=
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let _parse_func_tail f_name f_params f_template_params tokens =
    begin match tokens with
    | Colon(_) :: rest ->
        let (rest, f_ret_t) = parse_type ~ind:ind_next rest in
        (
          rest, {
            f_name=f_name;
            f_params=f_params;
            f_ret_t=f_ret_t;
          },
          f_template_params
        )

    | _ ->
        (
          tokens, {
            f_name=f_name;
            f_params=f_params;
            f_ret_t=Nil
          },
          f_template_params
        )
    end
  in

  let _parse_func_err tok =
    let fmted = fmt_token tok in
    failwith (
      Printf.sprintf
        "Unexpected token [%s], expected lc-identifer" fmted
    )
  in

  begin match tokens with
  (* Concrete function declaration. *)
  | LowIdent(_, f_name) :: LParen(_) :: rest ->
      let (rest, f_params) = parse_func_params ~ind:ind_next rest in
      _parse_func_tail f_name f_params [] rest

  (* Templated function declaration. *)
  | LowIdent(_, f_name) :: Lesser(_) :: rest ->
      let (rest, f_template_params) =
        parse_func_template_params ~ind:ind_next rest
      in

      begin match rest with
      | LParen(_) :: rest ->
          let (rest, f_params) = parse_func_params ~ind:ind_next rest in
          _parse_func_tail f_name f_params f_template_params rest

      | tok :: _ ->
          _parse_func_err tok

      | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
      end

  | tok :: _ ->
      _parse_func_err tok

  | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
  end


and parse_generator_decl ?(ind="") tokens : (token list * generator_decl_t) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LowIdent(_, g_name) :: LParen(_) :: rest ->
      let (rest, g_params) = parse_func_params ~ind:ind_next rest in

      begin match rest with
      | Colon(_) :: rest ->
          let (rest, g_ret_t) = parse_type ~ind:ind_next rest in
          (
            rest, {
              g_name=g_name;
              g_params=g_params;
              g_yield_t=Nil;
              g_ret_t=g_ret_t;
            }
          )

      | KWYield(_) :: rest ->
          let (rest, g_yield_t) = parse_type ~ind:ind_next rest in

          begin match rest with
          | Colon(_) :: rest ->
              let (rest, g_ret_t) = parse_type ~ind:ind_next rest in
              (
                rest, {
                  g_name=g_name;
                  g_params=g_params;
                  g_yield_t=g_yield_t;
                  g_ret_t=g_ret_t;
                }
              )

          | _ ->
              (
                rest, {
                  g_name=g_name;
                  g_params=g_params;
                  g_yield_t=g_yield_t;
                  g_ret_t=Nil;
                }
              )
          end

      | _ ->
          (
            rest, {
              g_name=g_name;
              g_params=g_params;
              g_yield_t=Nil;
              g_ret_t=Nil;
            }
          )
      end

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected lc-identifer" fmted
      )
  | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
  end


and parse_func_params ?(ind="") tokens : (token list * f_param list) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let parse_func_param ?(ind="") tokens params_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    let (rest, qual) = parse_var_qual ~ind:ind_next tokens in

    begin match rest with
    | LowIdent(_, p_name) :: Colon(_) :: rest ->
        let (rest, t) = parse_type ~ind:ind_next rest in
        let param = (p_name, qual, t) in
        let params_so_far = params_so_far @ [param] in

        (rest, params_so_far)

    | TriEllipses(_) :: rest ->
        let param = ("vargs", qual, VarArgSentinel) in
        let params_so_far = params_so_far @ [param] in

        (rest, params_so_far)

    | _ :: _ -> (rest, params_so_far)

    | [] -> failwith "Unexpected EOF while parsing `fn` param declaration."
    end
  in

  let rec _parse_func_params ?(ind="") tokens params_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    let (rest, params_so_far) =
      parse_func_param ~ind:ind_next tokens params_so_far
    in

    begin match rest with
    | RParen(_) :: rest ->
        (rest, params_so_far)

    | Comma(_) :: rest ->
        _parse_func_params ~ind:ind_next rest params_so_far

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s], expected lc-identifer" fmted
        )
    | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
    end
  in

  _parse_func_params ~ind:ind_next tokens []


and parse_func_template_params ?(ind="") tokens : (token list * ident_t list) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let parse_func_template_param ?(ind="") tokens template_params_so_far =
    let _ = print_trace ind __FUNCTION__ tokens in

    begin match tokens with
    | TickIdent(_, name) :: rest ->
        (rest, (template_params_so_far @ [name]))

    | _ :: _ ->
        (tokens, template_params_so_far)

    | [] ->
        failwith "Unexpected EOF while parsing `fn` template param declaration."
    end
  in

  let rec _parse_func_template_params ?(ind="") tokens template_params_so_far =
    let ind_next = print_trace ind __FUNCTION__ tokens in

    let (rest, template_params_so_far) =
      parse_func_template_param ~ind:ind_next tokens template_params_so_far
    in

    begin match rest with
    | Greater(_) :: rest ->
        (rest, template_params_so_far)

    | Comma(_) :: rest ->
        _parse_func_template_params ~ind:ind_next rest template_params_so_far

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s], expected lc-identifer" fmted
        )
    | [] -> failwith "Unexpected EOF while parsing `fn` declaration."
    end
  in

  _parse_func_template_params ~ind:ind_next tokens []


and parse_type ?(ind="") tokens : (token list * berk_t) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | KWi8(_)  :: rest -> (rest, I8)
  | KWi16(_) :: rest -> (rest, I16)
  | KWi32(_) :: rest -> (rest, I32)
  | KWi64(_) :: rest -> (rest, I64)
  | KWu8(_)  :: rest -> (rest, U8)
  | KWu16(_) :: rest -> (rest, U16)
  | KWu32(_) :: rest -> (rest, U32)
  | KWu64(_) :: rest -> (rest, U64)
  | KWf32(_) :: rest -> (rest, F32)
  | KWf64(_) :: rest -> (rest, F64)
  | KWf128(_) :: rest -> (rest, F128)
  | KWBool(_) :: rest -> (rest, Bool)
  | KWString(_) :: rest -> (rest, String)
  | LParen(_) :: RParen(_) :: rest -> (rest, Nil)

  (* Type variable *)
  | TickIdent(_, name) :: rest -> (rest, Unbound(name))

  (* Reference *)
  | KWRef(_) :: rest ->
      let (rest, refed_t) = parse_type ~ind:ind_next rest in
      (rest, Ref(refed_t))

  (* Static array. *)
  | LBracket(_) :: Integer(_, i) :: RBracket(_) :: rest ->
      let (rest, arr_t) = parse_type ~ind:ind_next rest in
      (rest, Array(arr_t, i))

  (* Size-templated static array. *)
  | LBracket(_) :: TickIdent(_, name)  :: RBracket(_) :: rest ->
      let (rest, arr_t) = parse_type ~ind:ind_next rest in
      (rest, SizeTemplatedArray(arr_t, Unbound(name)))

  (* Parse tuple. *)
  | LParen(_) :: rest ->
      let (rest, init_t) = parse_type ~ind:ind_next rest in

      (* There must be at least one comma, if this is a tuple type. There may be
      more types in this tuple, all comma-delimited. As a special case, it's
      valid to spell a 1-tuple via `(<type>,)`. *)
      begin match rest with
      (* Is this a 1-tuple? *)
      | Comma(_) :: RParen(_) :: rest ->
          (rest, Tuple([init_t]))

      (* This is at least a 2-tuple. *)
      | Comma(_) :: rest ->
          let (rest, pair_t) = parse_type ~ind:ind_next rest in

          (* At this point, we want to match 0 or more `, <type>` sequences,
          followed by a final closing paren. *)
          let rec _parse_remaining_tuple_t rest ts_so_far =
            begin match rest with
            | Comma(_) :: rest ->
                let (rest, next_t) = parse_type ~ind:ind_next rest in
                _parse_remaining_tuple_t rest (ts_so_far @ [next_t])

            | RParen(_) :: rest ->
                (rest, ts_so_far)

            | tok :: _ ->
                let fmted = fmt_token tok in
                failwith (
                  Printf.sprintf
                    "Unexpected token [%s] parsing tuple type, expected `)`."
                    fmted
                )
            | [] -> failwith "Unexpected EOF while parsing tuple type."
            end
          in

          let (rest, remaining_tuple_ts) = _parse_remaining_tuple_t rest [] in

          (
            rest,
            Tuple([init_t; pair_t] @ remaining_tuple_ts)
          )

      | _ -> failwith "Failed to complete parse of tuple type."
      end

  | CapIdent(_, name) :: Lesser(_) :: rest ->
      let (rest, first_t) = parse_type ~ind:ind_next rest in

      (* At this point, we want to match 0 or more `, <type>` sequences,
      followed by a final closing angle bracket. *)
      let rec _parse_remaining_template_inst_ts rest rest_ts_rev =
        begin match rest with
        | Comma(_) :: rest ->
            let (rest, next_t) = parse_type ~ind:ind_next rest in
            _parse_remaining_template_inst_ts rest (next_t :: rest_ts_rev)

        | Greater(_) :: rest ->
            (rest, rest_ts_rev)

        | tok :: _ ->
            let fmted = fmt_token tok in
            failwith (
              Printf.sprintf
                "Unexpected token [%s] parsing type, expected `>`."
                fmted
            )
        | [] -> failwith "Unexpected EOF while parsing type."
        end
      in

      let (rest, rest_ts_rev) = _parse_remaining_template_inst_ts rest [] in
      let rest_ts = List.rev rest_ts_rev in
      let template_inst_ts = first_t :: rest_ts in

      (rest, UnboundType(name, template_inst_ts))

  | CapIdent(_, name) :: rest ->
      (rest, UnboundType(name, []))

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected lc-identifer." fmted
      )
  | [] -> failwith "Unexpected EOF while parsing type."
  end


and parse_func ?(ind="") tokens : (token list * module_decl) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let (rest, f_decl, f_template_params) =
    parse_func_decl ~ind:ind_next tokens
  in
  let (rest, f_stmts) = parse_stmt_block ~ind:ind_next rest in

  begin match f_template_params with
  | [] ->
      (rest, FuncDef({f_decl=f_decl; f_stmts=f_stmts}))

  | _ ->
      (
        rest,
        FuncTemplateDef(
          {
            f_template_def_decl={f_template_params; f_template_decl=f_decl};
            f_template_stmts=f_stmts
          }
        )
      )
  end


and parse_generator ?(ind="") tokens : (token list * generator_def_t) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let (rest, g_decl) = parse_generator_decl ~ind:ind_next tokens in
  let (rest, g_stmts) = parse_stmt_block ~ind:ind_next rest in

  (
    rest, {
      g_decl=g_decl;
      g_stmts=g_stmts;
    }
  )


and parse_stmt_block ?(ind="") tokens : (token list * stmt list) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LBrace(_) :: rest ->
      let (rest, stmts) = parse_stmts ~ind:ind_next rest in

      begin match rest with
      | RBrace(_) :: rest -> (rest, stmts)

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s], expected `}`" fmted
          )
      | [] -> failwith "Unexpected EOF while searching for closing `}`."
      end

  | tok :: _ ->
      let fmted = fmt_token tok in
      failwith (
        Printf.sprintf
          "Unexpected token [%s], expected `{`" fmted
      )
  | [] -> failwith "Unexpected EOF while parsing block."
  end


and parse_expr_block ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LBrace(_) :: rest ->
      let (rest, stmts) = parse_stmts ~ind:ind_next rest in
      let (rest, exp) = begin
        try parse_expr ~ind:ind_next rest
        with Backtrack ->
        (rest, ValNil)
      end in

      begin match rest with
      | RBrace(_) :: rest -> (rest, BlockExpr(Undecided, stmts, exp))

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] in expr block, expected `}`" fmted
          )
      | [] -> failwith "Unexpected EOF while searching for closing `}`."
      end

  | _ -> raise Backtrack
  end


and parse_stmts ?(ind="") tokens : (token list * stmt list) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_stmts ?(ind="") tokens stmts_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match (parse_stmt ~ind:ind_next tokens) with
    | Some((rest, stmt)) ->
        _parse_stmts ~ind:ind_next rest (stmts_so_far @ [stmt])

    | None ->
        (tokens, stmts_so_far)
    end
  in

  _parse_stmts ~ind:ind_next tokens []


and parse_stmt ?(ind="") tokens : (token list * stmt) option =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  try
    let (rest, stmt) =
      begin match tokens with
      | KWLet(_) :: rest -> parse_decl_stmt ~ind:ind_next rest

      (* A return with no expression is a void return. *)
      | KWReturn(_) :: ((Semicolon(_) :: _) as rest) ->
          (rest, ReturnStmt(ValNil))

      | KWReturn(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, ReturnStmt(exp))

      (* A yield with no expression is a void yield. *)
      | KWYield(_) :: ((Semicolon(_) :: _) as rest) ->
          (rest, YieldStmt(ValNil))

      | KWYield(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, YieldStmt(exp))

      | _ ->
          try parse_assign_stmt ~ind:ind_next tokens
          with Backtrack ->
          parse_expr_stmt ~ind:ind_next tokens
      end
    in

    begin match (stmt, rest) with
    (* For certain block-based expression-statements, the trailing semicolon
    is optional. *)
    | (
        (
          ExprStmt(_, BlockExpr(_, _, _))
        | ExprStmt(_, IfThenElseExpr(_, _, _, _))
        | ExprStmt(_, IfIsThenElseExpr(_, _, _, _))
        | ExprStmt(_, WhileExpr(_, _, _, _))
        | ExprStmt(_, MatchExpr(_, _, _))
        ),
        (
          (Semicolon(_) :: rest)
        | rest
        )
      ) ->
        Some(rest, stmt)

    | (_, Semicolon(_) :: rest) -> Some(rest, stmt)

    | (_, _ :: _) -> None

    | (_, []) -> failwith "Unexpected EOF while parsing stmt."
    end

  with Backtrack ->
    None


and parse_var_qual ?(ind="") tokens : (token list * var_qual) =
  let _ = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | KWMut(_) :: rest -> (rest, {mut=true})

  | _ -> (tokens, {mut=false})
  end


and parse_decl_stmt ?(ind="") tokens : (token list * stmt) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  (* Parse eg:
    my_var
    mut my_var
    mut my_var: (bool, u32)
  *)
  let _parse_qual_varname_t
    ?(ind="") tokens : (token list * (var_qual * ident_t * berk_t))
  =
    let _ = print_trace ind __FUNCTION__ tokens in

    let (rest, qual) = parse_var_qual ~ind:ind_next tokens in

    begin match rest with
    | LowIdent(_, name) :: Colon(_) :: rest ->
        let (rest, t) = parse_type ~ind:ind_next rest in
        (rest, (qual, name, t))

    | LowIdent(_, name) :: rest ->
        (rest, (qual, name, Undecided))

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] (decl_stmt), expected identifier." fmted
        )
    | [] -> failwith "Unexpected EOF while parsing let declaration."
    end
  in

  (* Parse eg:
    my_var = 3
    mut my_var: (bool, u32) = (true || false, 5 + 6)
    (mut var1, var2: u32, mut var3: bool, var4) = (1, 2, true, 3)
  *)
  begin match tokens with
  | LParen(_) :: rest ->
      let (rest, first_qual_name_t) =
        _parse_qual_varname_t ~ind:ind_next rest
      in

      let rec _parse_remaining_qual_varname_t tokens qual_name_ts_rev =
        begin match tokens with
        | Comma(_) :: rest ->
            let (rest, next_name_qual_t) =
              _parse_qual_varname_t ~ind:ind_next rest
            in
            let qual_name_ts_rev' = (next_name_qual_t :: qual_name_ts_rev) in
            _parse_remaining_qual_varname_t rest qual_name_ts_rev'

        | _ ->
            (tokens, qual_name_ts_rev)
        end
      in

      let (rest, qual_name_ts_rev) = _parse_remaining_qual_varname_t rest [] in
      let qual_name_ts = List.rev qual_name_ts_rev in
      let qual_name_ts = first_qual_name_t :: qual_name_ts in
      let idents_quals =
        List.map (fun (qual, name, _) -> (name, qual)) qual_name_ts
      in
      let ts =
        List.map (fun (_, _, t) -> t) qual_name_ts
      in
      let tuple_t = Tuple(ts) in

      begin match rest with
      | RParen(_) :: Equal(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, DeclDeconStmt(idents_quals, tuple_t, exp))

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] (decl_stmt), expected identifier." fmted
          )
      | [] -> failwith "Unexpected EOF while parsing let declaration."
      end

  | _ ->
      let (rest, (qual, varname, t)) =
        _parse_qual_varname_t ~ind:ind_next tokens
      in

      begin match rest with
      | Equal(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in
          (rest, DeclStmt(varname, qual, t, exp))

      (* Lookahead to the semicolon, if there is one. If so, this is a
      "default declaration": `let var: bool; *)
      | (Semicolon(_) :: _) as rest ->
          (rest, DeclDefaultStmt([(varname, qual, t)]))

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] (decl_stmt), expected identifier." fmted
          )
      | [] -> failwith "Unexpected EOF while parsing let declaration."
      end
  (* TODO: Extend to recognize DeclDefaultStmt with multiple fields. *)
  end


and parse_assign_stmt ?(ind="") tokens : (token list * stmt) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  (* Parse `[<indexing-expr>]` *)
  let _parse_assign_array_index
    ?(ind="") tokens : (token list * assign_idx_lval)
  =
    let _ = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | LBracket(_) :: rest ->
        let (rest, indexing_exp) = parse_expr ~ind:ind_next rest in

        begin match rest with
        | RBracket(_) :: rest ->
            (rest, ALIndex(Undecided, indexing_exp))

        | _ -> failwith "Could not complete parse of indexing assignment."
        end

    | _ -> raise Backtrack
    end
  in

  (* Parse `.*` *)
  let _parse_assign_deref
    ?(ind="") tokens : (token list * assign_idx_lval)
  =
    let _ = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Dot(_) :: Star(_) :: rest ->
        (rest, ALDeref(Undecided))

    | _ -> raise Backtrack
    end
  in

  (* Parse `.<literal-integer>` *)
  let _parse_assign_tuple_index
    ?(ind="") tokens : (token list * assign_idx_lval)
  =
    let _ = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Dot(_) :: Integer(_, i) :: rest ->
        (rest, ALStaticIndex(Undecided, i))

    | _ -> raise Backtrack
    end
  in

  (* Assignment to some LHS value may be after an arbitrarily complex indexing
  into it (array indexing, tuple member indexing, recordfield indexing). *)
  let rec _parse_assign_index ?(ind="") rest idxs_so_far_rev =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token rest) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin
      try
        let (rest, idx) = _parse_assign_array_index ~ind:ind_next rest in
        _parse_assign_index rest (idx :: idxs_so_far_rev)
      with Backtrack ->
      try
        let (rest, idx) = _parse_assign_deref ~ind:ind_next rest in
        _parse_assign_index rest (idx :: idxs_so_far_rev)
      with Backtrack ->
      try
        let (rest, idx) = _parse_assign_tuple_index ~ind:ind_next rest in
        _parse_assign_index rest (idx :: idxs_so_far_rev)
      with Backtrack ->
        (rest, idxs_so_far_rev)
    end
  in

  (* Attempt to parse an assignment stmt. *)
  begin match tokens with
  (* var = ... *)
  | LowIdent(_, name) :: Equal(_) :: rest ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in
      (rest, AssignStmt(name, Undecided, [], exp))

  (* complex_datastructure.*[i + 2][6].2.3[4] = ... *)
  | LowIdent(_, name) :: rest ->
      let (rest, idxs_rev) = _parse_assign_index ~ind:ind_next rest [] in
      let idxs = List.rev idxs_rev in

      (* Once we've exhausted parsing some arbitrarily-deep series of indexing
      operations, we expect to see the assignment token if this is actually
      an assignment (and not, say, an expression-stmt that included indexing).
      *)
      begin match rest with
      | Equal(_) :: rest ->
          let (rest, exp) = parse_expr ~ind:ind_next rest in

          (rest, AssignStmt(name, Undecided, idxs, exp))

      | _ -> raise Backtrack
      end

  (* TODO: Extend to recognize AssignDeconStmt *)

  | _ -> raise Backtrack
  end


and parse_expr_stmt ?(ind="") tokens : (token list * stmt) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let (rest, es_mods) =
    begin match tokens with
    | KWIgnore(_) :: rest -> (rest, {ignore=true})
    | _ -> (tokens, {ignore=false})
    end
  in

  let (rest, exp) = parse_expr ~ind:ind_next rest in
  (rest, ExprStmt(es_mods, exp))


and parse_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let (rest, exp) = parse_logical_or ~ind:ind_next tokens in
  (rest, exp)


and parse_logical_or ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_logical_or ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | BarBar(_) :: rest ->
        let (rest, exp_rhs) = parse_logical_and ~ind:ind_next rest in
        let exp = BinOp(Undecided, LOr, exp_lhs, exp_rhs) in
        _parse_logical_or ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_logical_and ~ind:ind_next tokens in
  _parse_logical_or ~ind:ind_next rest exp_lhs


and parse_logical_and ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_logical_and ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | AmpAmp(_) :: rest ->
        let (rest, exp_rhs) = parse_equality ~ind:ind_next rest in
        let exp = BinOp(Undecided, LAnd, exp_lhs, exp_rhs) in
        _parse_logical_and ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_equality ~ind:ind_next tokens in
  _parse_logical_and ~ind:ind_next rest exp_lhs


and parse_if_is_reduced_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let (rest, exp) = parse_equality ~ind:ind_next tokens in
  (rest, exp)


and parse_equality ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_equality ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | EqualEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_relation ~ind:ind_next rest in
        let exp = BinOp(Undecided, Eq, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | BangEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_relation ~ind:ind_next rest in
        let exp = BinOp(Undecided, Ne, exp_lhs, exp_rhs) in
        _parse_equality ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_relation ~ind:ind_next tokens in
  _parse_equality ~ind:ind_next rest exp_lhs


and parse_relation ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_relation ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Lesser(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Lt, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | LessEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Le, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | Greater(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Gt, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | GreatEqual(_) :: rest ->
        let (rest, exp_rhs) = parse_sum ~ind:ind_next rest in
        let exp = BinOp(Undecided, Ge, exp_lhs, exp_rhs) in
        _parse_relation ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_sum ~ind:ind_next tokens in
  _parse_relation ~ind:ind_next rest exp_lhs


and parse_sum ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_sum ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Plus(_) :: rest ->
        let (rest, exp_rhs) = parse_prod ~ind:ind_next rest in
        let exp = BinOp(Undecided, Add, exp_lhs, exp_rhs) in
        _parse_sum ~ind:ind_next rest exp

    | Minus(_) :: rest ->
        let (rest, exp_rhs) = parse_prod ~ind:ind_next rest in
        let exp = BinOp(Undecided, Sub, exp_lhs, exp_rhs) in
        _parse_sum ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_prod ~ind:ind_next tokens in
  _parse_sum ~ind:ind_next rest exp_lhs


and parse_prod ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_prod ?(ind="") tokens exp_lhs =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin match tokens with
    | Star(_) :: rest ->
        let (rest, exp_rhs) = parse_unary ~ind:ind_next rest in
        let exp = BinOp(Undecided, Mul, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | Slash(_) :: rest ->
        let (rest, exp_rhs) = parse_unary ~ind:ind_next rest in
        let exp = BinOp(Undecided, Div, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | Percent(_) :: rest ->
        let (rest, exp_rhs) = parse_unary ~ind:ind_next rest in
        let exp = BinOp(Undecided, Mod, exp_lhs, exp_rhs) in
        _parse_prod ~ind:ind_next rest exp

    | _ -> (tokens, exp_lhs)
    end
  in

  let (rest, exp_lhs) = parse_unary ~ind:ind_next tokens in
  _parse_prod ~ind:ind_next rest exp_lhs


and parse_unary ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | Bang(_) :: rest ->
      let (rest, exp) = parse_value ~ind:ind_next rest in
      (rest, UnOp(Undecided, LNot, exp))

  | KWRef(_) :: rest ->
      let (rest, exp) = parse_value ~ind:ind_next rest in
      (rest, RefOf(Undecided, exp))

  | _ ->
      parse_value ~ind:ind_next tokens
  end


and parse_value ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let (rest, exp) = begin
    try parse_array_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_tuple_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_paren_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_if_expr_general ~ind:ind_next tokens
    with Backtrack ->
    try parse_while_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_match_expr ~ind:ind_next tokens
    with Backtrack ->
    try parse_expr_block ~ind:ind_next tokens
    with Backtrack ->
    try parse_func_call ~ind:ind_next tokens
    with Backtrack ->
    try parse_variant_ctor ~ind:ind_next tokens
    with Backtrack ->
    (* try *)
    parse_expr_atom ~ind:ind_next tokens
    (* with Backtrack *)
  end in

  (* There are various things that may then be done _to_ a just-evaluated
  expression, like indexing into arrays/aggregates, invoking functions pointers,
  etc, which can be arbitrarily chained. *)
  let rec _parse_value ?(ind="") rest exp_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token rest) ;
          (ind ^ " ")
        end
      else ind
    end in

    begin
      try
        let (rest, exp_chain) =
          parse_array_index ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
      try
        let (rest, exp_chain) =
          parse_deref ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
      try
        let (rest, exp_chain) =
          (* FIXME: Chained tuple indexing is a lexing ambiguity. Consider:
            let tup = (1, (2, 3), 4);
            let val = tup.1.0;
          where the `1.0` will get lexed as a float value and this parse will
          fail. Workaround: Inject whitespace, a la:
            let val = tup.1 .0;
            let val = tup. 1. 0;
            let val = tup .1 .0;
          *)
          parse_tuple_index ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
      try
        let (rest, exp_chain) =
          parse_ufcs_call ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
      try
        let (rest, exp_chain) =
          parse_func_var_call ~ind:ind_next rest exp_so_far
        in
        _parse_value rest exp_chain
      with Backtrack ->
        (rest, exp_so_far)
    end
  in

  _parse_value ~ind:ind_next rest exp


and parse_if_expr_general ?(ind="") tokens : (token list * expr) =
  try parse_if_expr ~ind:ind tokens
  with Backtrack ->
  parse_if_is_expr ~ind:ind tokens


and parse_func_call ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LowIdent(_, f_name) :: LParen(_) :: RParen(_) :: rest ->
      (rest, FuncCall(Undecided, f_name, []))

  | LowIdent(_, f_name) :: LParen(_) :: rest ->
      let (rest, exps) = parse_func_call_args ~ind:ind_next rest in
      (rest, FuncCall(Undecided, f_name, exps))

  | _ -> raise Backtrack
  end


and parse_func_call_args ?(ind="") tokens : (token list * expr list) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_func_call_args ?(ind="") tokens exps_so_far =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    let (rest, exp) = parse_expr ~ind:ind_next tokens in
    let exps_so_far = exps_so_far @ [exp] in

    begin match rest with
    | RParen(_) :: rest ->
        (rest, exps_so_far)

    | Comma(_) :: rest ->
        _parse_func_call_args ~ind:ind_next rest exps_so_far

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] (args), expected among `,`|`)`." fmted
        )
    | [] -> failwith "Unexpected EOF while parsing func call arg list."
    end
  in

  _parse_func_call_args ~ind:ind_next tokens []

(* As parse_func_call_args but also seeks the position of an argument indicated
only by an underscore, `_`. *)
and parse_func_call_args_w_underscore
  ?(ind="") tokens : (token list * expr list * int option)
=
  let ind_next = print_trace ind __FUNCTION__ tokens in

  let rec _parse_func_call_args_w_underscore
    ?(ind="") tokens exps_so_far cur_pos under_pos
  =
    let ind_next = begin
      if ind <> "" then
        begin
          Printf.printf "%sParsing: [%s] with [%s]\n"
            ind __FUNCTION__ (fmt_next_token tokens) ;
          (ind ^ " ")
        end
      else ind
    end in

    (* Either parse an underscore, or parse a general argument expression. *)
    let (rest, exps_so_far, under_pos) = begin
      begin match tokens with
      | Underscore(_) :: rest ->
          begin match under_pos with
          | None -> (rest, exps_so_far, Some(cur_pos))
          | Some(prev_pos) ->
              failwith (
                Printf.sprintf
                  (
                    "Found underscore while parsing func args at arg " ^^
                    "position [%d] but already noted underscore at " ^^
                    "position [%d]"
                  )
                  cur_pos
                  prev_pos
              )
          end

      | _ ->
        let (rest, exp) = parse_expr ~ind:ind_next tokens in
        let exps_so_far = exps_so_far @ [exp] in
        (rest, exps_so_far, under_pos)

      end
    end in

    begin match rest with
    | RParen(_) :: rest ->
        (rest, exps_so_far, under_pos)

    | Comma(_) :: rest ->
        _parse_func_call_args_w_underscore
          ~ind:ind_next rest exps_so_far (cur_pos + 1) under_pos

    | tok :: _ ->
        let fmted = fmt_token tok in
        failwith (
          Printf.sprintf
            "Unexpected token [%s] (args), expected among `,`|`)`." fmted
        )
    | [] -> failwith "Unexpected EOF while parsing func call arg list."
    end
  in

  _parse_func_call_args_w_underscore ~ind:ind_next tokens [] 0 None


(* Parse invocation of a function pointer, eg:
  .()
  .(arg1, arg2)
*)
and parse_func_var_call ?(ind="") tokens exp : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | Dot(_) :: LParen(_) :: RParen(_) :: rest ->
      (rest, ExprInvoke(Undecided, exp, []))

  | Dot(_) :: LParen(_) :: rest ->
      let (rest, args) = parse_func_call_args ~ind:ind_next rest in
      (rest, ExprInvoke(Undecided, exp, args))

  | _ -> raise Backtrack
  end


(* Parse a UFCS-style call, eg:
  .func_name()
  .other_func(arg1, _, arg3)
  .other_func(arg2, arg3)
*)
and parse_ufcs_call ?(ind="") tokens exp : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  (* .func_name() *)
  | Dot(_) :: LowIdent(_, name) :: LParen(_) :: RParen(_) :: rest ->
      (rest, UfcsCall(Undecided, exp, name, 0, []))

  (* .other_func(arg1, _, arg3) *)
  (* .other_func(arg2, arg2) *)
  | Dot(_) :: LowIdent(_, name) :: LParen(_) :: rest ->
      let (rest, args, underscore_pos) =
        parse_func_call_args_w_underscore ~ind:ind_next rest
      in
      begin match underscore_pos with
      | Some(under_pos) ->
          (rest, UfcsCall(Undecided, exp, name, under_pos, args))

      | None ->
          (rest, UfcsCall(Undecided, exp, name, 0, args))
      end

  | _ -> raise Backtrack
  end


(* Parse indexing into an array, eg:
  [6]
  [val + 5]
*)
and parse_array_index ?(ind="") tokens exp : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LBracket(_) :: rest ->
      let (rest, idx_expr) = parse_expr ~ind:ind_next rest in

      begin match rest with
      | RBracket(_) :: rest ->
          (rest, IndexExpr(Undecided, idx_expr, exp))

      | _ -> raise Backtrack
      end

  | _ -> raise Backtrack
  end


(* Parse indexing into a tuple by constant integer, eg:
  .0
  .3
*)
and parse_tuple_index ?(ind="") tokens exp : (token list * expr) =
  let _ = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | Dot(_) :: Integer(_, i) :: rest ->
      (rest, TupleIndexExpr(Undecided, i, exp))

  | _ -> raise Backtrack
  end


(* Parse dereferencing a variable, ie:
  .*
 *)
and parse_deref ?(ind="") tokens exp : (token list * expr) =
  let _ = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | Dot(_) :: Star(_) :: rest ->
      (rest, DerefOf(Undecided, exp))

  | _ -> raise Backtrack
  end


and parse_array_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  (* Accept empty array-expr. *)
  | LBracket(_) :: RBracket(_) :: rest ->
      (rest, ArrayExpr(Undecided, []))

  | LBracket(_) :: rest ->
      let (rest, init_exp) = parse_expr ~ind:ind_next rest in

      begin match rest with
      (* Accept trailing comma. *)
      | Comma(_) :: RBracket(_) :: rest ->
          (rest, ArrayExpr(Undecided, [init_exp]))

      (* This is at least a 2-element array. *)
      | Comma(_) :: rest ->
          let (rest, pair_exp) = parse_expr ~ind:ind_next rest in

          (* At this point, we want to match 0 or more `, <expr>` sequences,
          followed by a final closing bracket. *)
          let rec _parse_remaining_array rest exprs_so_far =
            begin match rest with
            (* Accept trailing comma. *)
            | Comma(_) :: RBracket(_) :: rest -> (rest, exprs_so_far)

            (* Termination of array expr without trailing comma. *)
            | RBracket(_) :: rest -> (rest, exprs_so_far)

            (* Comma followed by another array expr. *)
            | Comma(_) :: rest ->
                let (rest, next_exp) = parse_expr ~ind:ind_next rest in
                _parse_remaining_array rest (exprs_so_far @ [next_exp])

            | tok :: _ ->
                let fmted = fmt_token tok in
                failwith (
                  Printf.sprintf
                    "Unexpected token [%s] parsing array expr, expected `)`."
                    fmted
                )
            | [] -> failwith "Unexpected EOF while parsing array expr."
            end
          in

          let (rest, remaining_array_exprs) = _parse_remaining_array rest [] in

          (
            rest,
            ArrayExpr(Undecided, [init_exp; pair_exp] @ remaining_array_exprs)
          )

      | _ -> raise Backtrack
      end

  | _ ->
      raise Backtrack
  end


and parse_tuple_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LParen(_) :: rest ->
      let (rest, init_exp) = parse_expr ~ind:ind_next rest in

      (* There must be at least one comma, if this is a tuple. There may be more
      expressions in this tuple, all comma-delimited. As a special case, it's
      valid to spell a 1-tuple via `(<expr>,)`. *)
      begin match rest with
      (* Is this a 1-tuple? *)
      | Comma(_) :: RParen(_) :: rest ->
          (rest, TupleExpr(Undecided, [init_exp]))

      (* This is at least a 2-tuple. *)
      | Comma(_) :: rest ->
          let (rest, pair_exp) = parse_expr ~ind:ind_next rest in

          (* At this point, we want to match 0 or more `, <expr>` sequences,
          followed by a final closing paren. *)
          let rec _parse_remaining_tuple rest exprs_so_far =
            begin match rest with
            | Comma(_) :: rest ->
                let (rest, next_exp) = parse_expr ~ind:ind_next rest in
                _parse_remaining_tuple rest (exprs_so_far @ [next_exp])

            | RParen(_) :: rest -> (rest, exprs_so_far)

            | tok :: _ ->
                let fmted = fmt_token tok in
                failwith (
                  Printf.sprintf
                    "Unexpected token [%s] parsing tuple expr, expected `)`."
                    fmted
                )
            | [] -> failwith "Unexpected EOF while parsing tuple expr."
            end
          in

          let (rest, remaining_tuple_exprs) = _parse_remaining_tuple rest [] in

          (
            rest,
            TupleExpr(Undecided, [init_exp; pair_exp] @ remaining_tuple_exprs)
          )

      | _ -> raise Backtrack
      end

  | _ ->
      raise Backtrack
  end


and parse_paren_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LParen(_) :: rest ->
      let (rest, exp) = parse_expr ~ind:ind_next rest in

      begin match rest with
      | RParen(_) :: rest -> (rest, exp)

      | tok :: _ ->
          let fmted = fmt_token tok in
          failwith (
            Printf.sprintf
              "Unexpected token [%s] parsing parenthesized expr, expected `)`."
              fmted
          )
      | [] -> failwith "Unexpected EOF while parsing parenthesized expr."
      end

  | _ ->
      raise Backtrack
  end


and parse_if_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | KWIf(_) :: rest ->
      let (rest, cond_exp) = parse_expr ~ind:ind_next rest in
      let (rest, then_exp) = parse_expr_block ~ind:ind_next rest in

      let rec _parse_else_chain tokens : (token list * expr) =
        begin match tokens with
        | KWElse(_) :: KWIf(_) :: rest ->
            let (rest, cond_exp) = parse_expr ~ind:ind_next rest in
            let (rest, then_exp) = parse_expr_block ~ind:ind_next rest in
            let (rest, else_exp) = _parse_else_chain rest in

            (rest, IfThenElseExpr(Undecided, cond_exp, then_exp, else_exp))

        | KWElse(_) :: rest ->
            let (rest, else_exp) = parse_expr_block ~ind:ind_next rest in
            (rest, else_exp)

        | _ :: _ ->
            (rest, ValNil)

        | [] -> failwith "Unexpected EOF while parsing if-expr."
        end
      in

      let (rest, else_exp) = _parse_else_chain rest in

      (rest, IfThenElseExpr(Undecided, cond_exp, then_exp, else_exp))

  | _ ->
      raise Backtrack
  end


and parse_if_is_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | KWIf(_) :: rest ->
      let rec _parse_if_is_conds rest conds_rev =
        let (rest, conds_rev) =
          begin try
            let (rest, exp) = parse_if_is_reduced_expr ~ind:ind_next rest in
            begin match rest with
            | KWIs(_) :: rest ->
                let (rest, patt) = parse_pattern ~ind:ind_next rest in
                (rest, IfIsPattern(exp, patt) :: conds_rev)

            | _ ->
                raise Backtrack
            end

          with Backtrack ->
            let (rest, cond_exp) =
              parse_if_is_reduced_expr ~ind:ind_next rest
            in
            (rest, IfIsGeneral(cond_exp) :: conds_rev)
          end
        in
        begin match rest with
        | AmpAmp(_) :: rest ->
            _parse_if_is_conds rest conds_rev

        | _ ->
            (rest, conds_rev)
        end
      in

      let (rest, conds_rev) = _parse_if_is_conds rest [] in

      let conds = List.rev conds_rev in

      let (rest, then_exp) = parse_expr_block ~ind:ind_next rest in

      let _parse_else tokens : (token list * expr) =
        begin match tokens with
        | KWElse(_) :: rest ->
            begin try
              (* Try to chain into another if-expr. *)
              parse_if_expr_general ~ind:ind rest
            with Backtrack ->
              (* Try to parse the final else expr block. *)
              parse_expr_block ~ind:ind_next rest
            end

        | _ :: _ ->
            (rest, ValNil)

        | [] -> failwith "Unexpected EOF while parsing if-expr."
        end
      in

      let (rest, else_exp) = _parse_else rest in

      (rest, IfIsThenElseExpr(Undecided, conds, then_exp, else_exp))

  | _ ->
      raise Backtrack
  end


and parse_while_expr ?(ind="") tokens : (token list * expr) =
  let ind_next = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | KWWhile(_) :: LBrace(_) :: rest ->
      (* `while { <stmts> } <cond-expr> { <stmts> }` *)
      let (rest, init_stmts) = parse_stmts ~ind:ind_next rest in

      begin match rest with
      | RBrace(_) :: rest ->
          let (rest, cond_exp) = parse_expr ~ind:ind_next rest in
          let (rest, loop_exp) = parse_stmt_block ~ind:ind_next rest in

          (rest, WhileExpr(Undecided, init_stmts, cond_exp, loop_exp))

      | _ ->
          failwith "Could not find matching `}` in while-expr init-stmts"
      end

  | KWWhile(_) :: rest ->
      (* `while <cond-expr> { <stmts> }` *)
      let (rest, cond_exp) = parse_expr ~ind:ind_next rest in
      let (rest, loop_exp) = parse_stmt_block ~ind:ind_next rest in

      (rest, WhileExpr(Undecided, [], cond_exp, loop_exp))

  | _ ->
      raise Backtrack
  end


and parse_pattern ?(ind="") tokens : (token list * pattern) =
  let _ = print_trace ind __FUNCTION__ tokens in

  (* Parse eg:
    as <ident>
  *)
  let _parse_pattern_as tokens pattern =
    begin match tokens with
    | KWAs(_) :: LowIdent(_, as_name) :: rest ->
        (rest, PatternAs(Undecided, pattern, as_name))

    | KWAs(_) :: _ ->
        failwith "`as` match pattern requires bind name"

    | _ ->
        (tokens, pattern)
    end
  in

  (* Parse eg:
    , <pattern>, <pattern>, <pattern>)
  *)
  let rec _parse_comma_pattern_multi tokens more_patterns_rev =
    begin match tokens with
    | Comma(_) :: rest ->
        let (rest, next_pattern) = parse_pattern rest in
        let more_patterns_rev' = next_pattern :: more_patterns_rev in
        _parse_comma_pattern_multi rest more_patterns_rev'

    | RParen(_) :: rest ->
        (rest, more_patterns_rev)

    | _ ->
        failwith "Failed to parse comma-delimited patterns in match expr"
    end
  in

  begin match tokens with
  (* Variable bind pattern. *)
  | LowIdent(_, bind_name) :: rest ->
      (rest, VarBind(Undecided, bind_name))

  (* Wildcard pattern. *)
  | Underscore(_) :: rest ->
      let pattern = Wild(Undecided) in
      _parse_pattern_as rest pattern

  | KWTrue(_) :: rest ->
      let pattern = PBool(true) in
      _parse_pattern_as rest pattern

  | KWFalse(_) :: rest ->
      let pattern = PBool(false) in
      _parse_pattern_as rest pattern

  | Integer(_, i) :: DotDot(_) :: Integer(_, j) :: rest ->
      let pattern = PInt(Undecided, IRangeFromUntil(i, j)) in
      _parse_pattern_as rest pattern

  | Integer(_, i) :: DotDot(_) :: rest ->
      let pattern = PInt(Undecided, IRangeAllFrom(i)) in
      _parse_pattern_as rest pattern

  | DotDot(_) :: Integer(_, i) :: rest ->
      let pattern = PInt(Undecided, IRangeAllUntil(i)) in
      _parse_pattern_as rest pattern

  | Integer(_, i) :: rest ->
      let pattern = PInt(Undecided, IRangeLiteral(i)) in
      _parse_pattern_as rest pattern

  (* Tuple pattern. *)
  | LParen(_) :: rest ->
      let (rest, first_pattern) = parse_pattern rest in

      let (rest, more_patterns_rev) = _parse_comma_pattern_multi rest [] in
      let more_patterns = List.rev more_patterns_rev in
      let tuple_sub_patterns = first_pattern :: more_patterns in
      let pattern = PTuple(Undecided, tuple_sub_patterns) in
      _parse_pattern_as rest pattern

  (* Variant deconstruction pattern with fields. *)
  | CapIdent(_, v_name) :: LParen(_) :: rest ->
      let (rest, first_pattern) = parse_pattern rest in

      let (rest, more_patterns_rev) = _parse_comma_pattern_multi rest [] in
      let more_patterns = List.rev more_patterns_rev in
      let ctor_sub_patterns = first_pattern :: more_patterns in
      let pattern = Ctor(Undecided, v_name, ctor_sub_patterns) in
      _parse_pattern_as rest pattern

  (* Variant deconstruction with no fields. *)
  | CapIdent(_, v_name) :: rest ->
      let pattern = Ctor(Undecided, v_name, []) in
      _parse_pattern_as rest pattern

  | _ ->
      failwith "Failed to parse match expr pattern."
  end


and parse_match_expr ?(ind="") tokens : (token list * expr) =
  let _ = print_trace ind __FUNCTION__ tokens in

  (* Parse eg:
    | (Some(x, false, _), false) -> 5
    | (x, true as y) -> 6
    | (_, _) -> 5
  *)
  let _parse_pattern_expr_pairs tokens =
    let rec __parse_pattern_expr_pairs tokens pattern_expr_pairs_rev =
      begin match tokens with
      | Bar(_) :: rest ->
          let (rest, pattern) = parse_pattern rest in

          begin match rest with
          | Arrow(_) :: rest ->
              let (rest, pattern_matched_expr) = parse_expr rest in
              let pattern_expr_pairs_rev' =
                (pattern, pattern_matched_expr) :: pattern_expr_pairs_rev
              in
              __parse_pattern_expr_pairs rest pattern_expr_pairs_rev'

          | _ ->
              failwith "Could not find `->` after pattern in match expr"
          end

      | _ ->
          (tokens, pattern_expr_pairs_rev)
      end
    in

    let (rest, pattern_expr_pairs_rev) = __parse_pattern_expr_pairs tokens [] in
    let pattern_expr_pairs = List.rev pattern_expr_pairs_rev in
    (rest, pattern_expr_pairs)
  in

  (* Parse eg:
    match my_option {
    <pattern_list>
    }
  *)
  begin match tokens with
  | KWMatch(_) :: rest ->
      let (rest, match_expr) = parse_expr rest in

      begin match rest with
      | LBrace(_) :: rest ->
          let (rest, pattern_expr_pairs) = _parse_pattern_expr_pairs rest in

          begin match rest with
          | RBrace(_) :: rest ->
              (rest, MatchExpr(Undecided, match_expr, pattern_expr_pairs))

          | _ ->
              failwith "Could not find matching `}` in match expr"
          end

      | _ ->
          failwith "Could not find opening `{` in match expr"
      end

  | _ -> raise Backtrack
  end


(* Parse a variant constructor expression value. *)
and parse_variant_ctor ?(ind="") tokens : (token list * expr) =
  let _ = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | CapIdent(_, name) :: LParen(_) :: rest ->
      let (rest, first_elem) = parse_expr rest in

      let rec _parse_variant_ctor_elems tokens collected_elems_rev =
        begin match tokens with
        | Comma(_) :: rest ->
            let (rest, next_elem) = parse_expr rest in
            _parse_variant_ctor_elems rest (next_elem :: collected_elems_rev)

        | _ ->
            (tokens, collected_elems_rev)
        end
      in

      let (rest, collected_elems_rev) = _parse_variant_ctor_elems rest [] in
      let collected_elems = List.rev collected_elems_rev in

      let all_elems = first_elem :: collected_elems in

      begin match rest with
      | RParen(_) :: rest ->
          (
            rest,
            VariantCtorExpr(Undecided, name, all_elems)
          )

      | _ ->
          failwith "Could not find matching `)` in variant ctor expr"
      end

  | CapIdent(_, name) :: rest ->
      (rest, VariantCtorExpr(Undecided, name, []))

  | _ -> raise Backtrack
  end


and parse_expr_atom ?(ind="") tokens : (token list * expr) =
  let _ = print_trace ind __FUNCTION__ tokens in

  begin match tokens with
  | LParen(_) :: RParen(_) :: rest -> (rest, ValNil)
  | KWTrue(_) :: rest -> (rest, ValBool(true))
  | KWFalse(_) :: rest -> (rest, ValBool(false))
  | Float(_, num) :: rest -> (rest, ValF64(num))
  | Float32(_, num) :: rest -> (rest, ValF32(num))
  | Float64(_, num) :: rest -> (rest, ValF64(num))
  | Float128(_, num_str) :: rest -> (rest, ValF128(num_str))
  | Integer(_, num) :: rest -> (rest, ValInt(Undecided, num))
  | String(_, str) :: rest -> (rest, ValStr(str))
  | LowIdent(_, name) :: rest -> (rest, ValName(Undecided, name))

  | _ -> raise Backtrack
  end
