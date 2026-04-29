(** Z3 native OCaml API backend.
    Creates a fresh Z3 context and incremental solver, translates Sexplib0.Sexp.t
    expressions to Z3 terms internally. *)

open Smtlib_output

let make_solver timeout_ms : solver =
  let ctx = Z3.mk_context [] in
  let slv = Z3.Solver.mk_simple_solver ctx in

  if timeout_ms >= 0 then begin
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout_ms;
    Z3.Solver.set_parameters slv params
  end;

  let hist     = Buffer.create 4096 in
  let var_syms : (string, Z3.Expr.expr) Hashtbl.t = Hashtbl.create 64 in

  (* ------------------------------------------------------------------ *)
  (* Sort parser                                                         *)
  (* ------------------------------------------------------------------ *)

  let parse_sort sexp =
    match sexp with
    | Sexplib0.Sexp.Atom "Bool" -> Z3.Boolean.mk_sort ctx
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom "BitVec";
                          Sexplib0.Sexp.Atom n] ->
        Z3.BitVector.mk_sort ctx (int_of_string n)
    | s ->
        failwith ("z3: unsupported sort: " ^ sexp_to_smtlib s)
  in

  (* ------------------------------------------------------------------ *)
  (* Term parser                                                         *)
  (* ------------------------------------------------------------------ *)

  let rec parse_term sexp =
    match sexp with

    (* Boolean constants *)
    | Sexplib0.Sexp.Atom "true"  -> Z3.Boolean.mk_true ctx
    | Sexplib0.Sexp.Atom "false" -> Z3.Boolean.mk_false ctx

    (* Inline indexed literal atom: "(_ bvN M)" collapsed into one atom *)
    | Sexplib0.Sexp.Atom name when String.starts_with ~prefix:"(_" name ->
        (match String.split_on_char ' ' name with
        | [_; bvlit; size_s] ->
            let value = String.sub bvlit 2 (String.length bvlit - 2) in
            let size  = int_of_string (String.sub size_s 0 (String.length size_s - 1)) in
            Z3.BitVector.mk_numeral ctx value size
        | _ -> failwith ("z3: bad literal atom: " ^ name))

    (* Variable lookup *)
    | Sexplib0.Sexp.Atom name ->
        (match Hashtbl.find_opt var_syms name with
         | Some t -> t
         | None   -> failwith ("z3: unknown symbol: " ^ name))

    (* Indexed BV literal  (_ bvN M) — value N in decimal, width M *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom bvlit;
                          Sexplib0.Sexp.Atom size_s]
      when String.starts_with ~prefix:"bv" bvlit ->
        let value = String.sub bvlit 2 (String.length bvlit - 2) in
        let size  = int_of_string size_s in
        Z3.BitVector.mk_numeral ctx value size

    (* Boolean operators *)
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
        Z3.Boolean.mk_and ctx (List.map parse_term args)

    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: args) ->
        Z3.Boolean.mk_or ctx (List.map parse_term args)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; a] ->
        Z3.Boolean.mk_not ctx (parse_term a)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>"; a; b] ->
        Z3.Boolean.mk_implies ctx (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "xor"; a; b] ->
        Z3.Boolean.mk_xor ctx (parse_term a) (parse_term b)

    (* Equality, ITE, distinct *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; a; b] ->
        Z3.Boolean.mk_eq ctx (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "distinct"; a; b] ->
        Z3.Boolean.mk_distinct ctx [parse_term a; parse_term b]

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite"; c; t; e] ->
        Z3.Boolean.mk_ite ctx (parse_term c) (parse_term t) (parse_term e)

    (* BV arithmetic *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvadd";  a; b] -> Z3.BitVector.mk_add  ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsub";  a; b] -> Z3.BitVector.mk_sub  ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvmul";  a; b] -> Z3.BitVector.mk_mul  ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvudiv"; a; b] -> Z3.BitVector.mk_udiv ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvurem"; a; b] -> Z3.BitVector.mk_urem ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsdiv"; a; b] -> Z3.BitVector.mk_sdiv ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsrem"; a; b] -> Z3.BitVector.mk_srem ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsmod"; a; b] -> Z3.BitVector.mk_smod ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvneg";  a]    -> Z3.BitVector.mk_neg  ctx (parse_term a)

    (* BV bitwise *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvand";  a; b] -> Z3.BitVector.mk_and  ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvor";   a; b] -> Z3.BitVector.mk_or   ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxor";  a; b] -> Z3.BitVector.mk_xor  ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnand"; a; b] -> Z3.BitVector.mk_nand ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnor";  a; b] -> Z3.BitVector.mk_nor  ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxnor"; a; b] -> Z3.BitVector.mk_xnor ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnot";  a]    -> Z3.BitVector.mk_not  ctx (parse_term a)

    (* BV shifts *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvshl";  a; b] -> Z3.BitVector.mk_shl  ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvashr"; a; b] -> Z3.BitVector.mk_ashr ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvlshr"; a; b] -> Z3.BitVector.mk_lshr ctx (parse_term a) (parse_term b)

    (* BV comparisons — all return Bool *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvult";  a; b] -> Z3.BitVector.mk_ult ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvule";  a; b] -> Z3.BitVector.mk_ule ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvugt";  a; b] -> Z3.BitVector.mk_ugt ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvuge";  a; b] -> Z3.BitVector.mk_uge ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvslt";  a; b] -> Z3.BitVector.mk_slt ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsle";  a; b] -> Z3.BitVector.mk_sle ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsgt";  a; b] -> Z3.BitVector.mk_sgt ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsge";  a; b] -> Z3.BitVector.mk_sge ctx (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvcomp"; a; b] -> Z3.Boolean.mk_eq    ctx (parse_term a) (parse_term b)

    (* BV concat *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "concat"; a; b] ->
        Z3.BitVector.mk_concat ctx (parse_term a) (parse_term b)

    (* Indexed: (_ extract hi lo) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "extract";
                             Sexplib0.Sexp.Atom hi_s;
                             Sexplib0.Sexp.Atom lo_s]; a] ->
        Z3.BitVector.mk_extract ctx (int_of_string hi_s) (int_of_string lo_s) (parse_term a)

    (* Indexed: (_ zero_extend n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "zero_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_zero_ext ctx (int_of_string n_s) (parse_term a)

    (* Indexed: (_ sign_extend n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "sign_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_sign_ext ctx (int_of_string n_s) (parse_term a)

    (* Indexed: (_ rotate_left n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_left";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_rotate_left ctx (int_of_string n_s) (parse_term a)

    (* Indexed: (_ rotate_right n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_right";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_rotate_right ctx (int_of_string n_s) (parse_term a)

    (* Indexed: (_ repeat n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "repeat";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_repeat ctx (int_of_string n_s) (parse_term a)

    | s ->
        failwith ("z3: unsupported term: " ^ sexp_to_smtlib s)
  in

  (* ------------------------------------------------------------------ *)
  (* Declaration helpers                                                 *)
  (* ------------------------------------------------------------------ *)

  let do_declare_const name sort_sexp =
    let sort = parse_sort sort_sexp in
    let t = Z3.Expr.mk_const_s ctx name sort in
    Hashtbl.replace var_syms name t;
    Buffer.add_string hist
      (Printf.sprintf "(declare-const %s %s)\n" name (sexp_to_smtlib sort_sexp))
  in

  let do_fun_def ty name defs =
    Buffer.add_string hist
      (let kw = match ty with `Def -> "define-fun" | `Decl -> "declare-fun" in
       Printf.sprintf "(%s %s %s)\n" kw name
         (String.concat " " (List.map sexp_to_smtlib defs)));
    match ty with
    | `Decl ->
        (match defs with
         | [arg_list_sexp; ret_sort_sexp] ->
             (match arg_list_sexp with
              | Sexplib0.Sexp.List [] ->
                  let sort = parse_sort ret_sort_sexp in
                  let t = Z3.Expr.mk_const_s ctx name sort in
                  Hashtbl.replace var_syms name t
              | _ ->
                  failwith ("z3: declare-fun with arguments (UF) not supported: " ^ name))
         | _ -> failwith "z3: declare-fun: unexpected defs format")
    | `Def ->
        (match defs with
         | [arg_bindings_sexp; _ret_sort_sexp; body_sexp] ->
             (match arg_bindings_sexp with
              | Sexplib0.Sexp.List [] ->
                  let t = parse_term body_sexp in
                  Hashtbl.replace var_syms name t
              | _ ->
                  failwith ("z3: define-fun with arguments not supported: " ^ name))
         | _ -> failwith "z3: define-fun: unexpected defs format")
  in

  (* ------------------------------------------------------------------ *)
  (* check_sat                                                           *)
  (* ------------------------------------------------------------------ *)

  let do_check_sat () =
    Buffer.add_string hist "(check-sat)\n";
    match Z3.Solver.check slv [] with
    | Z3.Solver.SATISFIABLE   -> "sat"
    | Z3.Solver.UNSATISFIABLE -> "unsat"
    | Z3.Solver.UNKNOWN       -> "unknown"
  in

  (* ------------------------------------------------------------------ *)
  (* solver record                                                       *)
  (* ------------------------------------------------------------------ *)

  {
    name          = "z3";
    set_logic     = (fun l ->
      Buffer.add_string hist (Printf.sprintf "(set-logic %s)\n" l));
    set_option    = (fun k v ->
      Buffer.add_string hist (Printf.sprintf "(set-option %s %s)\n" k v));
    declare_const = do_declare_const;
    fun_def       = do_fun_def;
    assert_       = (fun e ->
      Buffer.add_string hist (Printf.sprintf "(assert %s)\n" (sexp_to_smtlib e));
      Z3.Solver.add slv [parse_term e]);
    assert_named  = (fun nm e ->
      Buffer.add_string hist
        (Printf.sprintf "(assert (! %s :named %s))\n" (sexp_to_smtlib e) nm);
      Z3.Solver.add slv [parse_term e]);
    push          = (fun () ->
      Buffer.add_string hist "(push)\n";
      Z3.Solver.push slv);
    pop           = (fun () ->
      Buffer.add_string hist "(pop)\n";
      Z3.Solver.pop slv 1);
    interrupt     = (fun () -> 
      try 
        Z3.Solver.interrupt ctx slv
    with _ ->
      ()
    );
    check_sat     = do_check_sat;
    history       = (fun () -> Buffer.contents hist);
    close         = (fun () -> ());
  }

(* ------------------------------------------------------------------ *)
(* Module interface                                                     *)
(* ------------------------------------------------------------------ *)

module Z3_solver : Solver.Solver = struct
  type t = {
    ctx      : Z3.context;
    slv      : Z3.Solver.solver;
    var_syms : (string, Z3.Expr.expr) Hashtbl.t;
  }

  let build () =
    let ctx = Z3.mk_context [] in
    let slv = Z3.Solver.mk_simple_solver ctx in
    { ctx; slv; var_syms = Hashtbl.create 64 }

  let set_timeout t ms =
    let params = Z3.Params.mk_params t.ctx in
    Z3.Params.add_int params (Z3.Symbol.mk_string t.ctx "timeout") ms;
    Z3.Solver.set_parameters t.slv params

  let set_logic _t _l = ()

  let set_option _t _k _v = ()

  let parse_sort t sexp =
    match sexp with
    | Sexplib0.Sexp.Atom "Bool" -> Z3.Boolean.mk_sort t.ctx
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom "BitVec";
                          Sexplib0.Sexp.Atom n] ->
        Z3.BitVector.mk_sort t.ctx (int_of_string n)
    | s ->
        failwith ("z3: unsupported sort: " ^ sexp_to_smtlib s)

  let rec parse_term t sexp =
    let ctx = t.ctx in
    match sexp with
    | Sexplib0.Sexp.Atom "true"  -> Z3.Boolean.mk_true ctx
    | Sexplib0.Sexp.Atom "false" -> Z3.Boolean.mk_false ctx
    | Sexplib0.Sexp.Atom name when String.starts_with ~prefix:"(_" name ->
        (match String.split_on_char ' ' name with
        | [_; bvlit; size_s] ->
            let value = String.sub bvlit 2 (String.length bvlit - 2) in
            let size  = int_of_string (String.sub size_s 0 (String.length size_s - 1)) in
            Z3.BitVector.mk_numeral ctx value size
        | _ -> failwith ("z3: bad literal atom: " ^ name))
    | Sexplib0.Sexp.Atom name ->
        (match Hashtbl.find_opt t.var_syms name with
         | Some term -> term
         | None      -> failwith ("z3: unknown symbol: " ^ name))
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom bvlit;
                          Sexplib0.Sexp.Atom size_s]
      when String.starts_with ~prefix:"bv" bvlit ->
        let value = String.sub bvlit 2 (String.length bvlit - 2) in
        let size  = int_of_string size_s in
        Z3.BitVector.mk_numeral ctx value size
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
        Z3.Boolean.mk_and ctx (List.map (parse_term t) args)
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: args) ->
        Z3.Boolean.mk_or ctx (List.map (parse_term t) args)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; a] ->
        Z3.Boolean.mk_not ctx (parse_term t a)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>"; a; b] ->
        Z3.Boolean.mk_implies ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "xor"; a; b] ->
        Z3.Boolean.mk_xor ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; a; b] ->
        Z3.Boolean.mk_eq ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "distinct"; a; b] ->
        Z3.Boolean.mk_distinct ctx [parse_term t a; parse_term t b]
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite"; c; th; el] ->
        Z3.Boolean.mk_ite ctx (parse_term t c) (parse_term t th) (parse_term t el)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvadd";  a; b] -> Z3.BitVector.mk_add  ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsub";  a; b] -> Z3.BitVector.mk_sub  ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvmul";  a; b] -> Z3.BitVector.mk_mul  ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvudiv"; a; b] -> Z3.BitVector.mk_udiv ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvurem"; a; b] -> Z3.BitVector.mk_urem ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsdiv"; a; b] -> Z3.BitVector.mk_sdiv ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsrem"; a; b] -> Z3.BitVector.mk_srem ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsmod"; a; b] -> Z3.BitVector.mk_smod ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvneg";  a]    -> Z3.BitVector.mk_neg  ctx (parse_term t a)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvand";  a; b] -> Z3.BitVector.mk_and  ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvor";   a; b] -> Z3.BitVector.mk_or   ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxor";  a; b] -> Z3.BitVector.mk_xor  ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnand"; a; b] -> Z3.BitVector.mk_nand ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnor";  a; b] -> Z3.BitVector.mk_nor  ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxnor"; a; b] -> Z3.BitVector.mk_xnor ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnot";  a]    -> Z3.BitVector.mk_not  ctx (parse_term t a)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvshl";  a; b] -> Z3.BitVector.mk_shl  ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvashr"; a; b] -> Z3.BitVector.mk_ashr ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvlshr"; a; b] -> Z3.BitVector.mk_lshr ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvult";  a; b] -> Z3.BitVector.mk_ult ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvule";  a; b] -> Z3.BitVector.mk_ule ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvugt";  a; b] -> Z3.BitVector.mk_ugt ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvuge";  a; b] -> Z3.BitVector.mk_uge ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvslt";  a; b] -> Z3.BitVector.mk_slt ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsle";  a; b] -> Z3.BitVector.mk_sle ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsgt";  a; b] -> Z3.BitVector.mk_sgt ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsge";  a; b] -> Z3.BitVector.mk_sge ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvcomp"; a; b] -> Z3.Boolean.mk_eq    ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "concat"; a; b] ->
        Z3.BitVector.mk_concat ctx (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "extract";
                             Sexplib0.Sexp.Atom hi_s;
                             Sexplib0.Sexp.Atom lo_s]; a] ->
        Z3.BitVector.mk_extract ctx (int_of_string hi_s) (int_of_string lo_s) (parse_term t a)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "zero_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_zero_ext ctx (int_of_string n_s) (parse_term t a)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "sign_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_sign_ext ctx (int_of_string n_s) (parse_term t a)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_left";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_rotate_left ctx (int_of_string n_s) (parse_term t a)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_right";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_rotate_right ctx (int_of_string n_s) (parse_term t a)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "repeat";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        Z3.BitVector.mk_repeat ctx (int_of_string n_s) (parse_term t a)
    | s ->
        failwith ("z3: unsupported term: " ^ sexp_to_smtlib s)

  let declare_const t name sort_sexp =
    let sort = parse_sort t sort_sexp in
    let term = Z3.Expr.mk_const_s t.ctx name sort in
    Hashtbl.replace t.var_syms name term

  let add t sexp =
    Z3.Solver.add t.slv [parse_term t sexp]

  let push t =
    Z3.Solver.push t.slv

  let pop t =
    Z3.Solver.pop t.slv 1

  let check_sat t =
    match Z3.Solver.check t.slv [] with
    | Z3.Solver.SATISFIABLE   -> Solver.Sat
    | Z3.Solver.UNSATISFIABLE -> Solver.Unsat
    | Z3.Solver.UNKNOWN       -> Solver.Unknown

  let interrupt t =
    (try Z3.Solver.interrupt t.ctx t.slv with _ -> ())

  let close _t = ()
end
