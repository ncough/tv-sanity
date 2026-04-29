(** CVC5 native OCaml API backend.
    Creates a fresh CVC5 TermManager and Solver, translates Sexplib0.Sexp.t
    expressions to CVC5 terms internally. *)

open Smtlib_output

let make_solver timeout_ms : solver =
  let tm  = Cvc5.TermManager.mk_tm () in
  let slv = Cvc5.Solver.mk_solver tm in

  Cvc5.Solver.set_option slv "incremental" "true";
  if timeout_ms >= 0 then
    Cvc5.Solver.set_option slv "tlimit-per" (string_of_int timeout_ms);

  let hist     = Buffer.create 4096 in
  let var_syms : (string, Cvc5.Term.term) Hashtbl.t = Hashtbl.create 64 in

  (* ------------------------------------------------------------------ *)
  (* Sort parser                                                         *)
  (* ------------------------------------------------------------------ *)

  let parse_sort sexp =
    match sexp with
    | Sexplib0.Sexp.Atom "Bool" -> Cvc5.Sort.mk_bool_sort tm
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom "BitVec";
                          Sexplib0.Sexp.Atom n] ->
        Cvc5.Sort.mk_bv_sort tm (int_of_string n)
    | s ->
        failwith ("cvc5: unsupported sort: " ^ sexp_to_smtlib s)
  in

  (* ------------------------------------------------------------------ *)
  (* Term parser                                                         *)
  (* ------------------------------------------------------------------ *)

  let mk1 k a     = Cvc5.Term.mk_term_1 tm k a in
  let mk2 k a b   = Cvc5.Term.mk_term_2 tm k a b in
  let mk3 k a b c = Cvc5.Term.mk_term_3 tm k a b c in
  let mkn k args  = Cvc5.Term.mk_term   tm k (Array.of_list args) in
  let mko op args = Cvc5.Term.mk_term_op tm op (Array.of_list args) in
  let op k idxs   = Cvc5.Op.mk_op tm k (Array.of_list idxs) in

  let rec parse_term sexp =
    match sexp with

    (* Boolean constants *)
    | Sexplib0.Sexp.Atom "true"  -> Cvc5.Term.mk_true tm
    | Sexplib0.Sexp.Atom "false" -> Cvc5.Term.mk_false tm

    (* Inline indexed literal atom: "(_ bvN M)" collapsed into one atom *)
    | Sexplib0.Sexp.Atom name when String.starts_with ~prefix:"(_" name ->
        (match String.split_on_char ' ' name with
        | [_; bvlit; size_s] ->
            let value = String.sub bvlit 2 (String.length bvlit - 2) in
            let size  = int_of_string (String.sub size_s 0 (String.length size_s - 1)) in
            Cvc5.Term.mk_bv_s tm size value 10
        | _ -> failwith ("cvc5: bad literal atom: " ^ name))

    (* Variable lookup *)
    | Sexplib0.Sexp.Atom name ->
        (match Hashtbl.find_opt var_syms name with
         | Some t -> t
         | None   -> failwith ("cvc5: unknown symbol: " ^ name))

    (* Indexed BV literal  (_ bvN M) — value N in decimal, width M *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom bvlit;
                          Sexplib0.Sexp.Atom size_s]
      when String.starts_with ~prefix:"bv" bvlit ->
        let value = String.sub bvlit 2 (String.length bvlit - 2) in
        let size  = int_of_string size_s in
        Cvc5.Term.mk_bv_s tm size value 10

    (* Boolean operators *)
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
        mkn Cvc5.Kind.And (List.map parse_term args)

    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: args) ->
        mkn Cvc5.Kind.Or (List.map parse_term args)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; a] ->
        mk1 Cvc5.Kind.Not (parse_term a)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>"; a; b] ->
        mk2 Cvc5.Kind.Implies (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "xor"; a; b] ->
        mk2 Cvc5.Kind.Xor (parse_term a) (parse_term b)

    (* Equality, ITE, distinct *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; a; b] ->
        mk2 Cvc5.Kind.Equal (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "distinct"; a; b] ->
        mk2 Cvc5.Kind.Distinct (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite"; c; t; e] ->
        mk3 Cvc5.Kind.Ite (parse_term c) (parse_term t) (parse_term e)

    (* BV arithmetic *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvadd";  a; b] -> mk2 Cvc5.Kind.Bitvector_add  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsub";  a; b] -> mk2 Cvc5.Kind.Bitvector_sub  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvmul";  a; b] -> mk2 Cvc5.Kind.Bitvector_mult (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvudiv"; a; b] -> mk2 Cvc5.Kind.Bitvector_udiv (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvurem"; a; b] -> mk2 Cvc5.Kind.Bitvector_urem (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsdiv"; a; b] -> mk2 Cvc5.Kind.Bitvector_sdiv (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsrem"; a; b] -> mk2 Cvc5.Kind.Bitvector_srem (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsmod"; a; b] -> mk2 Cvc5.Kind.Bitvector_smod (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvneg";  a]    -> mk1 Cvc5.Kind.Bitvector_neg  (parse_term a)

    (* BV bitwise *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvand";  a; b] -> mk2 Cvc5.Kind.Bitvector_and  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvor";   a; b] -> mk2 Cvc5.Kind.Bitvector_or   (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxor";  a; b] -> mk2 Cvc5.Kind.Bitvector_xor  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnand"; a; b] -> mk2 Cvc5.Kind.Bitvector_nand (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnor";  a; b] -> mk2 Cvc5.Kind.Bitvector_nor  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxnor"; a; b] -> mk2 Cvc5.Kind.Bitvector_xnor (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnot";  a]    -> mk1 Cvc5.Kind.Bitvector_not  (parse_term a)

    (* BV shifts *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvshl";  a; b] -> mk2 Cvc5.Kind.Bitvector_shl  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvashr"; a; b] -> mk2 Cvc5.Kind.Bitvector_ashr (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvlshr"; a; b] -> mk2 Cvc5.Kind.Bitvector_lshr (parse_term a) (parse_term b)

    (* BV comparisons — all return Bool *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvult";  a; b] -> mk2 Cvc5.Kind.Bitvector_ult  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvule";  a; b] -> mk2 Cvc5.Kind.Bitvector_ule  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvugt";  a; b] -> mk2 Cvc5.Kind.Bitvector_ugt  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvuge";  a; b] -> mk2 Cvc5.Kind.Bitvector_uge  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvslt";  a; b] -> mk2 Cvc5.Kind.Bitvector_slt  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsle";  a; b] -> mk2 Cvc5.Kind.Bitvector_sle  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsgt";  a; b] -> mk2 Cvc5.Kind.Bitvector_sgt  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsge";  a; b] -> mk2 Cvc5.Kind.Bitvector_sge  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvcomp"; a; b] -> mk2 Cvc5.Kind.Bitvector_comp (parse_term a) (parse_term b)

    (* BV concat *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "concat"; a; b] ->
        mk2 Cvc5.Kind.Bitvector_concat (parse_term a) (parse_term b)

    (* Indexed: (_ extract hi lo) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "extract";
                             Sexplib0.Sexp.Atom hi_s;
                             Sexplib0.Sexp.Atom lo_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_extract [int_of_string hi_s; int_of_string lo_s])
            [parse_term a]

    (* Indexed: (_ zero_extend n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "zero_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_zero_extend [int_of_string n_s]) [parse_term a]

    (* Indexed: (_ sign_extend n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "sign_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_sign_extend [int_of_string n_s]) [parse_term a]

    (* Indexed: (_ rotate_left n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_left";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_rotate_left [int_of_string n_s]) [parse_term a]

    (* Indexed: (_ rotate_right n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_right";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_rotate_right [int_of_string n_s]) [parse_term a]

    (* Indexed: (_ repeat n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "repeat";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_repeat [int_of_string n_s]) [parse_term a]

    | s ->
        failwith ("cvc5: unsupported term: " ^ sexp_to_smtlib s)
  in

  (* ------------------------------------------------------------------ *)
  (* Declaration helpers                                                 *)
  (* ------------------------------------------------------------------ *)

  let do_declare_const name sort_sexp =
    let sort = parse_sort sort_sexp in
    let t = Cvc5.Term.mk_const_s tm sort name in
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
                  let t = Cvc5.Term.mk_const_s tm sort name in
                  Hashtbl.replace var_syms name t
              | _ ->
                  failwith ("cvc5: declare-fun with arguments (UF) not supported: " ^ name))
         | _ -> failwith "cvc5: declare-fun: unexpected defs format")
    | `Def ->
        (match defs with
         | [arg_bindings_sexp; _ret_sort_sexp; body_sexp] ->
             (match arg_bindings_sexp with
              | Sexplib0.Sexp.List [] ->
                  let t = parse_term body_sexp in
                  Hashtbl.replace var_syms name t
              | _ ->
                  failwith ("cvc5: define-fun with arguments not supported: " ^ name))
         | _ -> failwith "cvc5: define-fun: unexpected defs format")
  in

  (* ------------------------------------------------------------------ *)
  (* check_sat                                                           *)
  (* ------------------------------------------------------------------ *)

  let do_check_sat () =
    Buffer.add_string hist "(check-sat)\n";
    let r = Cvc5.Solver.check_sat slv in
    if      Cvc5.Result.is_sat     r then "sat"
    else if Cvc5.Result.is_unsat   r then "unsat"
    else                                 "unknown"
  in

  (* ------------------------------------------------------------------ *)
  (* solver record                                                       *)
  (* ------------------------------------------------------------------ *)

  {
    name          = "cvc5";
    set_logic     = (fun l ->
      Cvc5.Solver.set_logic slv l;
      Buffer.add_string hist (Printf.sprintf "(set-logic %s)\n" l));
    set_option    = (fun k v ->
      Cvc5.Solver.set_option slv k v;
      Buffer.add_string hist (Printf.sprintf "(set-option %s %s)\n" k v));
    declare_const = do_declare_const;
    fun_def       = do_fun_def;
    assert_       = (fun e ->
      Buffer.add_string hist (Printf.sprintf "(assert %s)\n" (sexp_to_smtlib e));
      Cvc5.Solver.assert_formula slv (parse_term e));
    assert_named  = (fun nm e ->
      Buffer.add_string hist
        (Printf.sprintf "(assert (! %s :named %s))\n" (sexp_to_smtlib e) nm);
      Cvc5.Solver.assert_formula slv (parse_term e));
    push          = (fun () ->
      Buffer.add_string hist "(push)\n";
      Cvc5.Solver.push slv 1);
    pop           = (fun () ->
      Buffer.add_string hist "(pop)\n";
      Cvc5.Solver.pop slv 1);
    interrupt     = (fun () -> ());
    check_sat     = do_check_sat;
    history       = (fun () -> Buffer.contents hist);
    close         = (fun () -> Cvc5.Solver.delete slv; Cvc5.TermManager.delete tm);
  }

(* ------------------------------------------------------------------ *)
(* Module interface                                                     *)
(* ------------------------------------------------------------------ *)

module Cvc5_solver : Solver.Solver = struct
  type t = {
    tm       : Cvc5.TermManager.tm;
    slv      : Cvc5.Solver.solver;
    var_syms : (string, Cvc5.Term.term) Hashtbl.t;
  }

  let build () =
    let tm  = Cvc5.TermManager.mk_tm () in
    let slv = Cvc5.Solver.mk_solver tm in
    Cvc5.Solver.set_option slv "incremental" "true";
    { tm; slv; var_syms = Hashtbl.create 64 }

  let set_timeout t ms =
    Cvc5.Solver.set_option t.slv "tlimit-per" (string_of_int ms)

  let set_logic t l =
    Cvc5.Solver.set_logic t.slv l

  let set_option t k v =
    Cvc5.Solver.set_option t.slv k v

  let parse_sort t sexp =
    match sexp with
    | Sexplib0.Sexp.Atom "Bool" -> Cvc5.Sort.mk_bool_sort t.tm
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom "BitVec";
                          Sexplib0.Sexp.Atom n] ->
        Cvc5.Sort.mk_bv_sort t.tm (int_of_string n)
    | s ->
        failwith ("cvc5: unsupported sort: " ^ sexp_to_smtlib s)

  let rec parse_term t sexp =
    let tm = t.tm in
    let mk1 k a     = Cvc5.Term.mk_term_1 tm k a in
    let mk2 k a b   = Cvc5.Term.mk_term_2 tm k a b in
    let mk3 k a b c = Cvc5.Term.mk_term_3 tm k a b c in
    let mkn k args  = Cvc5.Term.mk_term   tm k (Array.of_list args) in
    let mko op args = Cvc5.Term.mk_term_op tm op (Array.of_list args) in
    let op k idxs   = Cvc5.Op.mk_op tm k (Array.of_list idxs) in
    match sexp with
    | Sexplib0.Sexp.Atom "true"  -> Cvc5.Term.mk_true tm
    | Sexplib0.Sexp.Atom "false" -> Cvc5.Term.mk_false tm
    | Sexplib0.Sexp.Atom name when String.starts_with ~prefix:"(_" name ->
        (match String.split_on_char ' ' name with
        | [_; bvlit; size_s] ->
            let value = String.sub bvlit 2 (String.length bvlit - 2) in
            let size  = int_of_string (String.sub size_s 0 (String.length size_s - 1)) in
            Cvc5.Term.mk_bv_s tm size value 10
        | _ -> failwith ("cvc5: bad literal atom: " ^ name))
    | Sexplib0.Sexp.Atom name ->
        (match Hashtbl.find_opt t.var_syms name with
         | Some term -> term
         | None      -> failwith ("cvc5: unknown symbol: " ^ name))
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom bvlit;
                          Sexplib0.Sexp.Atom size_s]
      when String.starts_with ~prefix:"bv" bvlit ->
        let value = String.sub bvlit 2 (String.length bvlit - 2) in
        let size  = int_of_string size_s in
        Cvc5.Term.mk_bv_s tm size value 10
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
        mkn Cvc5.Kind.And (List.map (parse_term t) args)
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: args) ->
        mkn Cvc5.Kind.Or (List.map (parse_term t) args)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; a] ->
        mk1 Cvc5.Kind.Not (parse_term t a)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>"; a; b] ->
        mk2 Cvc5.Kind.Implies (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "xor"; a; b] ->
        mk2 Cvc5.Kind.Xor (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; a; b] ->
        mk2 Cvc5.Kind.Equal (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "distinct"; a; b] ->
        mk2 Cvc5.Kind.Distinct (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite"; c; th; el] ->
        mk3 Cvc5.Kind.Ite (parse_term t c) (parse_term t th) (parse_term t el)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvadd";  a; b] -> mk2 Cvc5.Kind.Bitvector_add  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsub";  a; b] -> mk2 Cvc5.Kind.Bitvector_sub  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvmul";  a; b] -> mk2 Cvc5.Kind.Bitvector_mult (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvudiv"; a; b] -> mk2 Cvc5.Kind.Bitvector_udiv (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvurem"; a; b] -> mk2 Cvc5.Kind.Bitvector_urem (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsdiv"; a; b] -> mk2 Cvc5.Kind.Bitvector_sdiv (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsrem"; a; b] -> mk2 Cvc5.Kind.Bitvector_srem (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsmod"; a; b] -> mk2 Cvc5.Kind.Bitvector_smod (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvneg";  a]    -> mk1 Cvc5.Kind.Bitvector_neg  (parse_term t a)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvand";  a; b] -> mk2 Cvc5.Kind.Bitvector_and  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvor";   a; b] -> mk2 Cvc5.Kind.Bitvector_or   (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxor";  a; b] -> mk2 Cvc5.Kind.Bitvector_xor  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnand"; a; b] -> mk2 Cvc5.Kind.Bitvector_nand (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnor";  a; b] -> mk2 Cvc5.Kind.Bitvector_nor  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxnor"; a; b] -> mk2 Cvc5.Kind.Bitvector_xnor (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnot";  a]    -> mk1 Cvc5.Kind.Bitvector_not  (parse_term t a)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvshl";  a; b] -> mk2 Cvc5.Kind.Bitvector_shl  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvashr"; a; b] -> mk2 Cvc5.Kind.Bitvector_ashr (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvlshr"; a; b] -> mk2 Cvc5.Kind.Bitvector_lshr (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvult";  a; b] -> mk2 Cvc5.Kind.Bitvector_ult  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvule";  a; b] -> mk2 Cvc5.Kind.Bitvector_ule  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvugt";  a; b] -> mk2 Cvc5.Kind.Bitvector_ugt  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvuge";  a; b] -> mk2 Cvc5.Kind.Bitvector_uge  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvslt";  a; b] -> mk2 Cvc5.Kind.Bitvector_slt  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsle";  a; b] -> mk2 Cvc5.Kind.Bitvector_sle  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsgt";  a; b] -> mk2 Cvc5.Kind.Bitvector_sgt  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsge";  a; b] -> mk2 Cvc5.Kind.Bitvector_sge  (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvcomp"; a; b] -> mk2 Cvc5.Kind.Bitvector_comp (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "concat"; a; b] ->
        mk2 Cvc5.Kind.Bitvector_concat (parse_term t a) (parse_term t b)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "extract";
                             Sexplib0.Sexp.Atom hi_s;
                             Sexplib0.Sexp.Atom lo_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_extract [int_of_string hi_s; int_of_string lo_s])
            [parse_term t a]
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "zero_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_zero_extend [int_of_string n_s]) [parse_term t a]
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "sign_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_sign_extend [int_of_string n_s]) [parse_term t a]
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_left";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_rotate_left [int_of_string n_s]) [parse_term t a]
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_right";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_rotate_right [int_of_string n_s]) [parse_term t a]
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "repeat";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        mko (op Cvc5.Kind.Bitvector_repeat [int_of_string n_s]) [parse_term t a]
    | s ->
        failwith ("cvc5: unsupported term: " ^ sexp_to_smtlib s)

  let declare_const t name sort_sexp =
    let sort = parse_sort t sort_sexp in
    let term = Cvc5.Term.mk_const_s t.tm sort name in
    Hashtbl.replace t.var_syms name term

  let add t sexp =
    Cvc5.Solver.assert_formula t.slv (parse_term t sexp)

  let push t =
    Cvc5.Solver.push t.slv 1

  let pop t =
    Cvc5.Solver.pop t.slv 1

  let check_sat t =
    let r = Cvc5.Solver.check_sat t.slv in
    if      Cvc5.Result.is_sat   r then Solver.Sat
    else if Cvc5.Result.is_unsat r then Solver.Unsat
    else                                Solver.Unknown

  let interrupt _t = ()

  let close t =
    Cvc5.Solver.delete t.slv;
    Cvc5.TermManager.delete t.tm
end
