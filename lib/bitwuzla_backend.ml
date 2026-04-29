(** Bitwuzla native OCaml API backend.
    Creates a fresh Incremental() session per solver, translates Sexplib0.Sexp.t
    expressions to Bitwuzla terms internally. *)

open Smtlib_output

(** Build a solver record backed by a fresh Bitwuzla Incremental session.
    [timeout_ms] is applied per check_sat call; pass [< 0] for no timeout. *)
let make_solver timeout_ms : solver =
  let module BW = Bitwuzla.Incremental() in

  let hist        = Buffer.create 4096 in
  let timeout_s   = float_of_int timeout_ms /. 1000. in
  let interrupted = ref 0 in

  (* symbol tables — phantom types erased with Obj for UF terms *)
  let var_syms : (string, BW.bv BW.term)  Hashtbl.t = Hashtbl.create 64 in
  let fn_syms  : (string, int * Obj.t)    Hashtbl.t = Hashtbl.create  8 in

  (* ------------------------------------------------------------------ *)
  (* Sort parser                                                         *)
  (* ------------------------------------------------------------------ *)

  let parse_sort sexp =
    match sexp with
    | Sexplib0.Sexp.Atom "Bool" -> BW.Sort.bool
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom "BitVec";
                          Sexplib0.Sexp.Atom n] ->
        BW.Sort.bv (int_of_string n)
    | s ->
        failwith ("bitwuzla: unsupported sort: " ^ sexp_to_smtlib s)
  in

  (* ------------------------------------------------------------------ *)
  (* UF application — arity-specific dispatch via Obj.magic             *)
  (* ------------------------------------------------------------------ *)

  let apply_fn name arg_terms =
    match Hashtbl.find_opt fn_syms name with
    | None -> failwith ("bitwuzla: unknown function symbol: " ^ name)
    | Some (1, obj) ->
        let f : (BW.bv -> unit, BW.bv) BW.Term.Uf.t = Obj.obj obj in
        let open BW.Term in BW.Term.Uf.apply f (arg_terms.(0) :: [])
    | Some (2, obj) ->
        let f : (BW.bv -> BW.bv -> unit, BW.bv) BW.Term.Uf.t = Obj.obj obj in
        let open BW.Term in BW.Term.Uf.apply f (arg_terms.(0) :: arg_terms.(1) :: [])
    | Some (3, obj) ->
        let f : (BW.bv -> BW.bv -> BW.bv -> unit, BW.bv) BW.Term.Uf.t = Obj.obj obj in
        let open BW.Term in
        BW.Term.Uf.apply f (arg_terms.(0) :: arg_terms.(1) :: arg_terms.(2) :: [])
    | Some (n, _) ->
        failwith (Printf.sprintf "bitwuzla: UF arity %d not supported" n)
  in

  (* ------------------------------------------------------------------ *)
  (* Term parser                                                         *)
  (* ------------------------------------------------------------------ *)

  let rec parse_term sexp =
    match sexp with

    (* Boolean constants *)
    | Sexplib0.Sexp.Atom "true"  -> BW.Term.Bl.true'
    | Sexplib0.Sexp.Atom "false" -> BW.Term.Bl.false'

    (* Variable lookup *)
    | Sexplib0.Sexp.Atom name when String.starts_with ~prefix:"(_" name ->
        (match String.split_on_char ' ' name with
        | [_; bvlit; size_s] ->
            let value = String.sub bvlit 2 (String.length bvlit - 2) in
            let size = int_of_string (String.sub size_s 0 (String.length size_s - 1)) in
            BW.Term.Bv.of_string (BW.Sort.bv size) value
        | _ -> failwith "bad lit")

    (* Variable lookup *)
    | Sexplib0.Sexp.Atom name ->
        (match Hashtbl.find_opt var_syms name with
         | Some t -> t
         | None   ->
             failwith ("bitwuzla: unknown symbol: " ^ name))

    (* Indexed BV literal  (_ bvN M) — value N in decimal, width M *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                          Sexplib0.Sexp.Atom bvlit;
                          Sexplib0.Sexp.Atom size_s]
      when String.starts_with ~prefix:"bv" bvlit ->
        let value = String.sub bvlit 2 (String.length bvlit - 2) in
        let size  = int_of_string size_s in
        BW.Term.Bv.of_string (BW.Sort.bv size) value

    (* Boolean operators *)
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
        List.fold_left BW.Term.Bl.logand BW.Term.Bl.true'
          (List.map parse_term args)

    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: args) ->
        List.fold_left BW.Term.Bl.logor BW.Term.Bl.false'
          (List.map parse_term args)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; a] ->
        BW.Term.Bl.lognot (parse_term a)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>"; a; b] ->
        BW.Term.Bl.implies (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "xor"; a; b] ->
        BW.Term.Bl.logxor (parse_term a) (parse_term b)

    (* Equality, ITE, distinct *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; a; b] ->
        BW.Term.equal (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "distinct"; a; b] ->
        BW.Term.distinct (parse_term a) (parse_term b)

    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite"; c; t; e] ->
        BW.Term.ite (parse_term c) (parse_term t) (parse_term e)

    (* BV arithmetic *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvadd";  a; b] -> BW.Term.Bv.add  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsub";  a; b] -> BW.Term.Bv.sub  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvmul";  a; b] -> BW.Term.Bv.mul  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvudiv"; a; b] -> BW.Term.Bv.udiv (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvurem"; a; b] -> BW.Term.Bv.urem (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsdiv"; a; b] -> BW.Term.Bv.sdiv (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsrem"; a; b] -> BW.Term.Bv.srem (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsmod"; a; b] -> BW.Term.Bv.smod (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvneg";  a]    -> BW.Term.Bv.neg  (parse_term a)

    (* BV bitwise *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvand";  a; b] -> BW.Term.Bv.logand  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvor";   a; b] -> BW.Term.Bv.logor   (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxor";  a; b] -> BW.Term.Bv.logxor  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnand"; a; b] -> BW.Term.Bv.lognand (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnor";  a; b] -> BW.Term.Bv.lognor  (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxnor"; a; b] -> BW.Term.Bv.logxnor (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnot";  a]    -> BW.Term.Bv.lognot  (parse_term a)

    (* BV shifts *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvshl";  a; b] -> BW.Term.Bv.shift_left          (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvashr"; a; b] -> BW.Term.Bv.shift_right          (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvlshr"; a; b] -> BW.Term.Bv.shift_right_logical  (parse_term a) (parse_term b)

    (* BV comparisons *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvult";  a; b] -> BW.Term.Bv.ult (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvule";  a; b] -> BW.Term.Bv.ule (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvugt";  a; b] -> BW.Term.Bv.ugt (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvuge";  a; b] -> BW.Term.Bv.uge (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvslt";  a; b] -> BW.Term.Bv.slt (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsle";  a; b] -> BW.Term.Bv.sle (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsgt";  a; b] -> BW.Term.Bv.sgt (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsge";  a; b] -> BW.Term.Bv.sge (parse_term a) (parse_term b)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvcomp"; a; b] -> BW.Term.equal  (parse_term a) (parse_term b)

    (* BV concat *)
    | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "concat"; a; b] ->
        BW.Term.Bv.append (parse_term a) (parse_term b)

    (* Indexed: (_ extract hi lo) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "extract";
                             Sexplib0.Sexp.Atom hi_s;
                             Sexplib0.Sexp.Atom lo_s]; a] ->
        BW.Term.Bv.extract ~hi:(int_of_string hi_s) ~lo:(int_of_string lo_s)
          (parse_term a)

    (* Indexed: (_ zero_extend n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "zero_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        BW.Term.Bv.zero_extend (int_of_string n_s) (parse_term a)

    (* Indexed: (_ sign_extend n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "sign_extend";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        BW.Term.Bv.sign_extend (int_of_string n_s) (parse_term a)

    (* Indexed: (_ rotate_left n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_left";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        BW.Term.Bv.rotate_lefti (parse_term a) (int_of_string n_s)

    (* Indexed: (_ rotate_right n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "rotate_right";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        BW.Term.Bv.rotate_righti (parse_term a) (int_of_string n_s)

    (* Indexed: (_ repeat n) t *)
    | Sexplib0.Sexp.List
        [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                             Sexplib0.Sexp.Atom "repeat";
                             Sexplib0.Sexp.Atom n_s]; a] ->
        BW.Term.Bv.repeat (int_of_string n_s) (parse_term a)

    (* UF application: (f arg1 arg2 ...) *)
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom fname :: arg_sexps) ->
        let args = Array.of_list (List.map parse_term arg_sexps) in
        apply_fn fname args

    | s ->
        failwith ("bitwuzla: unsupported term: " ^ sexp_to_smtlib s)
  in

  (* ------------------------------------------------------------------ *)
  (* Declaration helpers                                                 *)
  (* ------------------------------------------------------------------ *)

  let do_declare_const name sort_sexp =
    let sort = parse_sort sort_sexp in
    let t = BW.Term.const sort name in
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
        (* defs = [ (arg_sort1 arg_sort2 ...) ; ret_sort ] *)
        (match defs with
         | [arg_list_sexp; ret_sort_sexp] ->
             let arg_sorts = match arg_list_sexp with
               | Sexplib0.Sexp.List ss -> List.map parse_sort ss
               | _ -> failwith "bitwuzla: declare-fun: expected arg sort list"
             in
             let ret_sort = parse_sort ret_sort_sexp in
             (match arg_sorts with
              | [] ->
                  let t = BW.Term.const ret_sort name in
                  Hashtbl.replace var_syms name t
              | [s1] ->
                  let fsort = BW.Sort.fn BW.Sort.[s1] ret_sort in
                  let t = BW.Term.const fsort name in
                  Hashtbl.replace fn_syms name (1, Obj.repr t)
              | [s1; s2] ->
                  let fsort = BW.Sort.fn BW.Sort.[s1; s2] ret_sort in
                  let t = BW.Term.const fsort name in
                  Hashtbl.replace fn_syms name (2, Obj.repr t)
              | [s1; s2; s3] ->
                  let fsort = BW.Sort.fn BW.Sort.[s1; s2; s3] ret_sort in
                  let t = BW.Term.const fsort name in
                  Hashtbl.replace fn_syms name (3, Obj.repr t)
              | _ -> failwith "bitwuzla: declare-fun arity > 3 not supported")
         | _ -> failwith "bitwuzla: declare-fun: unexpected defs format")
    | `Def ->
        (* defs = [ ((x1 sort1) ...) ; ret_sort ; body ] *)
        (match defs with
         | [arg_bindings_sexp; ret_sort_sexp; body_sexp] ->
             let bindings = match arg_bindings_sexp with
               | Sexplib0.Sexp.List bs ->
                   List.map (function
                     | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom n; s] -> (n, parse_sort s)
                     | _ -> failwith "bitwuzla: define-fun: bad binding") bs
               | _ -> failwith "bitwuzla: define-fun: expected binding list"
             in
             let ret_sort = parse_sort ret_sort_sexp in
             let arg_names  = List.map fst bindings in
             let arg_sorts  = List.map snd bindings in
             (match arg_sorts, arg_names with
              | [], [] ->
                  (* 0-arg define-fun: evaluate the body immediately *)
                  let t = parse_term body_sexp in
                  Hashtbl.replace var_syms name t
              | [s1], [n1] ->
                  let fn_term = BW.Term.Uf.lambda BW.Sort.[s1] (fun BW.Term.(x :: []) ->
                    Hashtbl.replace var_syms n1 x;
                    let body = parse_term body_sexp in
                    Hashtbl.remove var_syms n1;
                    body) in
                  ignore ret_sort;
                  Hashtbl.replace fn_syms name (1, Obj.repr fn_term)
              | [s1; s2], [n1; n2] ->
                  let fn_term = BW.Term.Uf.lambda BW.Sort.[s1; s2]
                    (fun BW.Term.(x :: y :: []) ->
                      Hashtbl.replace var_syms n1 x;
                      Hashtbl.replace var_syms n2 y;
                      let body = parse_term body_sexp in
                      Hashtbl.remove var_syms n1;
                      Hashtbl.remove var_syms n2;
                      body) in
                  ignore ret_sort;
                  Hashtbl.replace fn_syms name (2, Obj.repr fn_term)
              | _ -> failwith "bitwuzla: define-fun arity > 2 not supported")
         | _ -> failwith "bitwuzla: define-fun: unexpected defs format")
  in

  (* ------------------------------------------------------------------ *)
  (* check_sat with optional timeout                                     *)
  (* ------------------------------------------------------------------ *)

  let do_check_sat () =
    interrupted := 0;
    Buffer.add_string hist "(check-sat)\n";
    (* Compute deadline once up front; negative timeout_s means no limit. *)
    let deadline = if timeout_s >= 0.0
      then Some (Unix.gettimeofday () +. timeout_s)
      else None
    in
    (* Single interrupt callback combining external flag and optional timeout. *)
    let check () =
      !interrupted +
      (match deadline with
       | Some dl when Unix.gettimeofday () > dl -> 1
       | _ -> 0)
    in
    let result = BW.check_sat ~interrupt:(check, ()) () in
    match result with
    | BW.Sat     -> "sat"
    | BW.Unsat   -> "unsat"
    | BW.Unknown -> "unknown"
  in

  (* ------------------------------------------------------------------ *)
  (* solver record                                                       *)
  (* ------------------------------------------------------------------ *)

  {
    name          = "bitwuzla";
    set_logic     = (fun l ->
      Buffer.add_string hist (Printf.sprintf "(set-logic %s)\n" l));
    set_option    = (fun k v ->
      (* Timeout is handled at check_sat time; other options are ignored *)
      Buffer.add_string hist (Printf.sprintf "(set-option %s %s)\n" k v));
    declare_const = do_declare_const;
    fun_def       = do_fun_def;
    assert_       = (fun e ->
      Buffer.add_string hist (Printf.sprintf "(assert %s)\n" (sexp_to_smtlib e));
      BW.assert' (parse_term e));
    assert_named  = (fun nm e ->
      Buffer.add_string hist
        (Printf.sprintf "(assert (! %s :named %s))\n" (sexp_to_smtlib e) nm);
      BW.assert' ~name:nm (parse_term e));
    push          = (fun () ->
      Buffer.add_string hist "(push)\n";
      BW.push 1);
    pop           = (fun () ->
      Buffer.add_string hist "(pop)\n";
      BW.pop 1);
    interrupt     = (fun () -> interrupted := 1);
    check_sat     = do_check_sat;
    history       = (fun () -> Buffer.contents hist);
    close         = (fun () -> BW.unsafe_close ());
  }

(* ------------------------------------------------------------------ *)
(* Module interface                                                     *)
(* ------------------------------------------------------------------ *)

(* Bitwuzla.Incremental() produces a module, not a value, and its term
   types carry phantom parameters (BW.bv BW.term) that cannot appear in
   a generic record field.  We capture all BW-module operations as
   closures inside [build] and store them alongside the mutable state
   tables. *)

module Bitwuzla_solver : Solver.Solver = struct
  type t = {
    var_syms    : (string, Obj.t) Hashtbl.t;
    fn_syms     : (string, int * Obj.t) Hashtbl.t;
    interrupted : int ref;
    timeout_s   : float ref;
    bw_declare_const : string -> Sexplib0.Sexp.t -> unit;
    bw_add       : Sexplib0.Sexp.t -> unit;
    bw_push      : unit -> unit;
    bw_pop       : unit -> unit;
    bw_check     : (unit -> int) -> [`Sat | `Unsat | `Unknown];
    bw_close     : unit -> unit;
  }

  let build () =
    let module BW = Bitwuzla.Incremental() in

    let var_syms : (string, Obj.t) Hashtbl.t = Hashtbl.create 64 in
    let fn_syms  : (string, int * Obj.t)    Hashtbl.t = Hashtbl.create  8 in

    let parse_sort sexp =
      match sexp with
      | Sexplib0.Sexp.Atom "Bool" -> Obj.repr BW.Sort.bool
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                            Sexplib0.Sexp.Atom "BitVec";
                            Sexplib0.Sexp.Atom n] ->
          Obj.repr (BW.Sort.bv (int_of_string n))
      | s ->
          failwith ("bitwuzla: unsupported sort: " ^ sexp_to_smtlib s)
    in

    let apply_fn name arg_terms =
      match Hashtbl.find_opt fn_syms name with
      | None -> failwith ("bitwuzla: unknown function symbol: " ^ name)
      | Some (1, obj) ->
          let f : (BW.bv -> unit, BW.bv) BW.Term.Uf.t = Obj.obj obj in
          let open BW.Term in
          Obj.repr (BW.Term.Uf.apply f [Obj.obj arg_terms.(0)])
      | Some (2, obj) ->
          let f : (BW.bv -> BW.bv -> unit, BW.bv) BW.Term.Uf.t = Obj.obj obj in
          let open BW.Term in
          Obj.repr (BW.Term.Uf.apply f [Obj.obj arg_terms.(0); Obj.obj arg_terms.(1)])
      | Some (3, obj) ->
          let f : (BW.bv -> BW.bv -> BW.bv -> unit, BW.bv) BW.Term.Uf.t = Obj.obj obj in
          let open BW.Term in
          Obj.repr (BW.Term.Uf.apply f
            [Obj.obj arg_terms.(0); Obj.obj arg_terms.(1); Obj.obj arg_terms.(2)])
      | Some (n, _) ->
          failwith (Printf.sprintf "bitwuzla: UF arity %d not supported" n)
    in

    let rec parse_term sexp =
      match sexp with
      | Sexplib0.Sexp.Atom "true"  -> Obj.repr BW.Term.Bl.true'
      | Sexplib0.Sexp.Atom "false" -> Obj.repr BW.Term.Bl.false'
      | Sexplib0.Sexp.Atom name when String.starts_with ~prefix:"(_" name ->
          (match String.split_on_char ' ' name with
          | [_; bvlit; size_s] ->
              let value = String.sub bvlit 2 (String.length bvlit - 2) in
              let size  = int_of_string (String.sub size_s 0 (String.length size_s - 1)) in
              Obj.repr (BW.Term.Bv.of_string (BW.Sort.bv size) value)
          | _ -> failwith "bitwuzla: bad literal atom")
      | Sexplib0.Sexp.Atom name ->
          (match Hashtbl.find_opt var_syms name with
           | Some t -> t
           | None   -> failwith ("bitwuzla: unknown symbol: " ^ name))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                            Sexplib0.Sexp.Atom bvlit;
                            Sexplib0.Sexp.Atom size_s]
        when String.starts_with ~prefix:"bv" bvlit ->
          let value = String.sub bvlit 2 (String.length bvlit - 2) in
          let size  = int_of_string size_s in
          Obj.repr (BW.Term.Bv.of_string (BW.Sort.bv size) value)
      | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
          Obj.repr (List.fold_left BW.Term.Bl.logand BW.Term.Bl.true'
            (List.map (fun s -> Obj.obj (parse_term s)) args))
      | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: args) ->
          Obj.repr (List.fold_left BW.Term.Bl.logor BW.Term.Bl.false'
            (List.map (fun s -> Obj.obj (parse_term s)) args))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; a] ->
          Obj.repr (BW.Term.Bl.lognot (Obj.obj (parse_term a)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>"; a; b] ->
          Obj.repr (BW.Term.Bl.implies (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "xor"; a; b] ->
          Obj.repr (BW.Term.Bl.logxor (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; a; b] ->
          Obj.repr (BW.Term.equal (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "distinct"; a; b] ->
          Obj.repr (BW.Term.distinct (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite"; c; th; el] ->
          Obj.repr (BW.Term.ite (Obj.obj (parse_term c)) (Obj.obj (parse_term th)) (Obj.obj (parse_term el)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvadd";  a; b] -> Obj.repr (BW.Term.Bv.add  (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsub";  a; b] -> Obj.repr (BW.Term.Bv.sub  (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvmul";  a; b] -> Obj.repr (BW.Term.Bv.mul  (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvudiv"; a; b] -> Obj.repr (BW.Term.Bv.udiv (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvurem"; a; b] -> Obj.repr (BW.Term.Bv.urem (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsdiv"; a; b] -> Obj.repr (BW.Term.Bv.sdiv (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsrem"; a; b] -> Obj.repr (BW.Term.Bv.srem (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsmod"; a; b] -> Obj.repr (BW.Term.Bv.smod (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvneg";  a]    -> Obj.repr (BW.Term.Bv.neg  (Obj.obj (parse_term a)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvand";  a; b] -> Obj.repr (BW.Term.Bv.logand  (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvor";   a; b] -> Obj.repr (BW.Term.Bv.logor   (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxor";  a; b] -> Obj.repr (BW.Term.Bv.logxor  (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnand"; a; b] -> Obj.repr (BW.Term.Bv.lognand (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnor";  a; b] -> Obj.repr (BW.Term.Bv.lognor  (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvxnor"; a; b] -> Obj.repr (BW.Term.Bv.logxnor (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvnot";  a]    -> Obj.repr (BW.Term.Bv.lognot  (Obj.obj (parse_term a)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvshl";  a; b] -> Obj.repr (BW.Term.Bv.shift_left         (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvashr"; a; b] -> Obj.repr (BW.Term.Bv.shift_right         (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvlshr"; a; b] -> Obj.repr (BW.Term.Bv.shift_right_logical (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvult";  a; b] -> Obj.repr (BW.Term.Bv.ult (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvule";  a; b] -> Obj.repr (BW.Term.Bv.ule (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvugt";  a; b] -> Obj.repr (BW.Term.Bv.ugt (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvuge";  a; b] -> Obj.repr (BW.Term.Bv.uge (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvslt";  a; b] -> Obj.repr (BW.Term.Bv.slt (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsle";  a; b] -> Obj.repr (BW.Term.Bv.sle (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsgt";  a; b] -> Obj.repr (BW.Term.Bv.sgt (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvsge";  a; b] -> Obj.repr (BW.Term.Bv.sge (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "bvcomp"; a; b] -> Obj.repr (BW.Term.equal  (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "concat"; a; b] ->
          Obj.repr (BW.Term.Bv.append (Obj.obj (parse_term a)) (Obj.obj (parse_term b)))
      | Sexplib0.Sexp.List
          [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                               Sexplib0.Sexp.Atom "extract";
                               Sexplib0.Sexp.Atom hi_s;
                               Sexplib0.Sexp.Atom lo_s]; a] ->
          Obj.repr (BW.Term.Bv.extract ~hi:(int_of_string hi_s) ~lo:(int_of_string lo_s)
            (Obj.obj (parse_term a)))
      | Sexplib0.Sexp.List
          [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                               Sexplib0.Sexp.Atom "zero_extend";
                               Sexplib0.Sexp.Atom n_s]; a] ->
          Obj.repr (BW.Term.Bv.zero_extend (int_of_string n_s) (Obj.obj (parse_term a)))
      | Sexplib0.Sexp.List
          [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                               Sexplib0.Sexp.Atom "sign_extend";
                               Sexplib0.Sexp.Atom n_s]; a] ->
          Obj.repr (BW.Term.Bv.sign_extend (int_of_string n_s) (Obj.obj (parse_term a)))
      | Sexplib0.Sexp.List
          [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                               Sexplib0.Sexp.Atom "rotate_left";
                               Sexplib0.Sexp.Atom n_s]; a] ->
          Obj.repr (BW.Term.Bv.rotate_lefti (Obj.obj (parse_term a)) (int_of_string n_s))
      | Sexplib0.Sexp.List
          [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                               Sexplib0.Sexp.Atom "rotate_right";
                               Sexplib0.Sexp.Atom n_s]; a] ->
          Obj.repr (BW.Term.Bv.rotate_righti (Obj.obj (parse_term a)) (int_of_string n_s))
      | Sexplib0.Sexp.List
          [Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                               Sexplib0.Sexp.Atom "repeat";
                               Sexplib0.Sexp.Atom n_s]; a] ->
          Obj.repr (BW.Term.Bv.repeat (int_of_string n_s) (Obj.obj (parse_term a)))
      | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom fname :: arg_sexps) ->
          let args = Array.of_list (List.map parse_term arg_sexps) in
          apply_fn fname args
      | s ->
          failwith ("bitwuzla: unsupported term: " ^ sexp_to_smtlib s)
    in

    let bw_declare_const name sort_sexp =
      let sort : BW.bv BW.sort = Obj.obj (parse_sort sort_sexp) in
      let term = BW.Term.const sort name in
      Hashtbl.replace var_syms name (Obj.repr term)
    in

    let bw_add sexp =
      BW.assert' (Obj.obj (parse_term sexp))
    in

    let bw_check interrupt_fn =
      let result = BW.check_sat ~interrupt:(interrupt_fn, ()) () in
      match result with
      | BW.Sat     -> `Sat
      | BW.Unsat   -> `Unsat
      | BW.Unknown -> `Unknown
    in

    { var_syms;
      fn_syms;
      interrupted = ref 0;
      timeout_s   = ref (-1.0);
      bw_declare_const;
      bw_add;
      bw_push  = (fun () -> BW.push 1);
      bw_pop   = (fun () -> BW.pop 1);
      bw_check;
      bw_close = BW.unsafe_close;
    }

  let set_timeout t ms =
    t.timeout_s := float_of_int ms /. 1000.0

  let set_logic _t _l = ()

  let set_option _t _k _v = ()

  let declare_const t name sort_sexp =
    t.bw_declare_const name sort_sexp

  let add t sexp =
    t.bw_add sexp

  let push t = t.bw_push ()

  let pop t = t.bw_pop ()

  let check_sat t =
    t.interrupted := 0;
    let deadline = if !(t.timeout_s) >= 0.0
      then Some (Unix.gettimeofday () +. !(t.timeout_s))
      else None
    in
    let interrupt_fn () =
      !(t.interrupted) +
      (match deadline with
       | Some dl when Unix.gettimeofday () > dl -> 1
       | _ -> 0)
    in
    match t.bw_check interrupt_fn with
    | `Sat     -> Solver.Sat
    | `Unsat   -> Solver.Unsat
    | `Unknown -> Solver.Unknown

  let interrupt t = t.interrupted := 1

  let close t = t.bw_close ()
end
