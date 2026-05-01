(** SMT-LIB output generator and solver interface *)

open Data_structures
open Utilities

let mk_and sexps =
  match sexps with
  | [] -> Sexplib0.Sexp.Atom "true"
  | [a] -> a
  | _ -> Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: sexps)

let mk_imp ants cons =
  match ants, cons with
  | [], [a] -> a
  | _, _ -> Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>" ; mk_and ants ; mk_and cons]

let mk_not sexp =
  Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; sexp]

(** Flag to enable/disable default values in ite chains *)
let use_ite_default_values = ref false

(** Convert S-expression to SMT-LIB string with proper formatting *)
let sexp_to_smtlib sexp =
  let rec format_sexp = function
    | Sexplib0.Sexp.Atom s -> s
    | Sexplib0.Sexp.List items ->
        "(" ^ String.concat " " (List.map format_sexp items) ^ ")"
  in
  format_sexp sexp

(* ------------------------------------------------------------------ *)
(* Sexp-returning helpers used by emit_* and effect_optimizer          *)
(* ------------------------------------------------------------------ *)

(** Build a conjunction sexp from a list of predicates *)
let conjunction_sexp predicates =
  match List.map (fun p -> p.term) predicates with
  | []       -> Sexplib0.Sexp.Atom "true"
  | [single] -> single
  | multiple -> Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: multiple)

(** Build a reachability sexp from a query's source/target locations *)
let reachability_sexp query =
  let src = Option.get query.source_location in
  let tgt = Option.get query.target_location in
  Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "and";
                      Sexplib0.Sexp.Atom src;
                      Sexplib0.Sexp.Atom tgt]

(** Flatten nested 'and' expressions into a list of conjuncts *)
let rec flatten_and_conditions = function
  | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
      List.concat_map flatten_and_conditions args
  | expr -> [expr]

(* TODO: add named assertions (:named) *)

(* ------------------------------------------------------------------ *)
(* emit_* functions — take a solver module and issue commands directly  *)
(* ------------------------------------------------------------------ *)

let emit_variable_declarations (module S : Solver.Solver) program =
  StringMap.iter (fun var_name var ->
    S.declare_const var_name var.sort
  ) program.variables

let emit_block_assertions (module S : Solver.Solver) program _program_prefix =
  (match program.entry with
  | Some entry_block ->
      S.add (Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=";
                                 Sexplib0.Sexp.Atom entry_block;
                                 Sexplib0.Sexp.Atom "true"])
  | None -> ());

  StringMap.iter (fun block_name block ->
    if Some block_name <> program.entry then begin
      let pred_condition = match block.preds with
        | [] -> Sexplib0.Sexp.Atom "true"
        | [p] -> Sexplib0.Sexp.Atom p
        | ps  -> Sexplib0.Sexp.List
                   (Sexplib0.Sexp.Atom "or" :: List.map (fun p -> Sexplib0.Sexp.Atom p) ps)
      in
      let assumes = List.concat_map (function
        | Assume expr -> flatten_and_conditions expr
        | _ -> []
      ) block.ops in
      let all_conditions = assumes @ [pred_condition] in
      let full_condition = match all_conditions with
        | []       -> Sexplib0.Sexp.Atom "true"
        | [single] -> single
        | multiple -> Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: multiple)
      in
      S.add (Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=";
                                 Sexplib0.Sexp.Atom block_name;
                                 full_condition])
    end
  ) program.blocks

let emit_assignment_assertions (module S : Solver.Solver) program =
  let get_default_value var =
    match StringMap.find_opt var program.variables with
    | None -> Sexplib0.Sexp.Atom "false"
    | Some v ->
        match v.sort with
        | Sexplib0.Sexp.Atom "Bool" -> Sexplib0.Sexp.Atom "false"
        | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                              Sexplib0.Sexp.Atom "BitVec";
                              Sexplib0.Sexp.Atom size] ->
            Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                                Sexplib0.Sexp.Atom "bv0";
                                Sexplib0.Sexp.Atom size]
        | _ -> Sexplib0.Sexp.Atom "false"
  in
  StringMap.iter (fun _ block ->
    StringMap.iter (fun var phi_list ->
      match phi_list with
      | [] -> ()
      | [(_pred_block, expr)] ->
          S.add (Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; Sexplib0.Sexp.Atom var; expr])
      | _ ->
          if !use_ite_default_values then begin
            let default = get_default_value var in
            let rec build = function
              | [] -> default
              | [(pb, e)] ->
                  Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite";
                                      Sexplib0.Sexp.Atom pb; e; default]
              | (pb, e) :: rest ->
                  Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite";
                                      Sexplib0.Sexp.Atom pb; e; build rest]
            in
            S.add (Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; Sexplib0.Sexp.Atom var; build phi_list])
          end else begin
            let rec build = function
              | [] -> failwith "empty phi list"
              | [(_pb, e)] -> e
              | (pb, e) :: rest ->
                  Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "ite";
                                      Sexplib0.Sexp.Atom pb; e; build rest]
            in
            S.add (Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; Sexplib0.Sexp.Atom var; build phi_list])
          end
    ) block.phis;
    List.iter (fun op ->
      match op with
      | Assignment { var; expr } ->
          S.add (Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "="; Sexplib0.Sexp.Atom var; expr])
      | _ -> ()
    ) block.ops
  ) program.blocks

let emit_arbitrary_assertions (module S : Solver.Solver) state =
  List.iter (fun predicate ->
    S.add predicate.term
  ) state.arbitrary

let emit_effect_query (module S : Solver.Solver) query =
  let req = conjunction_sexp query.req in
  let ens = conjunction_sexp query.ens in
  let impl = Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "=>"; req; ens] in
  S.add impl

let emit_effect_assertions (module S : Solver.Solver) queries =
  List.iter (fun q -> emit_effect_query (module S) q) queries

let emit_initial_assertions (module S : Solver.Solver) predicates =
  List.iter (fun predicate ->
    S.add predicate.term
  ) predicates

let emit_final_assertions (module S : Solver.Solver) predicates =
  List.iter (fun predicate ->
    let neg = Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; predicate.term] in
    S.add neg
  ) predicates

(* ------------------------------------------------------------------ *)
(* Legacy string-returning functions — kept for non-incremental callers *)
(* ------------------------------------------------------------------ *)

let generate_conjunction predicates =
  let terms = List.map (fun pred -> pred.term) predicates in
  match terms with
  | [] -> "true"
  | [single] -> sexp_to_smtlib single
  | multiple -> Printf.sprintf "(and %s)" (String.concat " " (List.map sexp_to_smtlib multiple))

let generate_variable_declarations program =
  let buffer = Buffer.create 1024 in
  StringMap.iter (fun var_name var ->
    let sort_str = sexp_to_smtlib var.sort in
    Buffer.add_string buffer (Printf.sprintf "(declare-const %s %s )\n" var_name sort_str)
  ) program.variables;
  Buffer.contents buffer

let generate_block_assertions program program_prefix =
  let buffer = Buffer.create 2048 in
  (match program.entry with
  | Some entry_block ->
      Buffer.add_string buffer
        (Printf.sprintf "(assert (! (= %s true ) :named %s_entry ) )\n"
           entry_block program_prefix)
  | None -> ());
  StringMap.iter (fun block_name block ->
    if Some block_name <> program.entry then begin
      let pred_condition = match block.preds with
        | [] -> "true"
        | [single_pred] -> single_pred
        | multiple_preds ->
            Printf.sprintf "(or %s)" (String.concat " " multiple_preds)
      in
      let assumes = List.concat_map (function
        | Assume expr ->
            List.map sexp_to_smtlib (flatten_and_conditions expr)
        | _ -> []
      ) block.ops in
      let all_conditions = assumes @ [pred_condition] in
      let full_condition = match all_conditions with
        | [] -> "true"
        | [s] -> s
        | ms -> Printf.sprintf "(and %s)" (String.concat " " ms)
      in
      let assertion_name =
        if String.starts_with ~prefix:program_prefix block_name then
          let suffix = String.sub block_name (String.length program_prefix + 2)
                         (String.length block_name - String.length program_prefix - 2) in
          Printf.sprintf "%s%s" (String.sub program_prefix 0 3) suffix
        else
          block_name
      in
      Buffer.add_string buffer
        (Printf.sprintf "(assert (! (= %s %s ) :named %s ) )\n"
           block_name full_condition assertion_name)
    end
  ) program.blocks;
  Buffer.contents buffer

let generate_assignment_assertions program =
  let buffer = Buffer.create 2048 in
  let get_default_value var =
    match StringMap.find_opt var program.variables with
    | None -> "false"
    | Some var_info ->
        match var_info.sort with
        | Sexplib0.Sexp.Atom "Bool" -> "false"
        | Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "_";
                              Sexplib0.Sexp.Atom "BitVec";
                              Sexplib0.Sexp.Atom size] ->
            Printf.sprintf "(_ bv0 %s)" size
        | _ -> "false"
  in
  StringMap.iter (fun block_name block ->
    StringMap.iter (fun var phi_list ->
      match phi_list with
      | [] -> ()
      | [(pred_block, expr)] ->
          let phi_condition = Printf.sprintf "(= %s %s)" var (sexp_to_smtlib expr) in
          let assertion_name = Printf.sprintf "phi_%s_from_%s" var pred_block in
          Buffer.add_string buffer
            (Printf.sprintf "(assert (! %s :named %s ) )\n" phi_condition assertion_name)
      | _ ->
          if !use_ite_default_values then begin
            let default_value = get_default_value var in
            let rec build_ite_chain = function
              | [] -> default_value
              | [(pred_block, expr)] ->
                  Printf.sprintf "(ite %s %s %s)"
                    pred_block (sexp_to_smtlib expr) default_value
              | (pred_block, expr) :: rest ->
                  Printf.sprintf "(ite %s %s %s)"
                    pred_block (sexp_to_smtlib expr) (build_ite_chain rest)
            in
            let phi_condition =
              Printf.sprintf "(= %s %s)" var (build_ite_chain phi_list) in
            Buffer.add_string buffer
              (Printf.sprintf "(assert (! %s :named %s ) )\n"
                 phi_condition (Printf.sprintf "phi_%s" var))
          end else begin
            let rec build_ite_chain = function
              | [] -> failwith "Empty phi list in build_ite_chain"
              | [(_pred_block, expr)] -> sexp_to_smtlib expr
              | (pred_block, expr) :: rest ->
                  Printf.sprintf "(ite %s %s %s)"
                    pred_block (sexp_to_smtlib expr) (build_ite_chain rest)
            in
            let phi_condition =
              Printf.sprintf "(= %s %s)" var (build_ite_chain phi_list) in
            Buffer.add_string buffer
              (Printf.sprintf "(assert (! %s :named %s ) )\n"
                 phi_condition (Printf.sprintf "phi_%s" var))
          end
    ) block.phis;
    List.iteri (fun i operation ->
      match operation with
      | Assignment { var; expr } ->
          let assignment_condition =
            Printf.sprintf "(= %s %s)" var (sexp_to_smtlib expr) in
          let assertion_name = Printf.sprintf "%s_op_%d" block_name i in
          Buffer.add_string buffer
            (Printf.sprintf "(assert (! %s :named %s ) )\n"
               assignment_condition assertion_name)
      | _ -> ()
    ) block.ops
  ) program.blocks;
  Buffer.contents buffer

let generate_arbitrary_assertions state =
  let buffer = Buffer.create 2048 in
  List.iter (fun predicate ->
    Buffer.add_string buffer
      (Printf.sprintf "(assert %s)\n" (sexp_to_smtlib predicate.term))
  ) state.arbitrary;
  Buffer.contents buffer

let generate_effect_query_assertion query =
  let req_terms = List.map (fun pred -> pred.term) query.req in
  let ens_terms = List.map (fun pred -> pred.term) query.ens in
  let req_combined = match req_terms with
    | [] -> "true"
    | [single] -> sexp_to_smtlib single
    | multiple ->
        Printf.sprintf "(and %s)" (String.concat " " (List.map sexp_to_smtlib multiple))
  in
  let ens_combined = match ens_terms with
    | [] -> "true"
    | [single] -> sexp_to_smtlib single
    | multiple ->
        Printf.sprintf "(and %s)" (String.concat " " (List.map sexp_to_smtlib multiple))
  in
  let full_implication = Printf.sprintf "(=> %s %s)" req_combined ens_combined in
  Printf.sprintf "(assert (! %s :named %s ) )\n" full_implication query.qname

let generate_initial_assertions initial_queries =
  let buffer = Buffer.create 1024 in
  List.iteri (fun i predicate ->
    Buffer.add_string buffer
      (Printf.sprintf "(assert (! %s :named inv%d ) )\n"
         (sexp_to_smtlib predicate.term) (i + 1))
  ) initial_queries;
  Buffer.contents buffer

let generate_final_assertions final_queries =
  let buffer = Buffer.create 1024 in
  List.iteri (fun i predicate ->
    let negated_pred = Printf.sprintf "(not %s)" (sexp_to_smtlib predicate.term) in
    Buffer.add_string buffer
      (Printf.sprintf "(assert (! %s :named InvPrimed%s ) )\n"
         negated_pred (if i = 0 then "" else string_of_int i))
  ) final_queries;
  Buffer.contents buffer

let generate_effect_assertions effect_queries =
  let buffer = Buffer.create 1024 in
  List.iter (fun query ->
    Buffer.add_string buffer (generate_effect_query_assertion query)
  ) effect_queries;
  Buffer.contents buffer

let generate_smtlib_header = "(set-logic QF_UFBV )\n"

let generate_smtlib_footer () = "(check-sat)\n"

let generate_smtlib_tactic_footer tactic = Printf.sprintf "%s\n" tactic

let state_to_smtlib_string state =
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer generate_smtlib_header;
  Buffer.add_string buffer (generate_variable_declarations state.source);
  Buffer.add_string buffer (generate_variable_declarations state.target);
  Buffer.add_string buffer (generate_block_assertions state.source "source");
  Buffer.add_string buffer (generate_block_assertions state.target "target");
  Buffer.add_string buffer (generate_assignment_assertions state.source);
  Buffer.add_string buffer (generate_assignment_assertions state.target);
  Buffer.add_string buffer (generate_effect_assertions state.effects);
  Buffer.add_string buffer (generate_arbitrary_assertions state);
  Buffer.add_string buffer (generate_smtlib_footer ());
  Buffer.contents buffer

let state_to_smtlib_tactic_string state tactic =
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer generate_smtlib_header;
  Buffer.add_string buffer (generate_variable_declarations state.source);
  Buffer.add_string buffer (generate_variable_declarations state.target);
  Buffer.add_string buffer (generate_block_assertions state.source "source");
  Buffer.add_string buffer (generate_block_assertions state.target "target");
  Buffer.add_string buffer (generate_assignment_assertions state.source);
  Buffer.add_string buffer (generate_assignment_assertions state.target);
  Buffer.add_string buffer (generate_effect_assertions state.effects);
  Buffer.add_string buffer (generate_arbitrary_assertions state);
  Buffer.add_string buffer (generate_smtlib_tactic_footer tactic);
  Buffer.contents buffer

let write_smtlib_file filename state =
  let content = state_to_smtlib_string state in
  let oc = open_out filename in
  output_string oc content;
  close_out oc;
  Printf.printf "SMT-LIB file written: %s\n" filename

let write_smtlib_tactic_file filename state tactic =
  let content = state_to_smtlib_tactic_string state tactic in
  let oc = open_out filename in
  output_string oc content;
  close_out oc;
  Printf.printf "SMT-LIB tactic file written: %s\n" filename

let create_smtlib_file_with_content state content filename =
  let oc = open_out filename in
  Printf.fprintf oc "%s" generate_smtlib_header;
  Printf.fprintf oc "%s" (generate_variable_declarations state.source);
  Printf.fprintf oc "%s" (generate_variable_declarations state.target);
  Printf.fprintf oc "%s" content;
  close_out oc
