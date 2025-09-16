(** SMT-LIB output generator for states *)

open Data_structures
open Utilities

(** Convert S-expression to SMT-LIB string with proper formatting *)
let sexp_to_smtlib sexp =
  let rec format_sexp = function
    | Sexplib0.Sexp.Atom s -> s
    | Sexplib0.Sexp.List items ->
        let formatted_items = List.map format_sexp items in
        "(" ^ String.concat " " formatted_items ^ ")"
  in
  format_sexp sexp

(** Generate conjunction from list of predicates *)
let generate_conjunction predicates =
  let terms = List.map (fun pred -> pred.term) predicates in
  match terms with
  | [] -> "true"
  | [single] -> sexp_to_smtlib single
  | multiple -> Printf.sprintf "(and %s)" (String.concat " " (List.map sexp_to_smtlib multiple))

(** Flatten nested 'and' expressions into a list of conjuncts *)
let rec flatten_and_conditions = function
  | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: args) ->
      (* This is an 'and' expression, recursively flatten each argument *)
      List.concat_map flatten_and_conditions args
  | expr ->
      (* Not an 'and' expression, return as single element *)
      [expr]

let generate_fun_defs funs =
  let buffer = Buffer.create 1024 in
  List.iter (fun (fun_name,defs) ->
    let sort_str = String.concat " " (List.map sexp_to_smtlib defs) in
    Buffer.add_string buffer (Printf.sprintf "(define-fun %s %s )\n" fun_name sort_str)
  ) funs;
  Buffer.contents buffer

(** Generate variable declarations *)
let generate_variable_declarations program =
  let buffer = Buffer.create 1024 in
  StringMap.iter (fun var_name var ->
    let sort_str = sexp_to_smtlib var.sort in
    Buffer.add_string buffer (Printf.sprintf "(declare-const %s %s )\n" var_name sort_str)
  ) program.variables;
  Buffer.contents buffer

(** Generate block assertions for a program *)
let generate_block_assertions program program_prefix =
  let buffer = Buffer.create 2048 in

  (* Generate entry block assertions *)
  (match program.entry with
  | Some entry_block ->
      Buffer.add_string buffer (Printf.sprintf "(assert (! (= %s true ) :named %s_entry ) )\n" entry_block program_prefix)
  | None -> ());

  (* Generate regular block assertions *)
  StringMap.iter (fun block_name block ->
    (* Skip entry block as it's already handled *)
    if Some block_name <> program.entry then begin
      (* Generate predecessor condition *)
      let pred_condition = match block.preds with
        | [] -> "true"
        | [single_pred] -> single_pred
        | multiple_preds ->
            let pred_list = String.concat " " multiple_preds in
            Printf.sprintf "(or %s)" pred_list
      in

      (* Extract assume operations from the block and flatten nested 'and' conditions *)
      let assumes = List.concat_map (function
        | Assume expr ->
            (* Flatten any nested 'and' expressions and convert to strings *)
            let flattened_exprs = flatten_and_conditions expr in
            List.map sexp_to_smtlib flattened_exprs
        | _ -> []
      ) block.ops in

      (* Generate the full block condition: assumes AND predecessor_condition *)
      let all_conditions = assumes @ [pred_condition] in
      let full_condition = match all_conditions with
        | [] -> "true"
        | [single_condition] -> single_condition
        | multiple_conditions ->
            Printf.sprintf "(and %s)" (String.concat " " multiple_conditions)
      in

      (* Generate block assertion name by extracting the meaningful part *)
      let assertion_name =
        if String.starts_with ~prefix:program_prefix block_name then
          let suffix = String.sub block_name (String.length program_prefix + 2) (String.length block_name - String.length program_prefix - 2) in
          Printf.sprintf "%s%s" (String.sub program_prefix 0 3) suffix  (* "src" or "tgt" + suffix *)
        else
          block_name
      in
      Buffer.add_string buffer (Printf.sprintf "(assert (! (= %s %s ) :named %s ) )\n" block_name full_condition assertion_name)
    end
  ) program.blocks;

  Buffer.contents buffer

(** Generate assignment assertions within blocks *)
let generate_assignment_assertions program =
  let buffer = Buffer.create 2048 in
  StringMap.iter (fun block_name block ->
    (* Generate phi node assertions *)
    StringMap.iter (fun var phi_list ->
      match phi_list with
      | [] -> () (* No phi entries for this variable *)
      | [(pred_block, expr)] ->
          (* Single predecessor - simple equality *)
          let phi_condition = Printf.sprintf "(= %s %s)" var (sexp_to_smtlib expr) in
          let assertion_name = Printf.sprintf "phi_%s_from_%s" var pred_block in
          Buffer.add_string buffer (Printf.sprintf "(assert (! %s :named %s ) )\n" phi_condition assertion_name)
      | _ ->
          (* Multiple predecessors - use nested ite *)
          let rec build_ite_chain = function
            | [] -> failwith "Empty phi list in build_ite_chain"
            | [(_pred_block, expr)] -> sexp_to_smtlib expr
            | (pred_block, expr) :: rest ->
                Printf.sprintf "(ite %s %s %s)"
                  pred_block
                  (sexp_to_smtlib expr)
                  (build_ite_chain rest)
          in
          let phi_condition = Printf.sprintf "(= %s %s)" var (build_ite_chain phi_list) in
          let assertion_name = Printf.sprintf "phi_%s" var in
          Buffer.add_string buffer (Printf.sprintf "(assert (! %s :named %s ) )\n" phi_condition assertion_name)
    ) block.phis;

    (* Generate operation assertions - exclude assumes as they're in block assertions *)
    List.iteri (fun i operation ->
      match operation with
      | Assignment { var; expr } ->
          let assignment_condition = Printf.sprintf "(= %s %s)" var (sexp_to_smtlib expr) in
          let assertion_name = Printf.sprintf "%s_op_%d" block_name i in
          Buffer.add_string buffer (Printf.sprintf "(assert (! %s :named %s ) )\n" assignment_condition assertion_name)
      | _ -> ()
    ) block.ops
  ) program.blocks;

  Buffer.contents buffer


let generate_arbitrary_assertions state =
  let buffer = Buffer.create 2048 in
  List.iter (fun predicate ->
    let pred_str = sexp_to_smtlib predicate.term in
    Buffer.add_string buffer (Printf.sprintf "(assert %s)\n" pred_str)
  ) state.arbitrary;
  Buffer.contents buffer

(** Generate a single effect query assertion with location conditions *)
let generate_effect_query_assertion query =
  let req_terms = List.map (fun pred -> pred.term) query.req in
  let ens_terms = List.map (fun pred -> pred.term) query.ens in

  (* Build location condition: (and source_location target_location) *)
  let _location_condition =
    match query.source_location, query.target_location with
    | Some src, Some tgt -> Printf.sprintf "(and %s %s)" src tgt
    | Some src, None -> src
    | None, Some tgt -> tgt
    | None, None -> "true"
  in

  (* Build requirements *)
  let req_combined = match req_terms with
    | [] -> "true"
    | [single] -> sexp_to_smtlib single
    | multiple -> Printf.sprintf "(and %s)" (String.concat " " (List.map sexp_to_smtlib multiple))
  in

  (* Build ensures *)
  let ens_combined = match ens_terms with
    | [] -> "true"
    | [single] -> sexp_to_smtlib single
    | multiple -> Printf.sprintf "(and %s)" (String.concat " " (List.map sexp_to_smtlib multiple))
  in

  (* Build the complete implication: (=> (=> (and source_location target_location) req) ens) *)
  let inner_implication = Printf.sprintf "%s" req_combined in
  let full_implication = Printf.sprintf "(=> %s %s)" inner_implication ens_combined in

  Printf.sprintf "(assert (! %s :named %s ) )\n" full_implication query.qname

(** Generate initial queries (invariants) *)
let generate_initial_assertions initial_queries =
  let buffer = Buffer.create 1024 in
  List.iteri (fun i predicate ->
    let pred_str = sexp_to_smtlib predicate.term in
    Buffer.add_string buffer (Printf.sprintf "(assert (! %s :named inv%d ) )\n" pred_str (i + 1))
  ) initial_queries;
  Buffer.contents buffer

(** Generate final queries (post-conditions that should be false) *)
let generate_final_assertions final_queries =
  let buffer = Buffer.create 1024 in
  List.iteri (fun i predicate ->
    let pred_str = sexp_to_smtlib predicate.term in
    let negated_pred = Printf.sprintf "(not %s)" pred_str in
    Buffer.add_string buffer (Printf.sprintf "(assert (! %s :named InvPrimed%s ) )\n" negated_pred (if i = 0 then "" else string_of_int i))
  ) final_queries;
  Buffer.contents buffer

(** Generate effect queries *)
let generate_effect_assertions effect_queries =
  let buffer = Buffer.create 1024 in
  List.iter (fun query ->
    Buffer.add_string buffer (generate_effect_query_assertion query)
  ) effect_queries;
  Buffer.contents buffer

(** Generate SMT-LIB header *)
let generate_smtlib_header =
  "(set-logic QF_UFBV )\n"

(** Generate SMT-LIB footer *)
let generate_smtlib_footer () =
  "(check-sat)\n"

(** Generate SMT-LIB footer with custom tactic *)
let generate_smtlib_tactic_footer tactic =
  Printf.sprintf "%s\n" tactic

(** Generate complete SMT-LIB file from state *)
let state_to_smtlib_string state =
  let buffer = Buffer.create 4096 in

  (* Add SMT-LIB header *)
  Buffer.add_string buffer generate_smtlib_header;

  (* Add variable declarations for both programs *)
  Buffer.add_string buffer (generate_variable_declarations state.source);
  Buffer.add_string buffer (generate_variable_declarations state.target);

  (* Add block assertions for both programs *)
  Buffer.add_string buffer (generate_block_assertions state.source "source");
  Buffer.add_string buffer (generate_block_assertions state.target "target");

  (* Add assignment and operation assertions *)
  Buffer.add_string buffer (generate_assignment_assertions state.source);
  Buffer.add_string buffer (generate_assignment_assertions state.target);

  (* Add initial, effect, and final assertions *)
  Buffer.add_string buffer (generate_initial_assertions state.initial);
  Buffer.add_string buffer (generate_effect_assertions state.effects);
  Buffer.add_string buffer (generate_final_assertions state.final);

  (* Add arbitrary assertions *)
  Buffer.add_string buffer (generate_arbitrary_assertions state);

  (* Add final commands *)
  Buffer.add_string buffer (generate_smtlib_footer ());

  Buffer.contents buffer

(** Generate complete SMT-LIB file from state with custom tactic *)
let state_to_smtlib_tactic_string state tactic =
  let buffer = Buffer.create 4096 in

  (* Add SMT-LIB header *)
  Buffer.add_string buffer generate_smtlib_header;

  (* Add variable declarations for both programs *)
  (*Buffer.add_string buffer (generate_fun_defs state.funs);*)
  Buffer.add_string buffer (generate_variable_declarations state.source);
  Buffer.add_string buffer (generate_variable_declarations state.target);

  (* Add block assertions for both programs *)
  Buffer.add_string buffer (generate_block_assertions state.source "source");
  Buffer.add_string buffer (generate_block_assertions state.target "target");

  (* Add assignment and operation assertions *)
  Buffer.add_string buffer (generate_assignment_assertions state.source);
  Buffer.add_string buffer (generate_assignment_assertions state.target);

  (* Add initial, effect, and final assertions *)
  Buffer.add_string buffer (generate_initial_assertions state.initial);
  Buffer.add_string buffer (generate_effect_assertions state.effects);
  Buffer.add_string buffer (generate_final_assertions state.final);

  (* Add arbitrary assertions *)
  Buffer.add_string buffer (generate_arbitrary_assertions state);

  (* Add custom tactic instead of check-sat *)
  Buffer.add_string buffer (generate_smtlib_tactic_footer tactic);

  Buffer.contents buffer

(** Write state to SMT-LIB file *)
let write_smtlib_file filename state =
  let content = state_to_smtlib_string state in
  let oc = open_out filename in
  output_string oc content;
  close_out oc;
  Printf.printf "SMT-LIB file written: %s\n" filename

(** Write state to SMT-LIB file with custom tactic *)
let write_smtlib_tactic_file filename state tactic =
  let content = state_to_smtlib_tactic_string state tactic in
  let oc = open_out filename in
  output_string oc content;
  close_out oc;
  Printf.printf "SMT-LIB tactic file written: %s\n" filename

(** Create SMT-LIB file with state context and additional content *)
let create_smtlib_file_with_content state content filename =
  let oc = open_out filename in

  (* Write SMT-LIB header *)
  Printf.fprintf oc "%s" generate_smtlib_header;

  (* Write variable declarations for both programs *)
  Printf.fprintf oc "%s" (generate_variable_declarations state.source);
  Printf.fprintf oc "%s" (generate_variable_declarations state.target);

  (* Write the additional content *)
  Printf.fprintf oc "%s" content;

  close_out oc
