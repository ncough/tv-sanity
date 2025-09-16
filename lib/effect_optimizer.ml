(** Effect optimization using incremental CVC5 solving *)

open Data_structures
open Utilities
open Smtlib_output

(** Solver process management *)
type solver_process = {
  stdin: out_channel;
  stdout: in_channel;
  stderr: in_channel;
  debug_log: out_channel option;
}

(** Start incremental CVC5 solver process *)
let start_incremental_solver base_filename =
  let env = Unix.environment () in
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let (proc_in, proc_out, proc_err) = Unix.open_process_full cvc5_path (env) in
  let debug_log =
    if is_debug_enabled () then
      let debug_filename = get_debug_file_path (Filename.basename base_filename ^ "_cvc5_debug.smt2") in
      Some (open_out debug_filename)
    else
      None
  in
  { stdin = proc_out; stdout = proc_in; stderr = proc_err; debug_log }

(** Send command to solver *)
let send_to_solver solver cmd =
  (match solver.debug_log with
   | Some log -> output_string log cmd; flush log
   | None -> ());
  output_string solver.stdin cmd;
  flush solver.stdin

(** Read solver response *)
let read_solver_response solver =
  let line = input_line solver.stdout in
  String.trim line

(** Close solver process *)
let close_solver solver =
  (match solver.debug_log with
   | Some log -> close_out log
   | None -> ());
  close_out solver.stdin;
  ignore (Unix.close_process_full (solver.stdout, solver.stdin, solver.stderr))

let scoped_solve solver_process query =
  send_to_solver solver_process "(push)\n";
  send_to_solver solver_process query;
  send_to_solver solver_process "(check-sat)\n";
  let result = read_solver_response solver_process in
  send_to_solver solver_process "(pop)\n";
  result

(** Generate incremental SMT-LIB base content *)
let generate_incremental_base_smtlib state timeout_ms =
  let buffer = Buffer.create 4096 in

  (* Enable incremental mode *)
  if timeout_ms >= 0 then
    Buffer.add_string buffer (Printf.sprintf "(set-option :tlimit-per %d)\n" timeout_ms);
  Buffer.add_string buffer "(set-option :incremental true)\n";
  Buffer.add_string buffer generate_smtlib_header;

  (* Add variable declarations for both programs *)
  Buffer.add_string buffer (generate_variable_declarations state.source);
  Buffer.add_string buffer (generate_variable_declarations state.target);

  (* Add block assertions for both programs *)
  Buffer.add_string buffer (generate_block_assertions state.source "source");
  Buffer.add_string buffer (generate_block_assertions state.target "target");

  (* Add assignment assertions *)
  Buffer.add_string buffer (generate_assignment_assertions state.source);
  Buffer.add_string buffer (generate_assignment_assertions state.target);

  (* Add ONLY initial invariants *)
  Buffer.add_string buffer (generate_initial_assertions state.initial);

  (* Add all trivial queries (those without reqs) *)
  let trivial_queries = List.filter (fun q -> q.req = []) state.effects in
  List.iter (fun query ->
    if query.ens <> [] then begin
      let query_assertion = generate_effect_query_assertion query in
      Buffer.add_string buffer query_assertion
    end
  ) trivial_queries;

  (* Add arbitrary assertions *)
  Buffer.add_string buffer (generate_arbitrary_assertions state);

  Buffer.contents buffer

(** Query result with timing *)
type 'a query_result =
  | UNKNOWN of 'a  (* timeout/error *)
  | SAT of 'a      (* invalid *)
  | UNSAT of 'a    (* valid *)

(** Results map with timing *)
type results_map = float query_result StringMap.t

let empty_results_map = StringMap.empty

(** Lattice join operation - higher precedence wins, min timing within same result *)
let join_results old_result new_result =
  match old_result, new_result with
  | UNSAT old_time, UNSAT new_time -> UNSAT (min old_time new_time)
  | UNSAT a, _ | _, UNSAT a -> UNSAT a
  | SAT old_time, SAT new_time -> SAT (min old_time new_time)
  | SAT a, _ | _, SAT a -> SAT a
  | UNKNOWN _, UNKNOWN new_time -> UNKNOWN (new_time)

let update_results_map results_map query_name new_result =
  StringMap.update query_name (function
    | None -> Some new_result
    | Some existing_result -> Some (join_results existing_result new_result)
  ) results_map

(** Generate query reachability assertions *)
let generate_query_reachability query =
  let source = Option.get query.source_location in
  let target = Option.get query.target_location in
  Printf.sprintf "(and %s %s)" source target

let test_effect solver_process query complete =
  let req_combined = generate_conjunction query.req in
  let ens_combined = generate_conjunction query.ens in
  let reachable = generate_query_reachability query in

  (* The flow is:
    - Are the blocks that perform these calls mutually reachable?
      - If not, then there is nothing to do, this effect is not possible. SAT
    - Do the requirements for this effect hold given the blocks are reachable?
      - If so, can just inject all of these properties as known constraints.
      - If not, then this effect is unnecessary.

    In reality the injected conditions need to be guarded by reachability,
    though I don't believe the existing transforms can induce the problematic case here.
  *)
  let reach = scoped_solve solver_process (Printf.sprintf "(assert %s)\n" reachable) in
  let result = if reach = "unsat" then "sat" else begin
    let cond = Printf.sprintf "(assert %s)\n(assert (not %s))\n" reachable req_combined in
    scoped_solve solver_process cond
  end in

  match result with
  | "unsat" ->
      send_to_solver solver_process (Printf.sprintf "(assert %s)\n" req_combined);
      send_to_solver solver_process (Printf.sprintf "(assert %s)\n" ens_combined);
      UNSAT  { query with req = [] ; ens = (query.req @ query.ens) }
  | "sat" when complete -> SAT (query)
  | "sat" -> UNKNOWN (query)
  | "unknown" -> UNKNOWN (query)
  | error_msg ->
      debug_printf "ERROR: Solver issue: %s\n" error_msg;
      UNKNOWN (query)

(** Optimize queries using incremental solver and topological query traversal *)
let optimize_queries_incremental state timeout_ms base_filename =
  let solver = start_incremental_solver base_filename in
  send_to_solver solver (generate_incremental_base_smtlib state timeout_ms);

  (* Get topological order of queries based on their predecessors *)
  let queries = Data_structures.query_topo_sort state.effects in
  debug_printf "  Processing %d queries\n" (List.length queries);

  (* Filter out trivial queries first *)
  let (trivial, non_trivial) = List.partition (fun q -> q.req = []) queries in

  let (solved, unsolved, results_map, _, _) = List.fold_left (
    fun (solved, unsolved, results_map, pos, solver) query ->
      let (outcome,elapsed_ms) = get_time (fun _ -> test_effect solver query (unsolved = [])) in
      match outcome with
      | UNSAT query ->
          debug_printf "  [%d] UNSAT in %fms: %s\n" pos elapsed_ms query.qname;
          let updated_results_map = update_results_map results_map query.qname (UNSAT elapsed_ms) in
          (query :: solved, unsolved, updated_results_map, pos+1, solver)
      | SAT _ ->
          debug_printf "  [%d] SAT   in %fms: %s\n" pos elapsed_ms query.qname;
          let updated_results_map = update_results_map results_map query.qname (SAT elapsed_ms) in
          (solved, unsolved, updated_results_map, pos+1, solver)
      | UNKNOWN _ ->
          debug_printf "  [%d] UNKNW in %fms: %s\n" pos elapsed_ms query.qname;
          let updated_results_map = update_results_map results_map query.qname (UNKNOWN elapsed_ms) in
          (solved, query :: unsolved, updated_results_map, pos+1, solver))
      ([], [], empty_results_map, 0, solver) non_trivial
  in

  (* Combine results: trivial queries + solved + unsolved *)
  let effects = trivial @ solved @ List.rev unsolved in
  let removed_count = List.length queries - List.length effects in
  let validated_count = List.length solved in

  debug_printf "  %d -> %d non-trivial queries (removed: %d, validated: %d)\n"
    (List.length non_trivial)
    (List.length unsolved)
    removed_count
    validated_count;

  close_solver solver;

  (* Return state with results data *)
  ({ state with effects}, results_map)

(** Generate GraphViz DOT for query dependencies with results and timing *)
let generate_query_dependency_dot queries results_map =
  let buffer = Buffer.create 1024 in
  Buffer.add_string buffer "digraph QueryDependencies {\n";
  Buffer.add_string buffer "  rankdir=TB;\n";
  Buffer.add_string buffer "  node [shape=box];\n\n";

  (* Add entry node *)
  Buffer.add_string buffer "  \"entry\" [label=\"entry\", fillcolor=\"lightgray\", style=\"filled\", shape=\"ellipse\"];\n\n";

  (* Calculate maximum time from results map *)
  let max_time_ms =
    StringMap.fold (fun _ result acc ->
      let time_ms = match result with
        | UNSAT t | SAT t | UNKNOWN t -> t
      in
      max acc time_ms
    ) results_map 1.0 in (* minimum 1ms to avoid division by zero *)

  (* Helper function for colors based on result type and timing *)
  let get_result_color_with_timing result max_time =
    let (hue, time_ms) = match result with
      | UNSAT t -> (0.33, t)  (* Green hue *)
      | SAT t -> (0.0, t)     (* Red hue *)
      | UNKNOWN t -> (0.17, t) (* Yellow hue *)
    in
    (* Calculate intensity based on time ratio (0.0 to 1.0) *)
    let time_ratio = if max_time > 0.0 then min 1.0 (time_ms /. max_time) else 0.0 in
    (* Scale saturation and value based on timing *)
    let saturation = 0.4 +. (time_ratio *. 0.6) in  (* 0.4 to 1.0 *)
    let value = 1.0 -. (time_ratio *. 0.3) in        (* 1.0 to 0.7 *)
    (* Format as HSV: H S V where all values are 0.0 to 1.0 *)
    Printf.sprintf "\"%.2f %.2f %.2f\"" hue saturation value
  in

  (* Add all query nodes with colors and timing information *)
  List.iter (fun query ->
    let short_name =
      if String.length query.qname > 50 then
        String.sub query.qname 0 17 ^ "..."
      else query.qname
    in

    (* Get result and timing info from unified map *)
    let (result_color, timing_label) =
      match StringMap.find_opt query.qname results_map with
      | Some result ->
          let color = get_result_color_with_timing result max_time_ms in
          let time_ms = match result with
            | UNSAT t | SAT t | UNKNOWN t -> t
          in
          (color, Printf.sprintf "%s\\n(%.1fms)" short_name time_ms)
      | None ->
          (* Trivial query - no entry in results map *)
          ("\"lightblue\"", short_name)
    in

    Buffer.add_string buffer (Printf.sprintf "  \"%s\" [label=\"%s\", fillcolor=%s, style=\"filled\"];\n"
      query.qname timing_label result_color)
  ) queries;

  Buffer.add_string buffer "\n";

  (* Add legend *)
  Buffer.add_string buffer "  subgraph cluster_legend {\n";
  Buffer.add_string buffer (Printf.sprintf "    label=\"Legend (darker = longer time, max: %.1fms)\";\n" max_time_ms);
  Buffer.add_string buffer "    style=\"filled\";\n";
  Buffer.add_string buffer "    fillcolor=\"white\";\n";
  Buffer.add_string buffer "    \"UNSAT (fast)\" [fillcolor=\"0.33 0.40 1.00\", style=\"filled\"];\n";
  Buffer.add_string buffer "    \"UNSAT (slow)\" [fillcolor=\"0.33 1.00 0.70\", style=\"filled\"];\n";
  Buffer.add_string buffer "    \"SAT (fast)\" [fillcolor=\"0.00 0.40 1.00\", style=\"filled\"];\n";
  Buffer.add_string buffer "    \"SAT (slow)\" [fillcolor=\"0.00 1.00 0.70\", style=\"filled\"];\n";
  Buffer.add_string buffer "    \"UNKNOWN (fast)\" [fillcolor=\"0.17 0.40 1.00\", style=\"filled\"];\n";
  Buffer.add_string buffer "    \"UNKNOWN (slow)\" [fillcolor=\"0.17 1.00 0.70\", style=\"filled\"];\n";
  Buffer.add_string buffer "    \"Trivial\" [fillcolor=\"lightblue\", style=\"filled\"];\n";
  Buffer.add_string buffer "  }\n\n";

  (* Add predecessor edges *)
  List.iter (fun query ->
    StringSet.iter (fun pred_name ->
      Buffer.add_string buffer (Printf.sprintf "  \"%s\" -> \"%s\";\n" pred_name query.qname)
    ) query.preds
  ) queries;

  Buffer.add_string buffer "}\n";
  Buffer.contents buffer

(** Main entry point for query optimization *)
let optimize_queries_to_fixpoint state timeout_ms base_filename =
  (* Run optimization and collect results *)
  let (state_out, results_map) = optimize_queries_incremental state timeout_ms base_filename in

  (* Generate query dependency visualization with results and timing *)
  if is_debug_enabled () then begin
    let dot_content = generate_query_dependency_dot state.effects results_map in
    let dot_filename = get_debug_file_path (Filename.basename base_filename ^ "_query_dependencies.dot") in
    let dot_file = open_out dot_filename in
    output_string dot_file dot_content;
    close_out dot_file;
    debug_printf "  Query dependency graph written to %s\n" dot_filename
  end;

  state_out
