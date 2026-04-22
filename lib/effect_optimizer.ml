(** Effect optimization using incremental CVC5 solving *)

open Data_structures
open Utilities
open Smtlib_output
open Incremental_solver

(** Generate incremental SMT-LIB base content with Z3 simplification *)
let generate_incremental_base state =
  (* Create base content for Z3 simplification (without declarations) *)
  let base_buffer = Buffer.create 4096 in

  (* Add block assertions for both programs *)
  Buffer.add_string base_buffer (generate_block_assertions state.source "source");
  Buffer.add_string base_buffer (generate_block_assertions state.target "target");

  (* Add assignment assertions *)
  Buffer.add_string base_buffer (generate_assignment_assertions state.source);
  Buffer.add_string base_buffer (generate_assignment_assertions state.target);

  (* Add all trivial effects (those without reqs) *)
  List.iter (fun eff ->
    if eff.req = [] && eff.ens <> [] then begin
      let query_assertion = generate_effect_query_assertion eff in
      Buffer.add_string base_buffer query_assertion
    end
  ) state.effects;

  (* Add arbitrary assertions *)
  Buffer.add_string base_buffer (generate_arbitrary_assertions state);

  Buffer.contents base_buffer

(** Results map with timing *)
type results_map = (unit result * float) StringMap.t

let add_result results name result =
  StringMap.update name (function
    | None -> Some result
    | Some _ -> Some result(*failwith @@ "Reprocessed result: " ^ name*)
  ) results

(** Generate query reachability assertions *)
let generate_query_reachability query =
  let source = Option.get query.source_location in
  let target = Option.get query.target_location in
  Printf.sprintf "(and %s %s)" source target

let test_effect solver eff decidable =
  let req_combined = generate_conjunction eff.req in
  let ens_combined = generate_conjunction eff.ens in
  let reachable = generate_query_reachability eff in

  (* The flow is:
    - Are the blocks that perform these calls mutually reachable?
      - If not, then there is nothing to do, this effect is not possible. SAT
    - Do the requirements for this effect hold given the blocks are reachable?
      - If so, can just inject all of these properties as known constraints.
      - If not, then this effect is unnecessary.

    In reality the injected conditions need to be guarded by reachability,
    though I don't believe the existing transforms can induce the problematic case here.
  *)
  let cmt = Printf.sprintf "Reach %s" eff.qname in
  match scoped_solve ~cmt solver (Printf.sprintf "(assert %s)\n" reachable) with
  | UNSOLVED [] ->
      debug_printf "UNRCH";
      SOLVED
  | _ ->
      let cond = Printf.sprintf "(assert %s)\n(assert (not %s))\n" reachable req_combined in
      let cmt = Printf.sprintf "Solve %s" eff.qname in
      let req_result = scoped_solve ~cmt solver cond in
      match req_result with
      | UNSOLVED [] ->
          debug_printf "UNSAT";
          send_to_solver solver (Printf.sprintf "(assert %s)\n" ens_combined);
          send_to_solver solver (Printf.sprintf "(assert (=> %s %s))\n" reachable req_combined);
          UNSOLVED []
      | SOLVED when decidable ->
          debug_printf "SAT  ";
          SOLVED
      | SOLVED ->
          debug_printf "SAT? ";
          UNSOLVED [eff]
      | UNSOLVED _ ->
          debug_printf "UNKNW";
          send_to_solver solver (generate_effect_query_assertion eff);
          UNSOLVED [eff]

(**
  Look at predecessor outcomes to determine a series of properties:
    - At least one predecessor is UNSAT, there is a possibility this is UNSAT.
    - At least one predecessor un UNKNOWN, not decidable.
    - All predecessors are SAT, this must be SAT.
  *)
let shortcuts (eff : query) results =
  if eff.qname = "entry" then (true,false,false) else
  let (unsat,sat,unknown) = StringSet.fold (fun name (unsat,sat,unknown) ->
    match StringMap.find name results with
    | (UNSOLVED [],_) -> (unsat+1,sat,unknown)
    | (SOLVED,_) -> (unsat,sat+1,unknown)
    | (UNSOLVED _,_) -> (unsat,sat,unknown+1)
  ) eff.preds (0,0,0) in
  (unsat > 0, unknown > 0, unsat = 0 && unknown = 0 && sat > 0)

let rec dominator_solve count depth solver eff doms solved results imm_exit =
  debug_printf "  [%d,%d] %s - " !count depth eff.qname;
  flush_all ();
  count := !count + 1;
  let start_time = Unix.gettimeofday () in
  send_to_solver solver "(push)\n";
  let req_combined = generate_conjunction eff.req in
  let ens_combined = generate_conjunction eff.ens in
  let reachable = generate_query_reachability eff in

  let name = eff.qname in

  let reach_cond = Printf.sprintf "(assert %s)\n" reachable in
  send_to_solver solver reach_cond;
  send_to_solver solver "(check-sat)\n";
  let result = read_solver_response solver in
  match result with
  | "unsat" ->
      send_to_solver solver "(pop)\n";
      let end_time = Unix.gettimeofday () in
      let ms = ((end_time -. start_time) *. 1000.0) in
      debug_printf "UNRCH in %.2fms\n" ms;
      results := add_result !results name (SOLVED,ms);
      ""
  | _ ->
      send_to_solver solver "(push)\n";
      let inv_req_cond = Printf.sprintf "(assert (not %s))\n" req_combined in
      send_to_solver solver inv_req_cond;
      send_to_solver solver "(check-sat)\n";
      let result = read_solver_response solver in
      send_to_solver solver "(pop)\n";
      match result with
      | "sat" ->
          send_to_solver solver "(pop)\n";
          let end_time = Unix.gettimeofday () in
          let ms = ((end_time -. start_time) *. 1000.0) in
          debug_printf "SAT in %.2fms\n" ms;
          results := add_result !results name (SOLVED,ms);
          ""
      |  _ ->
          let suc = (result = "unsat") in
          let end_time = Unix.gettimeofday () in
          let ms = ((end_time -. start_time) *. 1000.0) in
          debug_printf "%s in %.2fms\n" (if suc then "UNSAT" else "UNKNOWN") ms;
          results := add_result !results name (UNSOLVED (if suc then [] else [eff]),ms);
          if suc then solved := {eff with req = []; ens = eff.req @ eff.ens} :: !solved;
          let cond = if suc then
            Printf.sprintf "(assert %s)\n(assert %s)\n" req_combined ens_combined
          else
            Printf.sprintf "(assert (=> %s %s))\n" req_combined ens_combined
          in
          send_to_solver solver cond;
          let sub_queries = match StringMap.find_opt eff.qname doms with Some v -> v | _ -> [] in
          let inner = List.fold_left (fun sides query ->
            let inner = dominator_solve count (depth + 1) solver query doms solved results imm_exit in
            sides ^ inner
          ) "" sub_queries in

          (match StringMap.find_opt eff.qname imm_exit with
          | Some exit ->
              debug_printf "  EXIT SPLIT START\n";
              List.iter (fun exit ->
                ignore (dominator_solve count (depth + 1) solver exit doms solved results imm_exit)
              ) exit;
              debug_printf "  EXIT SPLIT DONE\n";
          | None -> ());

          send_to_solver solver "(pop)\n";

          (* register results here *)
          let guarded = if suc then
            Printf.sprintf "%s\n(assert %s)\n(assert (=> %s %s))\n" inner ens_combined reachable req_combined
          else
            Printf.sprintf "%s\n(assert (=> %s %s))\n" inner req_combined ens_combined
          in
          send_to_solver solver guarded;
          guarded

let collect_splits queries depth =
  let query_map = List.fold_left (fun acc query ->
    StringMap.add query.qname query acc
  ) StringMap.empty queries in
  let visited = ref StringSet.empty in
  let rec walk depth query_name =
    if depth > 0 && not (StringSet.mem query_name !visited) then begin
      visited := StringSet.add query_name !visited;
      let preds = match StringMap.find_opt query_name query_map with Some(v) -> v.preds | None -> StringSet.empty in
      StringSet.iter (walk (depth - 1)) preds
    end
  in
  walk depth "exit";
  List.partition (fun q -> StringSet.mem q.qname !visited) queries

let scoped_solve_effects solver effects =
  let (exits,effects) = collect_splits effects 1 in
  let topo_effects = Data_structures.query_topo_sort effects in
  debug_printf "  Processing %d effects, %d split\n" (List.length topo_effects) (List.length exits);
  let doms = Data_structures.dom_tree topo_effects in
  let entry = List.hd topo_effects in
  let count = ref 0 in
  let solved = ref [] in
  let results = ref StringMap.empty in

  let imm_exit = List.fold_left (fun acc (q:query) ->
      StringSet.fold (fun pred -> StringMap.update pred (function
        | Some e -> Some (q::e)
        | None -> Some ([q])
  )) q.preds acc
  ) StringMap.empty exits in

  let (_,ms)= get_time (fun _ -> dominator_solve count 0 solver entry doms solved results imm_exit) in
  Printf.printf "SOLVED IN %.2fms\n" ms;
  (!solved, !results)

(** Solve conditions on effects by processing their conditions in topological order using an
    incremental SMT solver. *)
let solve_effects solver effects =
  (* Get topological order of queries based on their predecessors *)
  let topo_effects = Data_structures.query_topo_sort effects in

  (* Filter out trivial queries *)
  let (trivial, non_trivial) = List.partition (fun q -> q.req = []) topo_effects in
  let results = List.fold_right
    (fun eff -> StringMap.add eff.qname (UNSOLVED [],0.0)) trivial StringMap.empty in

  debug_printf "  Processing %d effects\n" (List.length non_trivial);

  let ((solved, unsolved, results, _),ms) = get_time (fun _ -> List.fold_left (
    fun (solved, unsolved, results, pos) eff ->
      let name = eff.qname in
      debug_printf "  [%d] " pos;
      let (outcome,elapsed_ms) = get_time (fun _ ->
        let (solvable, _, quick_sat) = shortcuts eff results in
        if quick_sat then begin
          debug_printf "SAT!";
          SOLVED
        end else if solvable then test_effect solver eff  true (*(not undecidable)*) else begin
          debug_printf "UNSOV";
          send_to_solver solver (generate_effect_query_assertion eff);
          UNSOLVED [eff]
        end
      ) in
      debug_printf " in %.2fms: %s\n" elapsed_ms name;
      let (solved,unsolved) = (match outcome with
      | UNSOLVED [] -> ({eff with req = []; ens = eff.req @ eff.ens} :: solved, unsolved)
      | SOLVED -> (solved, unsolved)
      | UNSOLVED _ -> (solved, eff :: unsolved)) in
      (solved,unsolved,add_result results name (outcome,elapsed_ms),pos+1)
    ) ([], [], results, 0) non_trivial)
  in

  debug_printf "SOLVED IN %.2fms\n" ms;

  (* Combine results: trivial queries + solved + unsolved *)
  let reduced_effects = trivial @ solved @ List.rev unsolved in
  let removed_count = List.length effects - List.length reduced_effects in
  let validated_count = List.length solved in

  debug_printf "  %d -> %d non-trivial effects (removed: %d, validated: %d)\n"
    (List.length non_trivial)
    (List.length unsolved)
    removed_count
    validated_count;

  (* Return state with results data *)
  (reduced_effects, results)

let solve_goal solver (goal,pos) =
  let cmt = Printf.sprintf "final-%d" pos in
  let cond = Printf.sprintf "(assert (not %s))\n" (pp_sexp goal.term) in
  let pp = pp_sexp goal.term in
  let pp = if String.length pp > 100 then String.sub pp 0 100 else pp in
  let (res,time) = get_time (fun _ -> scoped_solve ~cmt solver cond) in
  debug_printf "  [%d] %s in %.2fms: %s\n" pos (pp_result res) time pp;
  result_map (fun _ -> goal) res

let solve_goals solver effects =
  assert (List.length effects = 1);
  let ef = List.hd effects in
  assert (ef.qname = "exit");
  let goals = ef.req in
  debug_printf "  Attempting to solve %d goals\n" (List.length goals);
  let igoals = List.mapi (fun pos goal -> (goal,pos)) goals in
  match result_bind (UNSOLVED igoals) (solve_goal solver) with
  | SOLVED -> SOLVED
  | UNSOLVED [] -> UNSOLVED []
  | UNSOLVED req -> UNSOLVED [{ef with req}]

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
      let time_ms = snd result in
      max acc time_ms
    ) results_map 1.0 in (* minimum 1ms to avoid division by zero *)

  (* Helper function for colors based on result type and timing *)
  let get_result_color_with_timing result max_time =
    let (hue, time_ms) = match result with
      | UNSOLVED [], t -> (0.33, t)  (* Green hue *)
      | SOLVED,t -> (0.0, t)     (* Red hue *)
      | UNSOLVED _, t -> (0.17, t) (* Yellow hue *)
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
          let time_ms = snd result in
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
let run state timeout_ms enable_z3_simplify enable_scope =
  let base = generate_incremental_base state in
  let@ base = if enable_z3_simplify then Z3_solver.simplify state base else UNSOLVED [base] in
  let solver = begin_solver state timeout_ms base in

  (* Don't need effects that can't influence exit *)
  let filter_effects = Data_structures.reach_exit state.effects in

  (* Run solver over the effects *)
  if enable_scope then
    let (_, results_map) = scoped_solve_effects solver filter_effects in

    (* Generate query dependency visualization with results and timing *)
    if is_debug_enabled () then begin
      let dot_content = generate_query_dependency_dot state.effects results_map in
      let dot_filename = get_debug_file_path "query_dependencies.dot" in
      let dot_file = open_out dot_filename in
      output_string dot_file dot_content;
      close_out dot_file;
      debug_printf "  Query dependency graph written to %s\n" dot_filename
    end;

    UNSOLVED []
  else begin
    let (final,effects) = List.partition (fun q -> q.qname = "exit") filter_effects in
    let (effects, results_map) = solve_effects solver effects in

    (* Generate query dependency visualization with results and timing *)
    if is_debug_enabled () then begin
      let dot_content = generate_query_dependency_dot state.effects results_map in
      let dot_filename = get_debug_file_path "query_dependencies.dot" in
      let dot_file = open_out dot_filename in
      output_string dot_file dot_content;
      close_out dot_file;
      debug_printf "  Query dependency graph written to %s\n" dot_filename
    end;

    match solve_goals solver final with
    | SOLVED -> SOLVED
    | UNSOLVED [] -> UNSOLVED []
    | UNSOLVED final -> UNSOLVED ([{state with effects = effects @ final }])
  end
