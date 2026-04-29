(** Effect optimization using incremental SMT solving *)

open Data_structures
open Utilities
open Smtlib_output
open Incremental_solver

(** Emit the incremental base assertions (shared across all effect queries) *)
let emit_incremental_base solver state =
  emit_block_assertions solver state.source "source";
  emit_block_assertions solver state.target "target";
  emit_assignment_assertions solver state.source;
  emit_assignment_assertions solver state.target;
  emit_arbitrary_assertions solver state

(** Results map with timing *)
type results_map = (unit result * float) StringMap.t

let add_result results name (r, ms') =
  StringMap.update name (function
    | None -> Some (r, ms')
    | Some (SOLVED, ms) -> Some (SOLVED, ms +. ms')
    | Some (UNSOLVED l, ms) ->
        match r with
        | SOLVED -> Some (SOLVED, ms +. ms')
        | UNSOLVED l' -> Some (UNSOLVED (l @ l'), ms +. ms'))
  results

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

let collect_assumed solver req_sexps =
  let solved_all = ref true in
  let rec walk facts sexp =
    match sexp with
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: conjuncts) ->
        List.iter (walk facts) conjuncts
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "=>" :: [antecedent; consequent]) ->
        walk (facts @ [antecedent]) consequent
    | leaf ->
        let neg = Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "not"; leaf] in
        let t0 = Unix.gettimeofday () in
        let result = scoped_probe solver (fun s ->
          List.iter s.assert_ facts;
          s.assert_ neg) in
        let ms = (Unix.gettimeofday () -. t0) *. 1000.0 in
        if result <> "unsat" then begin
          let extra = Printf.sprintf "(check-sat-assuming (%s (not %s)))\n"
            (String.concat " " (List.map sexp_to_smtlib facts))
            (sexp_to_smtlib leaf) in
          dump_version ~extra solver "hard";
          debug_printf "\n      [hard] %s: %s in %.2fms\n"
            result (sexp_to_smtlib leaf) ms;
          solved_all := false
        end
  in
  List.iter (walk []) req_sexps;
  !solved_all

let breakdown sexps =
  let rec walk facts sexp =
    match sexp with
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: conjuncts) ->
        List.flatten (List.map (walk facts) conjuncts)
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "=>" :: [antecedent; consequent]) ->
        walk (facts @ [antecedent]) consequent
    | leaf -> [mk_imp facts [leaf]] in
  List.flatten (List.map (walk []) sexps)

let collapse_sequential queries = 
  let (query_map, succ_count) = List.fold_left (fun (m,s) query ->
    let m = StringMap.add query.qname query m in
    let s = StringSet.fold (fun pred ->
      StringMap.update pred (function Some v -> Some (v + 1) | None -> Some 1)
    ) query.preds s in
    (m,s)
  ) (StringMap.empty, StringMap.empty) queries in

  let visited = ref StringSet.empty in

  let rec consume query =
    if StringMap.find_opt query.qname succ_count <> Some 1 then query
    else 


  List.fold_left (fun acc (query:query) ->
    if StringSet.mem query.qname !visited then acc
    else if StringMap.find_opt query.qname succ_count <> Some 1 then query::acc
    else consume query


    | _ -> acc) [] query


 
  (* 
     - for a given node, ask if it has a single successor
     - ask if that single successor has a single predecessor
     - if so, merge 
   *)

let rec dominator_solve count depth solver eff doms results imm_exit =
  debug_printf "  [%d,%d] %s - " !count depth eff.qname;
  flush_all ();
  count := !count + 1;

  (*
  let start_time = Unix.gettimeofday () in
  let reqs = breakdown (List.map (fun p -> p.term) eff.req) in
  let (solved,remaining) = List.partition (fun term -> 
    (*debug_printf "solving: %s\n" (pp_sexp term);*)
    let result = scoped_probe solver (fun s -> s.assert_ (mk_not term))  in
    result = "unsat") reqs in
  let ms = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  debug_printf "early split %d %d in %.2fms -" (List.length solved) (List.length remaining) ms;
  *)

  let req_sexp   = conjunction_sexp eff.req in
  let ens_sexp   = conjunction_sexp eff.ens in
  let reach_sexp = reachability_sexp eff in
  let name = eff.qname in
  let start_time = Unix.gettimeofday () in

  let not_req = mk_not req_sexp in

  let uncond_req = scoped_probe solver (fun s -> s.assert_ not_req) in
  let outcome = if uncond_req = "unsat" then "TRIVIAL" else begin
    solver.push ();
    solver.assert_ reach_sexp;
    match solver.check_sat () with
    | "unsat" -> "UNRCH"
    | _ ->
        match scoped_probe solver (fun s -> s.assert_ not_req) with
        | "sat"   -> "SAT"
        | "unsat" -> "UNSAT"
        | _ ->
            let solved =
              collect_assumed solver (List.map (fun p -> p.term) eff.req) in
            if solved then "UNSAT" else failwith "UNKNOWN"
  end in

  match outcome with
  | "UNRCH" ->
      solver.pop ();
      let ms = (Unix.gettimeofday () -. start_time) *. 1000.0 in
      debug_printf "%s in %.2fms\n" outcome ms;
      results := add_result !results name (UNSOLVED [], ms);
      None

  | "SAT"
  | "TRIVIAL"
  | "UNSAT" ->
      let ms = (Unix.gettimeofday () -. start_time) *. 1000.0 in
      debug_printf "%s in %.2fms\n" outcome ms;
      let v = if outcome = "SAT" then SOLVED else UNSOLVED [] in
      results := add_result !results name (v, ms);

      (* *)
      if outcome <> "SAT" then begin
        solver.assert_ req_sexp;
        solver.assert_ ens_sexp
      end;

      let sub_queries =
        match StringMap.find_opt eff.qname doms with
        | Some v -> v
        | None   -> []
      in
      let sub_results = List.filter_map (fun query ->
        dominator_solve count (depth + 1) solver query doms results imm_exit
      ) sub_queries in

      (match StringMap.find_opt eff.qname imm_exit with
      | Some exits ->
          debug_printf "  EXIT SPLIT START\n";
          if outcome = "TRIVIAL" then begin
            solver.push ();
            solver.assert_ reach_sexp
          end;
          List.iter (fun exit ->
            ignore (dominator_solve count (depth + 1) solver exit doms results imm_exit)
          ) exits;
          if outcome = "TRIVIAL" then solver.pop ();
          debug_printf "  EXIT SPLIT DONE\n"
      | None -> ());

      let global = ens_sexp::(List.flatten (List.map fst sub_results)) in
      let spec = req_sexp::(List.flatten (List.map snd sub_results)) in

      if outcome = "TRIVIAL" then
        Some (global, spec)
      else if outcome = "SAT" then begin
        solver.pop ();
        None
      end else begin
        solver.pop ();
        let global = (mk_imp reach_sexp (mk_and spec))::global in
        solver.assert_ (mk_and global);
        Some (global, [])
      end
  | _ -> failwith "unreachable"

let collect_splits queries depth =
  let query_map = List.fold_left (fun acc query ->
    StringMap.add query.qname query acc
  ) StringMap.empty queries in
  let visited = ref StringSet.empty in
  let rec walk depth query_name =
    if depth > 0 && not (StringSet.mem query_name !visited) then begin
      visited := StringSet.add query_name !visited;
      let preds =
        match StringMap.find_opt query_name query_map with
        | Some v -> v.preds
        | None   -> StringSet.empty
      in
      StringSet.iter (walk (depth - 1)) preds
    end
  in
  List.iter (fun q ->
    if Data_structures.is_an_exit q then walk depth q.qname
  ) queries;
  let changed = ref true in
  visited := StringSet.remove "entry" !visited;
  while !changed do
    changed := false;
    List.iter (fun q ->
      if StringSet.mem q.qname !visited then () else
        StringSet.iter (fun p ->
          if StringSet.mem p !visited then begin
            changed := true;
            visited := StringSet.remove p !visited
          end) q.preds
    ) queries
  done;
  List.partition (fun q -> StringSet.mem q.qname !visited) queries

let scoped_solve_effects solver effects =
  let (exits, effects) = collect_splits effects 1 in
  let topo_effects = Data_structures.query_topo_sort effects in
  debug_printf "  Processing %d effects, %d split\n"
    (List.length topo_effects) (List.length exits);
  let doms  = Data_structures.dom_tree topo_effects in
  let entry = List.hd topo_effects in
  let count   = ref 0 in
  let results = ref StringMap.empty in

  let imm_exit = List.fold_left (fun acc (q : query) ->
    StringSet.fold (fun pred -> StringMap.update pred (function
      | Some e -> Some (q :: e)
      | None   -> Some [q]
    )) q.preds acc
  ) StringMap.empty exits in

  ignore (dominator_solve count 0 solver entry doms results imm_exit);
  !results

let generate_query_dependency_dot queries results_map =
  let buffer = Buffer.create 1024 in
  Buffer.add_string buffer "digraph QueryDependencies {\n";
  Buffer.add_string buffer "  rankdir=TB;\n";
  Buffer.add_string buffer "  node [shape=box];\n\n";
  Buffer.add_string buffer
    "  \"entry\" [label=\"entry\", fillcolor=\"lightgray\", style=\"filled\", shape=\"ellipse\"];\n\n";

  let max_time_ms =
    StringMap.fold (fun _ result acc ->
      max acc (snd result)
    ) results_map 1.0
  in

  let get_color result max_time =
    let (hue, time_ms) = match result with
      | UNSOLVED [], t -> (0.33, t)
      | SOLVED, t      -> (0.0,  t)
      | UNSOLVED _, t  -> (0.17, t)
    in
    let time_ratio = if max_time > 0.0 then min 1.0 (time_ms /. max_time) else 0.0 in
    let saturation = 0.4 +. (time_ratio *. 0.6) in
    let value      = 1.0 -. (time_ratio *. 0.3) in
    Printf.sprintf "\"%.2f %.2f %.2f\"" hue saturation value
  in

  List.iter (fun query ->
    let short_name =
      if String.length query.qname > 50
      then String.sub query.qname 0 17 ^ "..."
      else query.qname
    in
    let (result_color, timing_label) =
      match StringMap.find_opt query.qname results_map with
      | Some result ->
          (get_color result max_time_ms,
           Printf.sprintf "%s\\n(%.1fms)" short_name (snd result))
      | None ->
          ("\"lightblue\"", short_name)
    in
    Buffer.add_string buffer
      (Printf.sprintf "  \"%s\" [label=\"%s\", fillcolor=%s, style=\"filled\"];\n"
         query.qname timing_label result_color)
  ) queries;

  Buffer.add_string buffer "\n";
  Buffer.add_string buffer "  subgraph cluster_legend {\n";
  Buffer.add_string buffer
    (Printf.sprintf "    label=\"Legend (darker = longer time, max: %.1fms)\";\n"
       max_time_ms);
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

  List.iter (fun query ->
    StringSet.iter (fun pred_name ->
      Buffer.add_string buffer
        (Printf.sprintf "  \"%s\" -> \"%s\";\n" pred_name query.qname)
    ) query.preds
  ) queries;

  Buffer.add_string buffer "}\n";
  Buffer.contents buffer


let run state timeout_ms _enable_z3_simplify _enable_scope enable_multi_solver enable_cascade_solver =
  let solver =
    if enable_cascade_solver    then begin_cascade_solver state timeout_ms
    else if enable_multi_solver then begin_concurrent_solver   state timeout_ms
    else                             begin_solver         state timeout_ms
  in
  emit_incremental_base solver state;

  let filter_effects = Data_structures.reach_exit state.effects in
  let results_map = scoped_solve_effects solver filter_effects in

  if is_debug_enabled () then begin
    let dot_content = generate_query_dependency_dot state.effects results_map in
    let dot_filename = get_debug_file_path "query_dependencies.dot" in
    let dot_file = open_out dot_filename in
    output_string dot_file dot_content;
    close_out dot_file;
    debug_printf "  Query dependency graph written to %s\n" dot_filename
  end;

  let acc = StringMap.fold (fun k (r, _) acc ->
    if String.starts_with ~prefix:"exit" k then
      match acc, r with
      | UNSOLVED l, UNSOLVED l2 -> UNSOLVED (l @ l2)
      | SOLVED, _ | _, SOLVED   -> SOLVED
    else acc
  ) results_map (UNSOLVED []) in

  match acc with
  | SOLVED      -> SOLVED
  | UNSOLVED [] -> UNSOLVED []
  | UNSOLVED final -> UNSOLVED [({state with effects = final}, "")]

