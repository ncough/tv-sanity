(** Effect optimization using incremental SMT solving *)

open Data_structures
open Utilities
open Smtlib_output

exception Sat_outcome

type outcome =
  Sat | Unsat | Unreach | Trivial

let pp_outcome = function
  | Sat -> "SAT"
  | Unsat -> "UNSAT"
  | Unreach -> "UNRCH"
  | Trivial -> "TRIVIAL"

let join_outcome a b =
  match a, b with
  | Sat, _ 
  | _, Sat -> Sat
  | Unsat, _ 
  | _, Unsat -> Unsat
  | Trivial, _ 
  | _, Trivial -> Trivial
  | _ -> Unreach

(** Results map with timing *)
type results_map = (outcome * float) StringMap.t
let add_result results name (r, ms') =
  StringMap.update name (function
    | None -> Some (r, ms')
    | Some (Sat, ms) -> Some (Sat, ms +. ms')
    | Some (a, ms) -> Some (join_outcome a r, ms +. ms'))
  results

let can_reach_exit queries =
  let query_map = List.fold_left (fun acc query ->
    StringMap.add query.qname query acc
  ) StringMap.empty queries in
  let visited = ref StringSet.empty in
  let rec walk query_name =
    if not (StringSet.mem query_name !visited) then begin
      visited := StringSet.add query_name !visited;
      let (query:query) = StringMap.find query_name query_map in
      StringSet.iter walk query.preds
    end
  in
  List.iter (fun q -> if is_an_exit q then walk q.qname) queries;
  List.filter (fun q -> StringSet.mem q.qname !visited) queries

let collect_assumed (module S : Solver.Solver) req_sexps =
  let solved_all = ref Solver.Unsat in
  let rec walk facts sexp =
    match sexp with
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "and" :: conjuncts) ->
        List.iter (walk facts) conjuncts
    | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "=>" :: [antecedent; consequent]) ->
        walk (facts @ [antecedent]) consequent
    | leaf ->
        debug_printf "    %s: " (pp_sexp leaf);
        let t0 = Unix.gettimeofday () in
        let result = S.check_sat_assuming ((mk_not leaf)::facts) in
        let ms = (Unix.gettimeofday () -. t0) *. 1000.0 in
        solved_all := Solver.and_r !solved_all result;
        debug_printf "%s in %.2fms\n" (Solver.pp_r result) ms
  in
  List.iter (walk []) req_sexps;
  !solved_all

let collapse_sequential queries =
  let single_succ = List.fold_left (fun acc (query:query) ->
    StringSet.fold (fun pred ->
      StringMap.update pred (function
        | None -> Some (Some query)
        | _ -> Some None)
    ) query.preds acc
  ) StringMap.empty queries in
  let visited = ref StringSet.empty in
  let rec consume query =
    match StringMap.find_opt query.qname single_succ with
    | Some (Some succ) when StringSet.cardinal succ.preds = 1 ->
        visited := StringSet.add succ.qname !visited;
        let succ = consume succ in
        {
          qname = succ.qname ;
          req = query.req @ succ.req ;
          ens = query.ens @ succ.ens ;
          preds = query.preds ;
          source_location = succ.source_location ;
          target_location = succ.target_location ;
        }
    | _ -> query
  in
  let reduced = List.fold_left (fun acc (query:query) ->
    if StringSet.mem query.qname !visited then acc
    else (consume query)::acc
  ) [] queries
  in
  List.rev reduced

let rec dominator_solve (module S : Solver.Solver) count depth eff doms results imm_exit =
  debug_printf "  [%d,%d] %s - " !count depth eff.qname;
  count := !count + 1;
  let req_sexp   = conjunction_sexp eff.req in
  let ens_sexp   = conjunction_sexp eff.ens in
  let reach_sexp = reachability_sexp eff in
  let name = eff.qname in
  let start_time = Unix.gettimeofday () in
  let not_req = mk_not req_sexp in

  let rec try_forever terms =
    match collect_assumed (module S) terms with
    | Solver.Sat -> Sat
    | Solver.Unsat -> Unsat
    | _ -> try_forever terms
  in

  let outcome = match S.check_sat_assuming [ens_sexp; not_req] with
  | Solver.Unsat -> Trivial
  | _ ->
      begin
        S.push ();
        S.add ens_sexp;
        S.add reach_sexp;
        match S.check_sat_assuming []  with
        | Solver.Unsat -> Unreach
        | _ ->
            match S.check_sat_assuming [not_req] with
            | Solver.Sat -> Sat
            | Solver.Unsat -> Unsat
            | _ -> try_forever (List.map (fun p -> p.term) eff.req)
      end
  in

  let ms = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  debug_printf "%s in %.2fms\n" (pp_outcome outcome) ms;
  results := add_result !results name (outcome, ms);

  match outcome with
  | Unreach ->
      S.pop ();
      None
  | Sat -> raise Sat_outcome
  | _ ->
      if outcome = Trivial then S.add ens_sexp;
      S.add req_sexp;
      let sub_queries =
        match StringMap.find_opt eff.qname doms with
        | Some v -> v
        | None   -> []
      in
      let sub_results = List.filter_map (fun query ->
        dominator_solve (module S) count (depth + 1) query doms results imm_exit
      ) sub_queries in

      (match StringMap.find_opt eff.qname imm_exit with
      | Some exits ->
          if outcome = Trivial then begin
            S.push ();
            S.add reach_sexp
          end;
          List.iter (fun exit ->
            ignore (dominator_solve (module S) count (depth + 1) exit doms results imm_exit)
          ) exits;
          if outcome = Trivial then S.pop ();
      | None -> ());

      let global = ens_sexp::(List.flatten (List.map fst sub_results)) in
      let spec = req_sexp::(List.flatten (List.map snd sub_results)) in

      if outcome = Trivial then
        Some (global, spec)
      else begin
        S.pop ();
        let global = (mk_imp [reach_sexp] spec)::global in
        S.add (mk_and global);
        Some (global, [])
      end


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

  ignore (dominator_solve solver count 0 entry doms results imm_exit);
  !results

let generate_query_dependency_dot queries (results_map: results_map) =
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
      | Unsat, t    -> (0.33, t)
      | Trivial, t    -> (0.33, t)
      | Sat, t      -> (0.0,  t)
      | Unreach, t  -> (0.17, t)
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

let run solver queries =
  (* Remove queries that can't help to show exits *)
  let filtered = can_reach_exit queries in

  (* Split the exit queries from all others *)
  let (exits, nonexit) = collect_splits filtered 1 in

  (* TODO: Some benefit here, but needs to be explored. *)
  (*let nonexit = collapse_sequential nonexit in*)

  (* Topological sort on the remaining queries *)
  let topo_effects = Data_structures.query_topo_sort nonexit in

  (* Compute the dominator tree *)
  let domtree = Data_structures.dom_tree topo_effects in

  (* Mess *)
  let count   = ref 0 in
  let results = ref StringMap.empty in
  let imm_exit = List.fold_left (fun acc (q : query) ->
    StringSet.fold (fun pred -> StringMap.update pred (function
      | Some e -> Some (q :: e)
      | None   -> Some [q]
    )) q.preds acc
  ) StringMap.empty exits in

  (* Run the solver *)
  let r = try
    ignore (dominator_solve solver count 0 (List.hd topo_effects) domtree results imm_exit);
    Solver.Unsat
  with 
  | Sat_outcome ->  Solver.Sat
  | _ -> Solver.Unknown
  in

  (* Generate the query dot graph, if necessary *)
  if is_debug_enabled () then begin
    let dot_content = generate_query_dependency_dot queries !results in
    let dot_filename = Option.get (get_debug_file_path "query_dependencies.dot") in
    let dot_file = open_out dot_filename in
    output_string dot_file dot_content;
    close_out dot_file;
    debug_printf "  Query dependency graph written to %s\n" dot_filename
  end;

  r
