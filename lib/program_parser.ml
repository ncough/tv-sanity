(** Program parser for SMT-LIB2 files *)

open Data_structures
open Utilities
open Sexplib0.Sexp

(**************************************************************************************************
 * Parsing State
 *************************************************************************************************)

(** Parser state for building programs incrementally *)
type parser_state = {
  source_program : program;
  target_program : program;
  initial: predicate list;
  final: predicate list;
  effect_q: query list;
  last_block : string option;
  arbitrary : predicate list;
  funs: ([`Def | `Decl] * string * sexp list) list;
}

(** Create initial parser state *)
let empty_parser_state = {
  source_program = empty_program "source";
  target_program = empty_program "target";
  initial = [];
  final = [];
  effect_q = [];
  last_block = None;
  arbitrary = [];
  funs = [];
}

(**************************************************************************************************
 * Parsing Utilities
 *************************************************************************************************)

let rec collapse_op op = function
  | List (Atom op' :: args) when op = op' -> List.flatten (List.map (collapse_op op) args)
  | expr -> [expr]

let parse_conj = collapse_op "and"
let parse_disj = collapse_op "or"

let get_atom = function Atom s -> Some s | _ -> None

let all_some l = if List.mem None l then None else Some (List.map Option.get l)

let contains_block expr = StringSet.exists is_block (free_vars expr)

(** Transform bool2bv1 expressions to ite expressions *)
let rec transform_bool2bv1 = function
  | List [Atom "bool2bv1"; arg] ->
      (* Replace (bool2bv1 arg) with (ite arg (_ bv1 1) (_ bv0 1)) *)
      List [Atom "ite"; transform_bool2bv1 arg; Atom "(_ bv1 1)"; Atom "(_ bv0 1)"]
  | List exprs ->
      (* Recursively transform all expressions in the list *)
      List (List.map transform_bool2bv1 exprs)
  | Atom s -> Atom s

(** Apply bool2bv1 transformation to a predicate *)
let transform_predicate_bool2bv1 pred =
  { pred with term = transform_bool2bv1 pred.term }

(** Apply bool2bv1 transformation to an operation *)
let transform_operation_bool2bv1 = function
  | Assignment { var; expr } ->
      Assignment { var; expr = transform_bool2bv1 expr }
  | Assume expr ->
      Assume (transform_bool2bv1 expr)
  | Call call_op -> Call call_op  (* Call operations don't have expressions to transform *)

(** Apply bool2bv1 transformation to a block *)
let transform_block_bool2bv1 block =
  let transform_phi_entry (pred_block, expr) = (pred_block, transform_bool2bv1 expr) in
  let transform_phi_map phi_map =
    StringMap.map (List.map transform_phi_entry) phi_map
  in
  {
    block with
    phis = transform_phi_map block.phis;
    ops = List.map transform_operation_bool2bv1 block.ops;
  }

(** Apply bool2bv1 transformation to a program *)
let transform_program_bool2bv1 program =
  {
    program with
    blocks = StringMap.map transform_block_bool2bv1 program.blocks;
  }

(** Apply bool2bv1 transformation to a query *)
let transform_query_bool2bv1 query =
  {
    query with
    req = List.map transform_predicate_bool2bv1 query.req;
    ens = List.map transform_predicate_bool2bv1 query.ens;
  }

let build_predicate term = { term ; sat = None }

let build_query qname req ens = {
  qname;
  req = List.map build_predicate req;
  ens = List.map build_predicate ens;
  preds = StringSet.empty;
  source_location = None;
  target_location = None;
}

(** Utility to update a program based on a entity name prefix *)
let update_program state name fn =
  if is_source name then
    { state with source_program = fn state.source_program }
  else if is_target name then
    { state with target_program = fn state.target_program }
  else
    failwith ("Unknown program entity: " ^ name)

(** Utility to update the most recently defined block *)
let update_last_block state fn =
  let name = match state.last_block with None -> failwith "No last block!" | Some v -> v in
  update_program state name (fun prog ->
    let block = StringMap.find name prog.blocks in
    let blocks = StringMap.add name (fn block) prog.blocks in
    {prog with blocks})

(**************************************************************************************************
 * Parsing Operations
 *************************************************************************************************)

let process_declaration state name sort =
  update_program state name (fun prog -> add_variable prog name sort None)

let process_fun state name def =
  {state with funs = (`Def,name,def)::state.funs}

let process_fun_decl state name def =
  {state with funs = (`Decl,name,def)::state.funs}

let process_entry_block state var =
  let state = update_program state var (fun prog -> add_entry prog var) in
  {state with last_block = Some var}

let process_exit_block state var  =
  update_program state var (fun prog -> set_exit prog var)

(** Parse predecessor expressions from SMT-LIB2 assertions.
    Expects an 'and' operations over standard expressions and some disjunction of
    predecessor blocks.
 *)
let parse_predecessors expr =
  let conjs = parse_conj expr in
  let (blocks, exprs) = List.partition contains_block conjs in
  let expr = match exprs with [] -> Atom "true" | l -> List (Atom "and" :: l) in
  match blocks with
  | [] -> Some (expr, [])
  | [x] ->
      let blocks = parse_disj x in
      (match all_some (List.map get_atom blocks) with
      | Some blocks -> Some (expr, blocks)
      | _ -> None)
  | _ -> None

(** Process regular block definitions with predecessor conditions as assumes *)
let process_block state var predecessors condition =
  let state = update_program state var (fun prog ->
    let ops = match condition with Atom "true" -> [] | _ -> [Assume condition] in
    add_block prog var predecessors ops) in
  {state with last_block = Some var}

(** Parse assignment expressions from SMT-LIB2 assertions.
    Expects an 'and' operation over a series of equalities, where the LHS is
    a variable and the RHS an arbitrary expression.
 *)
let parse_assignments expr =
  let conjs = parse_conj expr in
  all_some (List.map (function
    | List [Atom "="; Atom var; expr] when is_var var -> Some (var,expr)
    | _ -> None) conjs)

(** Process variable assignments within blocks *)
let process_assignment state assigns =
  let ops = List.map (fun (var,expr) -> Assignment { var; expr } ) assigns in
  update_last_block state (fun b -> { b with ops = ops @ b.ops })

(** Parse phi expressions from SMT-LIB2 assertions.
    Expects an 'and' operation over a series of conditional equalities,
    where the condition is a disjunction over block variables, the LHS of the
    equality is some expression and the RHS is a common variable.
 *)
let parse_phis expr =
  let conjs = parse_conj expr in
  let phis = all_some (List.map (function
    | List [Atom "=>"; blocks; List [Atom "="; expr; Atom var]] when is_var var ->
        let blocks_atom = parse_disj blocks in
        (match all_some (List.map get_atom blocks_atom) with
        | Some blocks -> Some (var, blocks, expr)
        | _ -> None)
    | _ -> None) conjs) in
  match phis with
  | Some ((v,blocks,expr)::ls) when List.for_all (fun (w,_,_) -> v = w) ls ->
      Some(v,(blocks,expr)::(List.map (fun (_,b,e) -> (b,e)) ls))
  | _ -> None

let rec parse_ite = function
  | List [Atom "ite"; blocks; Atom var; rest] when is_var var ->
      (match all_some (List.map get_atom (parse_disj blocks)), parse_ite rest with
      | Some blocks, Some (var_map, def) ->
          (* Add blocks to the mapping for this variable *)
          let updated_map = StringMap.update var (function
            | None -> Some blocks
            | Some existing_blocks -> Some (existing_blocks @ blocks)
          ) var_map in
          Some (updated_map, def)
      | _ -> None)
  | Atom var when is_var var ->
      Some (StringMap.empty, var)
  | _ -> None

let process_ite state var (phis,def) =
  update_last_block state (fun block ->
    let included_blocks = StringMap.fold (fun _ blocks acc -> StringSet.union acc (StringSet.of_list blocks)) phis StringSet.empty in
    let missing_preds = StringSet.diff (StringSet.of_list block.preds) included_blocks in
    let def_blocks = StringSet.elements missing_preds in
    let phis = StringMap.bindings (StringMap.add def def_blocks phis) in
    let flat = List.flatten (List.map (fun (a,blocks) -> List.map (fun b -> (b,Atom a)) blocks) phis) in
    let updated_phis = StringMap.update var (function
      | None -> Some flat
      | Some _ -> failwith "huh"
    ) block.phis in
    { block with phis = updated_phis })

(** Process phi node definitions *)
let process_phis state var phis =
  update_last_block state (fun block ->
    let exp = List.map (fun (blocks,expr) -> List.map (fun b -> (b,expr)) blocks) phis in
    let flat_phis = List.flatten exp in
    let updated_phis = StringMap.update var (function
      | None -> Some flat_phis
      | Some existing -> Some (existing @ flat_phis)
    ) block.phis in
    { block with phis = updated_phis })

(** Process assertion statements *)
let parse_assertion state assertion name =
  match assertion with
  | List [Atom "="; Atom var; Atom "true"] when is_block var ->
      process_entry_block state var
  (* Regular blocks: (= block_var dependency_expr) *)
  | List [Atom "="; Atom var; pred_expr] when is_block var ->
      (match parse_predecessors pred_expr with
      | Some (c,p) ->
          let st = process_block state var p c in
          if is_exit_block var then process_exit_block st var else st
      | None ->
          failwith ("Invalid predecessor expression " ^ var ^ ": " ^ pp_sexp pred_expr))
  (* Phi nodes: (= var (ite block_var ...) *)
  | List [Atom "="; Atom var; List (Atom "ite" :: _) as expr] when is_var var && Option.is_some (parse_ite expr) ->
      (match parse_ite expr with
      | Some phis -> process_ite state var phis
      | None -> unreachable ())
  (* Variable declarations within blocks *)
  | expr when Option.is_some (parse_assignments expr) ->
      (match parse_assignments expr with
       | Some assigns -> process_assignment state assigns
       | None -> state)
  (* Phi nodes: (and ...) with phi patterns *)
  | expr when Option.is_some (parse_phis expr) ->
      (match parse_phis expr with
       | Some (var, phis) -> process_phis state var phis
       | None -> unreachable ())
  (* Unknown assertion *)
  | Atom s as e when String.ends_with ~suffix:"_SYNTH_EXIT_done" s ->
      { state with arbitrary = build_predicate e :: state.arbitrary }
  | e ->
      debug_printf "WARNING: Arbitary Named Assert: %s %s\n" name (pp_sexp e);
      { state with arbitrary = build_predicate e :: state.arbitrary }

let rec leading_implies = function
  | List [Atom "=>"; cond; goal] ->
      let (conds,goal) = leading_implies goal in
      (cond::conds,goal)
  | List [Atom "or"; cond; goal] ->
      let (conds,goal) = leading_implies goal in
      ((List [Atom "not";cond])::conds,goal)
  | g -> ([],g)

let rec collase_conj = function
  | List (Atom "and"::conds) ->
      List.flatten (List.map collase_conj conds)
  | g -> [g]

let process_goal state goal =
  assert (state.final = []);
  let (conds,goal) = leading_implies goal in
  let goals = collase_conj goal in
  let state = List.fold_left (fun state cond ->
    debug_printf "WARNING: Elevating Goal Condition to Assert: %s\n" (pp_sexp cond);
    { state with arbitrary = build_predicate cond :: state.arbitrary }) state conds in
  let final = List.map build_predicate goals in
  { state with final }

(** Parse a single S-expression and update parser state *)
let parse_sexp state sexp =
  match sexp with
  (* Variable declarations *)
  | List [Atom "declare-const"; Atom name; sort_sexp] ->
      process_declaration state name sort_sexp
  | List (Atom "declare-fun"::Atom name::defs) ->
      process_fun_decl state name defs
  | List (Atom "define-fun"::Atom name::defs) ->
      process_fun state name defs
  (* Final assertions: (assert (! (not a) :named InvPrimed)) *)
  | List [Atom "assert"; List [Atom "!"; List [Atom "not"; req]; Atom ":named"; Atom name]]
      when String.starts_with ~prefix:"InvPrimed" name ->
        process_goal state req
  (* Query requirements and ensures: (assert (! (=> req ens) :named ackermann...)) *)
  | List [Atom "assert"; List [Atom "!"; List [Atom "=>"; req; ens]; Atom ":named"; Atom name]]
      when String.starts_with ~prefix:"ackermann" name ->
        let query = build_query name [req] [ens] in
        { state with effect_q = query :: state.effect_q }
  (* Initial constraint assertions: (assert (! a :named invN)) *)
  | List [Atom "assert"; List [Atom "!"; ens; Atom ":named"; Atom name]]
      when String.starts_with ~prefix:"inv" name ->
        let query = build_predicate ens in
        { state with initial = query :: state.initial }
  (* General assertions: (assert (! a :named name)) *)
  | List [Atom "assert"; List [Atom "!"; assertion; Atom ":named"; Atom name]] ->
      parse_assertion state assertion name
  | List [Atom "assert"; e] ->
      debug_printf "WARNING: Arbitary Unamed Assert: %s\n" (pp_sexp e);
      { state with arbitrary = build_predicate e :: state.arbitrary }
  (* Ignore standard SMT-LIB2 commands *)
  | List [Atom "check-sat"] | List [Atom "get-model"] -> state
  | List [Atom "set-logic"; _] -> state  (* Ignore logic declarations *)
  | List (Atom "check-sat-using" :: _) -> state  (* Ignore check-sat-using with tactics *)
  (* Unknown command - fail with informative error *)
  | _ -> failwith ("Unknown SMT command: " ^ pp_sexp sexp)

(** Collect all definitions *)
let collect_defs program =
  List.fold_left (fun seen block_name ->
    let block = StringMap.find block_name program.blocks in
    let defs = StringMap.to_seq block.phis |> Seq.map fst |> StringSet.of_seq in
    let defs = List.fold_left StringSet.union defs (List.map op_defs block.ops) in
    let overlap = StringSet.inter defs seen in
    if not (StringSet.is_empty overlap) then
      debug_printf "WARNING: Variable(s) %s redefined in block %s\n"
        (pp_set overlap) block_name;
    StringSet.union seen defs
  ) StringSet.empty (topo_sort program)

(** Helper to validate phi node *)
let validate_phi block_predecessors def_at_exit_map var phi_list =
  let phi_blocks = List.map fst phi_list |> StringSet.of_list in
  let pred_blocks = StringSet.of_list block_predecessors in
  if not (StringSet.equal phi_blocks pred_blocks) then
    debug_printf "WARNING: Phi %s edges don't match flow edges: %s <> %s\n"
      var
      (String.concat "," (StringSet.elements pred_blocks))
      (String.concat "," (StringSet.elements phi_blocks));
  let undef = List.map (fun (pred_block, expr) ->
    let used_vars = free_vars expr in
    let pred_defs = StringMap.find pred_block def_at_exit_map in
    let undefined = StringSet.diff used_vars pred_defs in
    (*if not (StringSet.is_empty undefined) then
      Printf.printf "WARNING: Phi %s uses undefined vars %s from %s\n"
        var (String.concat "," (StringSet.elements undefined)) pred_block;*)
    undefined
  ) phi_list in
  union_all undef


let is_trace s =
  (String.starts_with ~prefix:"target__TRACE" s ||
  String.starts_with ~prefix:"source__TRACE" s) &&
  not (String.starts_with ~prefix:"target__TRACE_MEM" s ||
  String.starts_with ~prefix:"source__TRACE_MEM" s)

let get_trace s =
  match StringSet.fold (fun name acc -> if is_trace name then name::acc else acc) s [] with
  | [a] -> a
  | _ -> failwith "no trace"

let get_traces = StringSet.filter (is_trace)

let find_trace name defs =
  match StringMap.find_opt name defs with
  | Some v -> v
  | None -> failwith (Printf.sprintf "No entry for %s\n" name)

(** Place as many floating operations as possible *)
let rec repeat_floating defs floating trace_defs effs name =
  let (placeable, floating) = List.partition (fun op ->
    StringSet.subset (op_fvs op) defs
  ) floating in
  if placeable = [] then (defs,placeable,floating,trace_defs,effs)
  else
    let placed_calls = List.filter_map (function Call c -> Some c | _ -> None) placeable in

    (* Link the placed queries to the effects that define its trace *)
    let effs = List.fold_left (fun effs c ->
      let trace_arg = get_trace c.args in
      let preds = find_trace trace_arg trace_defs in
      StringSet.fold (fun query_name effs ->
        StringMap.add query_name (preds,name) effs
      ) c.queries effs
    ) effs placed_calls in

    (* Update trace_def for the placed queries *)
    let trace_defs = List.fold_left (fun trace_defs c ->
      let trace_res = get_trace c.vars in
      let existing = StringMap.find_opt trace_res trace_defs in
      let updated = match existing with Some(s) -> StringSet.union s c.queries | None -> c.queries in
      StringMap.add trace_res updated trace_defs
    ) trace_defs placed_calls in

    let defs = List.fold_right StringSet.union (List.map op_defs placeable) defs in
    let (defs,placeable',floating,trace_defs,effs) = repeat_floating defs floating trace_defs effs name in
    (defs,placeable@placeable',floating,trace_defs,effs)

(** Place the floating operations throughout the program, based on dependecies *)
let solve_definitions program floating =
  let trace_entry = program.name ^ "__TRACE" in
  let trace_defs = StringMap.add trace_entry (StringSet.add "entry" StringSet.empty) StringMap.empty in

  let (program, _, floating, undefined, trace_defs, effs) =
    List.fold_left (fun (program, def_at_exit_map, floating, undefined,trace_defs,effs) block_name ->
      let block = StringMap.find block_name program.blocks in
      let undefined = StringMap.fold (fun k v acc ->
        let undef = validate_phi block.preds def_at_exit_map k v in
        StringSet.union acc undef) block.phis undefined in

      (* Calculate initial definitions for this block *)
      let incoming = List.map (fun p -> StringMap.find p def_at_exit_map) block.preds in
      let def_at_entry = inter_all incoming in
      let phi_defs = StringMap.to_seq block.phis |> Seq.map fst |> StringSet.of_seq in
      let defs = StringSet.union phi_defs def_at_entry in

      (* Calculate incoming exit order *)
      let trace_defs = StringMap.fold (fun var exps acc ->
        if is_trace var then begin
          let inputs = List.map (function
            | (_,Atom v) -> find_trace v trace_defs
            | _ -> failwith "huh") exps in
          let join = List.fold_left StringSet.union StringSet.empty inputs in
          StringMap.add var join acc
        end else acc) block.phis trace_defs in

      let (defs,prefix,floating,trace_defs,effs) =
        if block_name <> get_entry program then repeat_floating defs floating trace_defs effs block_name
        else (defs,[],floating,trace_defs,effs) in

      (* Process operations in sequence, tracking definitions and placing floating *)
      let (ops, defs, floating, undefined, trace_defs, effs) =
        List.fold_left (fun (ops, defs, floating, undefined, trace_defs, effs) operation ->
          (* Check that all uses in this operation are defined *)
          let used_vars = op_fvs operation in
          let new_undefined = StringSet.diff used_vars defs in
          if not (StringSet.is_empty new_undefined) then
            debug_printf "WARNING: Undefined variables %s in operation %s\n"
              (pp_set new_undefined)
              (pp_op operation);
          let defs = StringSet.union (op_defs operation) defs in
          let undefined = StringSet.union new_undefined undefined in

          (* Place operations whose dependencies are now satisfied *)
          let (defs,placeable,floating,trace_defs,effs) = repeat_floating defs floating trace_defs effs block_name in
          (ops@ [operation] @ placeable, defs, floating, undefined,trace_defs,effs)
        ) ([], defs, floating, undefined, trace_defs, effs) block.ops
      in
      let (defs,suffix,floating,trace_defs,effs) = repeat_floating defs floating trace_defs effs block_name in

      (* Update the block with processed operations *)
      let ops = prefix @ ops @ suffix in
      let program = update_block program block_name (fun b -> {b with ops}) in
      let updated_def_map = StringMap.add block_name defs def_at_exit_map in

      (program, updated_def_map, floating, undefined,trace_defs,effs)
  ) (program, StringMap.empty, floating, StringSet.empty, trace_defs, StringMap.empty) (topo_sort program) in

  (* Store exit predecessors in effs map when processing exit block *)
  let exit_preds =
    let block = get_block program (get_exit program) in

    let default_trace = match block.ops with
    | (Call c)::_ when c.name = "exit" ->
        let traces = get_traces c.args in
        (match StringSet.to_list traces with [v] -> v | _ -> failwith "no clear trace var")
    | _ -> failwith "bad exit block" in

    List.fold_left (fun acc pred ->
      (* phi effects *)
      let subst = StringMap.map (fun uses ->
        let reduced = List.filter (fun (b,_) -> b = pred) uses in
        match reduced with
        | [(_,sexp)] -> sexp
        | _ -> failwith "Phi with multiple values for the same block") block.phis in

      (* find the trace variable *)
      let traces = StringMap.filter (fun k _ -> is_trace k) subst in
      let trace = match StringMap.bindings traces with [(_,Atom v)] -> v | _ -> default_trace
      in
      let preds = find_trace trace trace_defs in
      StringMap.add pred (preds,subst) acc
    ) StringMap.empty block.preds
  in

  (* Validate there are no remaining effects that couldn't be placed *)
  if floating <> [] then
    failwith ("Unplaced effects: " ^ (String.concat ", " (List.map pp_op floating)));

  let defined_anywhere = collect_defs program in
  let bad_flow = StringSet.inter defined_anywhere undefined in
  if not (StringSet.is_empty bad_flow) then
    debug_printf "WARNING: Variables used without path to definition: %s\n"
      (pp_set bad_flow);

  (* dump_program program; *)
  (program,StringSet.diff undefined defined_anywhere,effs,exit_preds)

let create_entry_operation (program : program) initial =
  let fvsl = List.map (fun pred -> free_vars pred.term) initial in
  let fvs = List.fold_left StringSet.union StringSet.empty fvsl in
  let fvs = StringSet.filter (fun v -> String.starts_with ~prefix:program.name v) fvs in
  let call = Call { vars = fvs; name = "entry"; args = StringSet.empty; queries = StringSet.singleton "entry" } in
  update_block program (get_entry program) (fun block -> {block with ops = call :: block.ops})

let add_entry_vars program new_vars =
  update_block program (get_entry program) (fun block ->
    match block.ops with
    | Call { vars; name ; args; queries} :: ops when name = "entry" ->
        { block with ops = Call { name ; args ; vars = StringSet.union vars new_vars ; queries }::ops }
    | _ -> failwith "Missing entry")

let create_exit_operation (program : program) final =
  let fvsl = List.map (fun pred -> free_vars pred.term) final in
  let fvs = List.fold_left StringSet.union StringSet.empty fvsl in
  let fvs = StringSet.filter (fun v -> String.starts_with ~prefix:program.name v) fvs in
  let call = Call { args = fvs; name = "exit"; vars = StringSet.empty; queries = StringSet.singleton "exit"} in
  update_block program (get_exit program) (fun block -> {block with ops = call :: block.ops})

(** Create entry effect from initial conditions *)
let create_entry_effect source_program target_program initial =
  let source_entry = get_entry source_program in
  let target_entry = get_entry target_program in
  {
    qname = "entry";
    req = [];
    ens = initial;
    preds = StringSet.empty;
    source_location = Some source_entry;
    target_location = Some target_entry;
  }

(** Create exit effect from final conditions *)
let create_exit_effect source_program target_program final =
  let source_exit = get_exit source_program in
  let target_exit = get_exit target_program in
  let false_predicate = { term = Atom "false"; sat = None } in
  {
    qname = "exit";
    req = final;
    ens = [false_predicate];
    preds = StringSet.empty;
    source_location = Some source_exit;
    target_location = Some target_exit;
  }

let deduplicate_calls =
  let join_call (a : call_op) (b : call_op) =
    { a with vars = StringSet.union a.vars b.vars ; args = StringSet.union a.args b.args ; queries = StringSet.union a.queries b.queries } in
  let join_calls = List.fold_left join_call in
  List.fold_left (fun acc call ->
    let (acc,dup) = List.partition (fun other -> StringSet.disjoint other.vars call.vars) acc in
    (join_calls call dup)::acc) []

let create_floating_operations program effects =
  let calls = List.map (fun query ->
    let filter_fn = fun v -> is_source v = is_source (get_entry program) in
    let req_vars = List.fold_left (fun acc pred ->
      StringSet.union acc (free_vars pred.term)
    ) StringSet.empty query.req in
    let ens_vars = List.fold_left (fun acc pred ->
      StringSet.union acc (free_vars pred.term)
    ) StringSet.empty query.ens in
    let filtered_req = StringSet.filter filter_fn req_vars in
    let filtered_ens = StringSet.filter filter_fn ens_vars in
    {
      vars = filtered_ens;
      name = query.qname;
      args = filtered_req;
      queries = StringSet.singleton query.qname;
    }
  ) effects in
  let calls = deduplicate_calls calls in
  List.map (fun s -> Call s) calls

(* Clean up a program post parsing *)
let process_program program state =
  let program = create_entry_operation program state.initial in
  let program = create_exit_operation program state.final in
  let free_ops = create_floating_operations program state.effect_q in
  let (program,undefined,effs,exits) = solve_definitions program free_ops in
  let program = add_entry_vars program undefined in
  (program,effs,exits)

let order_effects parser_state effs =
  let entry = create_entry_effect parser_state.source_program parser_state.target_program parser_state.initial in
  (*let exit = create_exit_effect parser_state.source_program parser_state.target_program parser_state.final in*)
  let effects = List.map (fun ef ->
    match StringMap.find_opt ef.qname effs with
    | Some (preds,source,target) -> { ef with preds ; source_location = Some source ; target_location = Some target }
    | None ->
        Printf.printf "missing effect %s\n" ef.qname;
        failwith "missing effect "
  ) (parser_state.effect_q) in
  entry::effects

let join_effs a b =
  StringMap.merge (fun k a b ->
    match a, b with
    | Some (a,n), Some (b,m) -> Some (StringSet.inter a b,n,m)
    | Some _, _
    | _, Some _ -> Printf.printf "Removing %s\n" k; None
    | _ -> None) a b

let rec apply_subst (m: t StringMap.t) (s: sexp) =
  match s with
  | Atom v -> (match StringMap.find_opt v m with Some s -> s | _ -> s)
  | List a -> List (List.map (apply_subst m) a)

let apply_subst_pred (m: t StringMap.t) (s: predicate list) =
  List.map (fun p -> {p with term = apply_subst m p.term}) s

(** Parse SMT-LIB2 file and return a State object *)
let parse_file filename : state =
  let content = In_channel.with_open_text filename In_channel.input_all in
  let parsed = match load_sexp ("(" ^ content ^ ")") with
    | Error msg -> failwith ("Failed to parse S-expressions: " ^ msg)
    | Ok sexps -> sexps
  in
  let state = List.fold_left parse_sexp empty_parser_state parsed in
  let (source,effs,exits) = process_program state.source_program state in
  let (target,effs2,exits2) = process_program state.target_program state in
  let effects = order_effects state (join_effs effs effs2) in

  (* mess around with exit effect here *)
  let exit_effects = StringMap.fold (fun src_block (src_preds,src_subst) ->
    StringMap.fold (fun tgt_block (tgt_preds,tgt_subst) acc ->
      let preds = StringSet.inter src_preds tgt_preds in
      if StringSet.cardinal preds = 0 then acc
      else
      let qname = "exit_" ^ src_block ^ "_" ^ tgt_block in
      let req = apply_subst_pred src_subst (apply_subst_pred tgt_subst state.final) in
      {
        qname;
        req;
        ens = [];
        preds;
        source_location = Some src_block;
        target_location = Some tgt_block
    }::acc) exits2) exits [] in

  (* Apply bool2bv1 transformation to both programs and all effects *)
  let transformed_source = transform_program_bool2bv1 source in
  let transformed_target = transform_program_bool2bv1 target in
  let transformed_arbitrary = List.map transform_predicate_bool2bv1 state.arbitrary in
  let transformed_effects = List.map transform_query_bool2bv1 (exit_effects@effects) in

  {
    source = transformed_source;
    target = transformed_target;
    effects = transformed_effects;
    arbitrary = transformed_arbitrary;
    funs = state.funs;
  }
