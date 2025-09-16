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
  funs: (string * sexp list) list;
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
  {state with funs = (name,def)::state.funs}

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

(** Parse a single S-expression and update parser state *)
let parse_sexp state sexp =
  match sexp with
  (* Variable declarations *)
  | List [Atom "declare-const"; Atom name; sort_sexp] ->
      process_declaration state name sort_sexp
  | List (Atom "define-fun"::Atom name::defs) ->
      process_fun state name defs
  (* Final assertions: (assert (! (not a) :named InvPrimed)) *)
  | List [Atom "assert"; List [Atom "!"; List [Atom "not"; req]; Atom ":named"; Atom name]]
      when String.starts_with ~prefix:"InvPrimed" name ->
        let query = build_predicate req in
        { state with final = query :: state.final }
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

(** Place as many floating operations as possible *)
let rec repeat_floating defs floating preds effs name =
  let (placeable, floating) = List.partition (fun op ->
    StringSet.subset (op_fvs op) defs
  ) floating in
  if placeable = [] then (defs,placeable,floating,preds,effs)
  else
    let placed_calls = List.filter_map (function Call c -> Some c | _ -> None) placeable in
    let effs = List.fold_left (fun effs c ->
      StringSet.fold (fun query_name effs ->
        StringMap.add query_name (preds,name) effs
      ) c.queries effs
    ) effs placed_calls in
    let all_queries = List.fold_left (fun acc c -> StringSet.union acc c.queries) StringSet.empty placed_calls in
    let preds = all_queries in
    let defs = List.fold_right StringSet.union (List.map op_defs placeable) defs in
    let (defs,placeable',floating,preds,effs) = repeat_floating defs floating preds effs name in
    (defs,placeable@placeable',floating,preds,effs)

(** Place the floating operations throughout the program, based on dependecies *)
let solve_definitions program floating =
  let (program, _, floating, undefined, _, effs) =
    List.fold_left (fun (program, def_at_exit_map, floating, undefined, preds_at_exit,effs) block_name ->
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
      let incoming = List.map (fun p -> StringMap.find p preds_at_exit) block.preds in
      let incoming = if block_name = get_entry program then [StringSet.singleton "entry"] else incoming in
      let preds = List.fold_left StringSet.union StringSet.empty incoming in


      let (defs,prefix,floating,preds,effs) =
        if block_name <> get_entry program then repeat_floating defs floating preds effs block_name
        else (defs,[],floating,preds,effs) in

      (* Process operations in sequence, tracking definitions and placing floating *)
      let (ops, defs, floating, undefined, preds, effs) =
        List.fold_left (fun (ops, defs, floating, undefined, preds, effs) operation ->
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
          let (defs,placeable,floating,preds,effs) = repeat_floating defs floating preds effs block_name in
          (ops@ [operation] @ placeable, defs, floating, undefined,preds,effs)
        ) ([], defs, floating, undefined, preds, effs) block.ops
      in
      let (defs,suffix,floating,preds,effs) = repeat_floating defs floating preds effs block_name in

      (* Update the block with processed operations *)
      let ops = prefix @ ops @ suffix in
      let program = update_block program block_name (fun b -> {b with ops}) in
      let updated_def_map = StringMap.add block_name defs def_at_exit_map in
      let preds_map = StringMap.add block_name preds preds_at_exit in

      (program, updated_def_map, floating, undefined,preds_map,effs)
  ) (program, StringMap.empty, floating, StringSet.empty, StringMap.empty, StringMap.empty) (topo_sort program) in

  (* Validate there are no remaining effects that couldn't be placed *)
  if floating <> [] then
    failwith ("Unplaced effects: " ^ (String.concat ", " (List.map pp_op floating)));

  let defined_anywhere = collect_defs program in
  let bad_flow = StringSet.inter defined_anywhere undefined in
  if not (StringSet.is_empty bad_flow) then
    debug_printf "WARNING: Variables used without path to definition: %s\n"
      (pp_set bad_flow);

  (* dump_program program; *)
  (program,StringSet.diff undefined defined_anywhere,effs)

let create_entry_operation (program : program) initial =
  let fvsl = List.map (fun pred -> free_vars pred.term) initial in
  let fvs = List.fold_left StringSet.union StringSet.empty fvsl in
  let fvs = StringSet.filter (fun v -> String.starts_with ~prefix:program.name v) fvs in
  let call = Call { vars = fvs; name = "entry"; args = StringSet.empty; queries = StringSet.empty } in
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
  let call = Call { args = fvs; name = "exit"; vars = StringSet.empty; queries = StringSet.empty } in
  update_block program (get_exit program) (fun block -> {block with ops = call :: block.ops})

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
  let (program,undefined,effs) = solve_definitions program free_ops in
  let program = add_entry_vars program undefined in
  (program,effs)

let order_effects effects effs =
  List.map (fun effect ->
    match StringMap.find_opt effect.qname effs with
    | Some (preds,source,target) -> { effect with preds ; source_location = Some source ; target_location = Some target }
    | None -> failwith "missing effect")  effects

let join_effs a b =
  StringMap.merge (fun k a b ->
    match a, b with
    | Some (_,n), Some (a,m) -> Some (a,n,m)
    | Some _, _
    | _, Some _ -> Printf.printf "Removing %s\n" k; None
    | _ -> None) a b

(** Parse SMT-LIB2 file and return a State object *)
let parse_file filename : state =
  let content = In_channel.with_open_text filename In_channel.input_all in
  let parsed = match load_sexp ("(" ^ content ^ ")") with
    | Error msg -> failwith ("Failed to parse S-expressions: " ^ msg)
    | Ok sexps -> sexps
  in
  let state = List.fold_left parse_sexp empty_parser_state parsed in
  let (source,effs) = process_program state.source_program state in
  let (target,effs2) = process_program state.target_program state in
  let effects = order_effects state.effect_q (join_effs effs effs2) in

  (* Apply bool2bv1 transformation to both programs and all predicates *)
  let transformed_source = transform_program_bool2bv1 source in
  let transformed_target = transform_program_bool2bv1 target in
  let transformed_initial = List.map transform_predicate_bool2bv1 state.initial in
  let transformed_final = List.map transform_predicate_bool2bv1 state.final in
  let transformed_arbitrary = List.map transform_predicate_bool2bv1 state.arbitrary in
  let transformed_effects = List.map transform_query_bool2bv1 effects in

  {
    source = transformed_source;
    target = transformed_target;
    initial = transformed_initial;
    effects = transformed_effects;
    final = transformed_final;
    arbitrary = transformed_arbitrary;
    funs = state.funs;
  }
