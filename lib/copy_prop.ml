(** Copy and constant propagation optimization for SMT programs *)

open Data_structures
open Utilities
open Sexplib0.Sexp

(** Substitute variables in an S-expression based on copy/constant map *)
let rec substitute_sexp copy_map expr =
  match expr with
  | Atom var when is_var var ->
      (match StringMap.find_opt var copy_map with
      | Some canonical -> canonical
      | None -> expr)
  | Atom _ -> expr
  | List exprs ->
      List (List.map (substitute_sexp copy_map) exprs)

(** Check if an expression is a copy (variable) or constant (no free variables) *)
let is_copy_or_constant expr =
  match expr with
  | Atom var when is_var var -> Some expr  (* It's a copy *)
  | _ ->
      let fvs = free_vars expr in
      if StringSet.is_empty fvs then Some expr  (* It's a constant *)
      else None

(** Apply copy/constant propagation to a single operation *)
let substitute_operation copy_map = function
  | Assignment { var; expr } ->
      Assignment { var; expr = substitute_sexp copy_map expr }
  | Call call_op ->
      let new_args = StringSet.fold (fun arg acc ->
        match StringMap.find_opt arg copy_map with
        | Some (Atom canonical) when is_var canonical ->
            StringSet.add canonical acc
        | Some _ ->
            (* Argument was replaced by a constant, prune it *)
            acc
        | None ->
            StringSet.add arg acc
      ) call_op.args StringSet.empty in
      Call { call_op with args = new_args }
  | Assume expr ->
      Assume (substitute_sexp copy_map expr)

(** Process operations in a block, accumulating copy/constant mappings *)
let process_operations copy_map ops =
  List.fold_left (fun (copy_map, new_ops) op ->
    let subst_op = substitute_operation copy_map op in
    match subst_op with
    | Assignment { var; expr } ->
        (match is_copy_or_constant expr with
        | Some source ->
            let new_copy_map = StringMap.add var source copy_map in
            (new_copy_map, new_ops)
        | None ->
            (copy_map, new_ops @ [subst_op]))
    | _ ->
        (copy_map, new_ops @ [subst_op])
  ) (copy_map, []) ops

(** Process phi nodes in a block, accumulating copy/constant mappings *)
let process_phis copy_map phis =
  StringMap.fold (fun var phi_list (copy_map, new_phis) ->
    let phi_list = List.map (fun (block, expr) ->
      (block, substitute_sexp copy_map expr)
    ) phi_list in

    (* Check if all phi sources are the same expression after substitution *)
    let sources = List.filter_map (fun (_, expr) -> is_copy_or_constant expr) phi_list in
    let all_same = match sources with
      | first :: rest when List.length sources = List.length phi_list ->
          List.for_all (fun s -> s = first) rest
      | _ -> false
    in

    if all_same then
      let source = List.hd sources in
      let new_copy_map = StringMap.add var source copy_map in
      (new_copy_map, new_phis)
    else
      (copy_map, StringMap.add var phi_list new_phis)
  ) phis (copy_map, StringMap.empty)

(** Process a block to extract copy assignments and apply substitutions *)
let process_block copy_map block =
  let (copy_map_after_phis, updated_phis) = process_phis copy_map block.phis in
  let (copy_map_after_ops, updated_ops) = process_operations copy_map_after_phis block.ops in
  let updated_block = { block with phis = updated_phis; ops = updated_ops } in
  (updated_block, copy_map_after_ops)

(** Apply copy propagation to an entire program *)
let copy_propagate program =
  let sorted_blocks = topo_sort program in

  let (updated_blocks, copy_map) = List.fold_left
    (fun (blocks_map, copy_map) block_name ->
      let block = StringMap.find block_name program.blocks in
      let (updated_block, new_copy_map) = process_block copy_map block in
      (StringMap.add block_name updated_block blocks_map, new_copy_map)
    ) (StringMap.empty, StringMap.empty) sorted_blocks
  in

  (* Remove replaced variables from the variable list *)
  let updated_variables = StringMap.filter (fun var_name _ ->
    not (StringMap.mem var_name copy_map)
  ) program.variables in

  let updated_program = { program with blocks = updated_blocks; variables = updated_variables } in
  (updated_program, copy_map, StringMap.cardinal copy_map)

(** Apply substitutions to a predicate *)
let substitute_predicate copy_map pred =
  { pred with term = substitute_sexp copy_map pred.term }

(** Apply substitutions to a query *)
let substitute_query source_map target_map query =
  let combined_map = StringMap.union (fun _ a _ -> Some a) source_map target_map in
  {
    query with
    req = List.map (substitute_predicate combined_map) query.req;
    ens = List.map (substitute_predicate combined_map) query.ens;
  }

(** Transform both programs in a state *)
let transform_state state =
  let (source_result, source_time) = get_time (fun () ->
    copy_propagate state.source
  ) in
  let (source_program, source_map, source_removed) = source_result in

  let (target_result, target_time) = get_time (fun () ->
    copy_propagate state.target
  ) in
  let (target_program, target_map, target_removed) = target_result in

  let total_removed = source_removed + target_removed in
  let total_time = source_time +. target_time in

  debug_printf "Copy/constant propagation: removed %d variables in %.2fms\n" total_removed total_time;

  let updated_effects = List.map (substitute_query source_map target_map) state.effects in
  let combined_map = StringMap.union (fun _ a _ -> Some a) source_map target_map in
  let updated_arbitrary = List.map (substitute_predicate combined_map) state.arbitrary in

  { state with
    source = source_program;
    target = target_program;
    effects = updated_effects;
    arbitrary = updated_arbitrary;
  }
