(** Program validation pass for checking predecessor exclusivity *)

open Data_structures
open Utilities
open Smtlib_output
open Incremental_solver

(** Generate pairwise conjunction check for predecessor exclusivity *)
let generate_pairwise_check preds =
  let rec generate_pairs = function
    | [] -> []
    | x :: xs ->
        List.map (fun y -> Printf.sprintf "(and %s %s)" x y) xs @ generate_pairs xs
  in
  match generate_pairs preds with
  | [] -> None
  | pairs -> Some (Printf.sprintf "(or %s)" (String.concat " " pairs))

(** Validate that all blocks have mutually exclusive predecessors for a single program *)
let validate_program_exclusivity program timeout_ms =
  debug_printf "Starting predecessor exclusivity validation for %s\n" program.name;

  (* Build base assertions for this program only *)
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer (generate_block_assertions program program.name);
  Buffer.add_string buffer (generate_assignment_assertions program);

  let base_query = Buffer.contents buffer in

  (* Create a minimal state with just this program *)
  let minimal_state = {
    source = program;
    target = empty_program "dummy";
    effects = [];
    arbitrary = [];
    funs = [];
  } in

  (* Start incremental solver *)
  let solver = begin_solver minimal_state timeout_ms base_query in

  (* Check each block's predecessors *)
  StringMap.iter (fun block_name block ->
    match block.preds with
    | [] | [_] -> () (* 0 or 1 predecessor is always valid *)
    | preds when List.length preds >= 2 ->
        (match generate_pairwise_check preds with
        | None -> ()
        | Some pairwise_expr ->
            let assertion = Printf.sprintf "(assert %s)\n" pairwise_expr in
            (* Check if any two predecessors can be true simultaneously *)
            let result = scoped_solve ~cmt:("Check " ^ block_name) solver assertion in
            (match result with
            | SOLVED ->
                debug_printf "WARNING: Block %s has non-exclusive predecessors: %s\n" block_name (String.concat ", " preds)
            | UNSOLVED _ ->
                debug_printf "  Block %s: predecessors are mutually exclusive\n" block_name))
    | _ -> ()
  ) program.blocks;

  close_solver solver;
  debug_printf "Finished predecessor exclusivity validation for %s\n" program.name
