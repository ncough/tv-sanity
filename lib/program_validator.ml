(** Program validation pass for checking predecessor exclusivity *)

open Data_structures
open Utilities
open Smtlib_output
open Incremental_solver

(** Build an 'or' sexp over all pairwise 'and' combinations of preds. *)
let generate_pairwise_check preds =
  let rec pairs = function
    | []     -> []
    | x :: xs ->
        List.map (fun y ->
          Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "and";
                              Sexplib0.Sexp.Atom x;
                              Sexplib0.Sexp.Atom y]
        ) xs @ pairs xs
  in
  match pairs preds with
  | []    -> None
  | [one] -> Some one
  | many  -> Some (Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: many))

let validate_program_exclusivity (program : program) timeout_ms =
  debug_printf "Starting predecessor exclusivity validation for %s\n" program.name;

  let minimal_state = {
    source = program;
    target = empty_program "dummy";
    effects = [];
    arbitrary = [];
    funs = [];
  } in

  let solver = begin_solver minimal_state timeout_ms in
  emit_block_assertions solver program program.name;
  emit_assignment_assertions solver program;

  StringMap.iter (fun block_name block ->
    match block.preds with
    | [] | [_] -> ()
    | preds when List.length preds >= 2 ->
        (match generate_pairwise_check preds with
        | None -> ()
        | Some pairwise_sexp ->
            let result = scoped_solve ~cmt:("Check " ^ block_name) solver
              (fun s -> s.assert_ pairwise_sexp) in
            (match result with
            | SOLVED ->
                debug_printf "WARNING: Block %s has non-exclusive predecessors: %s\n"
                  block_name (String.concat ", " preds)
            | UNSOLVED _ ->
                debug_printf "  Block %s: predecessors are mutually exclusive\n"
                  block_name))
    | _ -> ()
  ) program.blocks;

  solver.close ();
  debug_printf "Finished predecessor exclusivity validation for %s\n" program.name
