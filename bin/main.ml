(** Main entry point for tv-sanity *)

open Tv_sanity.Program_parser
open Tv_sanity.Solver_pipeline
open Tv_sanity.Utilities
open Tv_sanity.Program_validator

(** Parse and process a single SMT-LIB2 file with main pipeline *)
let process_file filename timeout_ms disable_z3_simplify validate_preds =
  try
    let state = parse_file filename in
    let base_filename = Filename.remove_extension filename in

    (* Create debug directory if in debug mode *)
    (if is_debug_enabled () then ignore (create_debug_directory (Filename.basename base_filename)));

    (* Validate predecessor exclusivity *)
    if validate_preds then begin
      validate_program_exclusivity state.source timeout_ms;
      validate_program_exclusivity state.target timeout_ms
    end;

    (* Apply copy/constant propagation *)
    let state = Tv_sanity.Copy_prop.transform_state state in

    let _ = solve state timeout_ms ~enable_z3_simplify:(not disable_z3_simplify) in
    true
  with
  | exn ->
    let error_msg = Printexc.to_string exn in
    Printf.printf "FAIL: %s - %s\n" (Filename.basename filename) error_msg;
    false

(** Main entry point *)
let () =
  (* Command line argument variables *)
  let timeout_ms = ref 30000 in  (* Default 30 second timeout *)
  let input_files = ref [] in
  let validate_preds = ref false in
  let disable_z3_simplify = ref false in

  (* Argument specification *)
  let spec = [
    ("--debug", Arg.Unit (fun () -> set_debug_mode true),
     " Enable debug mode with debug directory creation");
    ("--timeout", Arg.Int (fun t -> timeout_ms := t),
     "<timeout_ms> Timeout in milliseconds for solver operations (default: 30000)");
    ("--validate_preds", Arg.Set validate_preds,
     " Enable mutually exclusive predecessor check");
    ("--no-z3-simplify", Arg.Set disable_z3_simplify,
     " Disable Z3 simplification before effect optimization");
  ] in

  let usage_msg = Printf.sprintf "Usage: %s [options] <smt2_file>\nOptions:" Sys.argv.(0) in

  (* Parse anonymous arguments (input files) *)
  let anon_fun filename = input_files := filename :: !input_files in

  (* Parse command line arguments *)
  Arg.parse spec anon_fun usage_msg;

  (* Validate input *)
  match List.rev !input_files with
  | [] ->
      Printf.printf "Error: No input file specified\n";
      Arg.usage spec usage_msg;
      exit 1
  | [filename] ->
      if process_file filename !timeout_ms !disable_z3_simplify !validate_preds then
        exit 0
      else
        exit 1
  | _ ->
      Printf.printf "Error: Too many input files specified\n";
      Arg.usage spec usage_msg;
      exit 1
