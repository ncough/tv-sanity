(** Main entry point for tv-sanity *)

open Tv_sanity.Program_parser
open Tv_sanity.Solver_pipeline
open Tv_sanity.Utilities
open Tv_sanity.Solver

(** Parse and process a single SMT-LIB2 file with main pipeline *)
let process_file filename ~timeout_ms ~use_async ~resolution_ms ~enable_z3 ~enable_cvc5 ~enable_bitwuzla =
  try
    let state = parse_file filename in
    let base_filename = Filename.remove_extension filename in

    (* Create debug directory if in debug mode *)
    (if is_debug_enabled () then ignore (create_debug_directory (Filename.basename base_filename)));

    (* Apply copy/constant propagation *)
    let state = Tv_sanity.Copy_prop.transform_state state in

    let (r,ms) = solve state ~timeout_ms ~use_async ~resolution_ms ~enable_z3 ~enable_cvc5 ~enable_bitwuzla in
    if is_debug_enabled () then
      Printf.printf "%s in %.2fms\n" (pp_r r) ms
    else
      Printf.printf "%s\n" (pp_r r);
    0
  with
  | exn ->
    let error_msg = Printexc.to_string exn in
    debug_printf "FAIL: %s - %s\n" (Filename.basename filename) error_msg;
    Printf.printf "unknown\n" ;
    1

(** Main entry point *)
let () =
  (* Command line argument variables *)
  let timeout_ms = ref 10000 in
  let resolution_ms = ref 1000 in
  let use_async = ref true in
  let input_files = ref [] in
  let enable_z3 = ref true in
  let enable_cvc5 = ref true in
  let enable_bitwuzla = ref true in
  let version = ref false in

  (* Argument specification *)
  let spec = [
    ("--debug", Arg.Unit (fun () -> set_debug_mode true),
     " Enable debug mode with debug directory creation");
    ("--timeout", Arg.Int (fun t -> timeout_ms := t),
     "<timeout_ms> Timeout in milliseconds for solver operations (default: 10000)");
    ("--resolution", Arg.Int (fun r -> resolution_ms := r),
     "<ms> Per-solver check-sat budget in milliseconds (default: 1000)");
    ("--sync", Arg.Clear use_async,
     " Use synchronous round-robin solving instead of async");
    ("--disable-z3", Arg.Clear enable_z3,
     " Disable use of z3");
    ("--disable-cvc5", Arg.Clear enable_cvc5,
     " Disable use of cvc5");
    ("--disable-bw", Arg.Clear enable_bitwuzla,
     " Disable use of bitwuzla");
    ("--version", Arg.Set version,
     " Dump version information");
  ] in

  let usage_msg = Printf.sprintf "Usage: %s [options] <smt2_file>\nOptions:" Sys.argv.(0) in
  let anon_fun filename = input_files := filename :: !input_files in
  Arg.parse spec anon_fun usage_msg;

  if !version then begin
    List.iter (fun cmd ->
      let ic = Unix.open_process_in cmd in
      (try while true do print_string (input_line ic); print_char '\n' done
       with End_of_file -> ());
      ignore (Unix.close_process_in ic)
    ) ["z3 --version"; "cvc5 --version"; "bitwuzla --version"];
    exit 0
  end;

  (* Validate input *)
  match List.rev !input_files with
  | [] ->
      Printf.printf "Error: No input file specified\n";
      Arg.usage spec usage_msg;
      exit 1
  | [filename] ->
      let timeout_ms = !timeout_ms in
      let resolution_ms = !resolution_ms in
      let use_async = !use_async in
      let enable_z3 = !enable_z3 in
      let enable_cvc5 = !enable_cvc5 in
      let enable_bitwuzla = !enable_bitwuzla in
      let code = process_file filename
        ~timeout_ms ~use_async ~resolution_ms ~enable_z3 ~enable_cvc5 ~enable_bitwuzla in
      exit code
  | _ ->
      Printf.printf "Error: Too many input files specified\n";
      Arg.usage spec usage_msg;
      exit 1
