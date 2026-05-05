(** Main entry point for tv-sanity *)

open Tv_sanity.Program_parser
open Tv_sanity.Solver_pipeline
open Tv_sanity.Utilities
open Tv_sanity.Solver


let result_of_cvc exit_status output =
    match exit_status, String.trim output with
    | Unix.WEXITED 0, "sat" -> Sat
    | Unix.WEXITED 0, "unsat" -> Unsat
    | Unix.WEXITED 0, _ -> Unknown
    | _, "cvc5 interrupted by timeout." ->
        (* CVC5 timeout - treat as unsolved *)
        Unknown
    | _ ->
        Unknown


let run_command cmd =
  debug_printf "  Running command: %s\n" cmd;
  let env = Unix.environment () in
  let (ic,oc,ec) = Unix.open_process_full cmd env in
  let buffer = Buffer.create 8192 in
  (try
    while true do
      let line = input_line ic in
      Buffer.add_string buffer line;
      Buffer.add_char buffer '\n'
    done
  with End_of_file -> ());
  let output = Buffer.contents buffer in
  let exit_status = Unix.close_process_full (ic,oc,ec) in
  (exit_status, output)

let cvc5_batch timeout_ms filename =
  let cvc5_cmd = Printf.sprintf "%s --tlimit %d --repeat-simp '%s'" "cvc5" timeout_ms filename in
  let (exit_status, output) = run_command cvc5_cmd in
  result_of_cvc exit_status output


(** Parse and process a single SMT-LIB2 file with main pipeline *)
let process_file filename ~timeout_ms ~use_async ~resolution_ms ~enable_z3 ~enable_cvc5 ~enable_bitwuzla ~fallback_batch  ~topo =
  try
    let state = parse_file filename in
    let base_filename = Filename.remove_extension filename in

    (* Create debug directory if in debug mode *)
    (if is_debug_enabled () then ignore (create_debug_directory (Filename.basename base_filename)));

    (* Apply copy/constant propagation *)
    let state = Tv_sanity.Copy_prop.transform_state state in

    let (r,ms) = solve state ~timeout_ms ~use_async ~resolution_ms ~enable_z3 ~enable_cvc5 ~enable_bitwuzla ~topo in
    if is_debug_enabled () then
      Printf.printf "%s in %.2fms\n" (pp_r r) ms
    ;
     let r = (match r with
         | Sat when fallback_batch -> begin
         let (final) = cvc5_batch timeout_ms filename in
         final
         end
         | o -> o
     ) in
      print_endline @@ pp_r r ;
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
  let topo = ref true in
  let version = ref false in
  let fallback_batch = ref false in

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
    ("--fallback-batch", Arg.Set fallback_batch,
     " On sat try again with cvc5 batch solver");
    ("--dom", Arg.Clear topo,
     " Use dominator walk");
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
      let fallback_batch = !fallback_batch in
      let topo = !topo in
      let code = process_file filename
        ~timeout_ms ~use_async ~resolution_ms ~enable_z3 ~enable_cvc5 ~enable_bitwuzla ~fallback_batch  ~topo in
      exit code
  | _ ->
      Printf.printf "Error: Too many input files specified\n";
      Arg.usage spec usage_msg;
      exit 1
