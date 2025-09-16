(** Utility functions for SMT parsing and analysis *)

open Sexplib0.Sexp

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let cvc5_path = "cvc5"
let z3_path = "z3"

let unreachable () = failwith "unreachable"

(** Check if a string represents a program variable (has source__/target__ prefix) *)
let is_var var =
  String.starts_with ~prefix:"source__" var || String.starts_with ~prefix:"target__" var

(** Check if a variable represents a block (ends with _done) *)
let is_block var =
  is_var var && String.ends_with ~suffix:"_done" var

let is_exit_block var =
  is_var var && String.ends_with ~suffix:"_SYNTH_EXIT_done" var

(** Check if a variable belongs to the source program *)
let is_source var =
  String.starts_with ~prefix:"source__" var

(** Check if a variable belongs to the target program *)
let is_target var =
  String.starts_with ~prefix:"target__" var

(** Extract all free variables from an S-expression *)
let rec free_vars expr =
  match expr with
  | Atom var when is_var var -> StringSet.singleton var
  | Atom _ -> StringSet.empty
  | List exprs ->
      List.fold_left (fun acc e -> StringSet.union acc (free_vars e)) StringSet.empty exprs

(** Convert S-expression to string representation *)
let rec pp_sexp sexp =
  match sexp with
  | Atom s -> s
  | List sexps ->
      "(" ^ String.concat " " (List.map pp_sexp sexps) ^ ")"

(** Load S-expressions from a string *)
let load_sexp s =
  match Parsexp.Single.parse_string_exn s with
  | List sexps -> Ok sexps
  | Atom _ -> Error "Expected list of S-expressions"
  | exception Parsexp.Parse_error error ->
      Error (Parsexp.Parse_error.message error)

(** Compute intersection of string sets from list *)
let inter_all = function
  | [] -> StringSet.empty
  | [s] -> s
  | s :: rest -> List.fold_left StringSet.inter s rest

let union_all = function
  | [] -> StringSet.empty
  | [s] -> s
  | s :: rest -> List.fold_left StringSet.union s rest


let pp_set set =
  String.concat "," (StringSet.elements set)

let pp_map fn m =
  String.concat "," (List.map fn (StringMap.bindings m))

(** Global debug flag - off by default *)
let debug_enabled = ref false

(** Set debug mode *)
let set_debug_mode enabled = debug_enabled := enabled

(** Check if debug mode is enabled *)
let is_debug_enabled () = !debug_enabled

(** Debug printing function *)
let debug_printf fmt =
  if is_debug_enabled () then begin
    flush_all ();
    Printf.printf fmt
  end else
    Printf.ifprintf stdout fmt

(** CVC5 solver path and configuration *)

(** Timing utility function *)
let get_time fn =
  let start_time = Unix.gettimeofday () in
  let res = fn () in
  let end_time = Unix.gettimeofday () in
  let elapsed_ms = (end_time -. start_time) *. 1000.0 in
  (res,elapsed_ms)

(** Initialize random seed for unique directory names *)
let () = Random.self_init ()

(** Debug directory management *)
let debug_directory = ref None

(** Generate unique debug directory name with collision avoidance *)
let generate_unique_debug_dir_name base_filename =
  let max_attempts = 1000 in
  let rec try_generate attempts =
    if attempts >= max_attempts then
      failwith ("Unable to generate unique debug directory name after " ^
                string_of_int max_attempts ^ " attempts")
    else
      let random_value = Random.int 100000 in  (* Increased range for better uniqueness *)
      let dir_name = Printf.sprintf "%s_debug_%05d" base_filename random_value in
      if Sys.file_exists dir_name then
        (* Directory exists, try again with new random number *)
        try_generate (attempts + 1)
      else
        dir_name
  in
  try_generate 0

(** Create debug directory based on filename and random value *)
let create_debug_directory base_filename =
  if is_debug_enabled () then begin
    let dir_name = generate_unique_debug_dir_name base_filename in
    (try
      Unix.mkdir dir_name 0o755;
      debug_directory := Some dir_name;
      debug_printf "Created debug directory: %s\n" dir_name;
      dir_name
    with
    | Unix.Unix_error (error, _, _) ->
        let error_msg = Printf.sprintf "Failed to create debug directory %s: %s"
                         dir_name (Unix.error_message error) in
        debug_printf "%s\n" error_msg;
        failwith error_msg
    | exn ->
        let error_msg = Printf.sprintf "Failed to create debug directory %s: %s"
                         dir_name (Printexc.to_string exn) in
        debug_printf "%s\n" error_msg;
        failwith error_msg)
  end else
    failwith "Debug directory requested but debug mode is disabled"

(** Get debug directory path *)
let get_debug_directory () = !debug_directory

(** Get debug file path *)
let get_debug_file_path filename =
  match get_debug_directory () with
  | Some dir -> Filename.concat dir filename
  | None -> filename  (* fallback to current directory if no debug dir *)

(** Solver result type *)
type solver_result =
  | UNSAT
  | SAT
  | UNKNOWN of string list

(** Temporary file management with automatic cleanup *)
let with_temp_file prefix suffix f =
  let temp_filename =
    if is_debug_enabled () then
      get_debug_file_path (Printf.sprintf "%s_%05d%s" prefix (Random.int 100000) suffix)
    else
      Printf.sprintf "%s_%05d%s" prefix (Random.int 100000) suffix
  in
  let result =
    try
      f temp_filename
    with exn ->
      (* Clean up on exception if not in debug mode *)
      (if not (is_debug_enabled ()) then
        try Sys.remove temp_filename with _ -> ());
      raise exn
  in
  (* Clean up normally if not in debug mode *)
  (if not (is_debug_enabled ()) then
    try Sys.remove temp_filename with _ -> ());
  result

(** Run external command and capture output *)
let run_command cmd =
  debug_printf "  Running command: %s\n" cmd;
  let ic = Unix.open_process_in cmd in
  let buffer = Buffer.create 8192 in
  (try
    while true do
      let line = input_line ic in
      Buffer.add_string buffer line;
      Buffer.add_char buffer '\n'
    done
  with End_of_file -> ());
  let output = Buffer.contents buffer in
  let exit_status = Unix.close_process_in ic in
  (exit_status, output)
