(** Incremental CVC5 solver interface *)

open Utilities
open Data_structures

(** Solver process management *)
type solver_process = {
  stdin: out_channel;
  stdout: in_channel;
  stderr: in_channel;
  debug_log: out_channel option;
}

(** Start incremental CVC5 solver process *)
let start_incremental_solver () =
  let env = Unix.environment () in
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let (proc_in, proc_out, proc_err) = Unix.open_process_full cvc5_path (env) in
  let debug_log =
    if is_debug_enabled () then
      let debug_filename = get_debug_file_path "incr_cvc5_debug.smt2" in
      Some (open_out debug_filename)
    else
      None
  in
  { stdin = proc_out; stdout = proc_in; stderr = proc_err; debug_log }

(** Send command to solver *)
let send_to_solver solver cmd =
  (match solver.debug_log with
   | Some log -> output_string log cmd; flush log
   | None -> ());
  output_string solver.stdin cmd;
  flush solver.stdin

let begin_solver state timeout_ms base_query =
  let solver = start_incremental_solver () in
  let final_buffer = Buffer.create 4096 in

  (* Enable incremental mode *)
  if timeout_ms >= 0 then
    Buffer.add_string final_buffer (Printf.sprintf "(set-option :tlimit-per %d)\n" timeout_ms);
  Buffer.add_string final_buffer "(set-option :incremental true)\n";
  Buffer.add_string final_buffer "(set-option :repeat-simp true)\n";
  Buffer.add_string final_buffer "(set-logic QF_UFBV )\n";

  (* Add variable declarations for both programs *)
  Buffer.add_string final_buffer (Smtlib_output.generate_fun_defs state.funs);
  Buffer.add_string final_buffer (Smtlib_output.generate_variable_declarations state.source);
  Buffer.add_string final_buffer (Smtlib_output.generate_variable_declarations state.target);

  (* Add the simplified goal *)
  Buffer.add_string final_buffer base_query;

  send_to_solver solver (Buffer.contents final_buffer);

  solver

(** Read solver response *)
let read_solver_response solver =
  let line = input_line solver.stdout in
  String.trim line

(** Close solver process *)
let close_solver solver =
  (match solver.debug_log with
   | Some log -> close_out log
   | None -> ());
  close_out solver.stdin;
  ignore (Unix.close_process_full (solver.stdout, solver.stdin, solver.stderr))

(** Scoped solve that returns solver_result *)
let scoped_solve ?cmt solver_process query =
  ignore (Option.map (fun s ->
    send_to_solver solver_process "; ";
    send_to_solver solver_process s;
    send_to_solver solver_process "\n") cmt);
  send_to_solver solver_process "(push)\n";
  send_to_solver solver_process query;
  send_to_solver solver_process "(check-sat)\n";
  let result = read_solver_response solver_process in
  send_to_solver solver_process "(pop)\n";
  match result with
  | "unsat" -> UNSOLVED []
  | "sat" -> SOLVED
  | "unknown" -> UNSOLVED [query]
  | error_msg ->
      Printf.printf "Solver error: %s\n" error_msg;
      UNSOLVED [query]
