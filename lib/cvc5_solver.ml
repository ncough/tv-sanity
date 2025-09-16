(** CVC5 solver interface *)

open Utilities
open Smtlib_output

(** Analyze CVC5 output and determine result *)
let analyze_cvc5_output output =
  match String.trim output with
  | "sat" -> SAT
  | "unsat" -> UNSAT
  | _ -> UNKNOWN [String.trim output]

(** Apply CVC5 tactic to a goal with state context *)
let apply_tactic state timeout tactic goal =
  with_temp_file "cvc5_tactic" ".smt2" (fun temp_file ->
    (* Create SMT-LIB file with tactic and goal *)
    let content = Printf.sprintf "%s\n%s\n" goal tactic in
    create_smtlib_file_with_content state content temp_file;

    (* Run CVC5 with timeout *)
    let cvc5_cmd = Printf.sprintf "%s --tlimit %d %s" cvc5_path timeout temp_file in
    let (exit_status, output) = run_command cvc5_cmd in

    match exit_status with
    | Unix.WEXITED 0 -> analyze_cvc5_output output
    | _ -> UNKNOWN [goal]
  )

(** Simple CVC5 satisfiability check *)
let check_sat state timeout goal =
  apply_tactic state timeout "(check-sat)" goal
