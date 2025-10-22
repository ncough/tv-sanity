(** CVC5 solver interface *)

open Utilities
open Smtlib_output


let result_of_cvc goal exit_status output =
    match exit_status, String.trim output with
    | Unix.WEXITED 0, "sat" -> SOLVED
    | Unix.WEXITED 0, "unsat" -> UNSOLVED []
    | Unix.WEXITED 0, _ -> UNSOLVED [goal]
    | _, "cvc5 interrupted by timeout." ->
        (* CVC5 timeout - treat as unsolved *)
        UNSOLVED [goal]
    | _ ->
        Printf.printf "CVC5 Error: %s\n" output;
        UNSOLVED [goal]

(** Apply CVC5 tactic to a goal with state context *)
let apply_tactic state timeout tactic goal =
  with_temp_file "cvc5_tactic" ".smt2" (fun temp_file ->
    (* Create SMT-LIB file with tactic and goal *)
    let content = Printf.sprintf "%s\n%s\n" goal tactic in
    create_smtlib_file_with_content state content temp_file;

    (* Run CVC5 with timeout *)
    let cvc5_cmd = Printf.sprintf "%s --tlimit %d --repeat-simp %s" cvc5_path timeout temp_file in
    let (exit_status, output) = run_command cvc5_cmd in

    result_of_cvc goal exit_status output
  )

(** Simple CVC5 satisfiability check *)
let check_sat state timeout goal =
  apply_tactic state timeout "(check-sat)" goal
