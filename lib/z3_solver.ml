(** Z3 solver interface *)

open Utilities
open Smtlib_output

(** Parse goals from Z3 tactic output *)
let parse_z3_goals output =
  let lines = String.split_on_char '\n' output in
  let goals = ref [] in
  let current_goal = ref [] in
  let in_goal = ref false in

  List.iter (fun line ->
    if line = "(goal" then begin
      (* Starting a new goal *)
      if !current_goal <> [] then begin
        (* Save previous goal *)
        let goal_content = "(assert (and\n" ^ String.concat "\n" (List.rev !current_goal) ^ "\n))" in
        goals := goal_content :: !goals;
        current_goal := []
      end;
      in_goal := true
    end else if String.starts_with ~prefix:"  :pre" line then begin
      in_goal := false
    end else if !in_goal then begin
      current_goal := line :: !current_goal
    end
  ) lines;

  (* Don't forget the last goal *)
  if !current_goal <> [] then begin
    let goal_content = "(assert (and\n" ^ String.concat "\n" (List.rev !current_goal) ^ "\n))" in
    goals := goal_content :: !goals
  end;

  List.rev !goals

(** Analyze Z3 output and determine result *)
let analyze_z3_output output =
  match String.trim output with
  | "sat" -> SOLVED
  | "unsat" -> UNSOLVED []
  | s when String.starts_with ~prefix:"(goals" s ->
      UNSOLVED (parse_z3_goals output)
  | _ ->
      failwith ("Z3 error: " ^ output)

(** Apply Z3 tactic to a goal with state context *)
let apply_tactic state tactic goal =
  with_temp_file "z3_tactic" ".smt2" (fun temp_file ->
    let content = Printf.sprintf "%s\n%s\n" goal tactic in
    create_smtlib_file_with_content state content temp_file;
    let z3_cmd = Printf.sprintf "%s %s" z3_path temp_file in
    let (exit_status, output) = run_command z3_cmd in
    match exit_status with
    | Unix.WEXITED 0 -> analyze_z3_output output
    | _ ->
        debug_printf "Z3 failed with exit status and output:\n%s\n" output;
        failwith "Z3 execution failed"
  )

(** Z3 satisfiability check *)
let check_sat state goal =
  apply_tactic state "(check-sat)" goal

(** Z3 simplification tactic *)
let simplify state goal =
  apply_tactic state "(apply (repeat (then propagate-values simplify)))" goal
