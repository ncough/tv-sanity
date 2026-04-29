(** Solver pipeline orchestration for combining Z3 tactics and CVC5 *)

open Data_structures
open Utilities
open Smtlib_output

(*
  TODO:
    - Possible improvements:
      1. Batch a sequential series of effects into a single request.
      2. Batch final goals based on common condition
      3. Directed splitting over exit condition
*)

(** Generate initial goal from state *)
let make_initial_goal ?(hints="") state =
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer (generate_block_assertions state.source "source");
  Buffer.add_string buffer (generate_block_assertions state.target "target");
  Buffer.add_string buffer (generate_assignment_assertions state.source);
  Buffer.add_string buffer (generate_assignment_assertions state.target);
  Buffer.add_string buffer (generate_effect_assertions state.effects);
  Buffer.add_string buffer (generate_arbitrary_assertions state);
  Buffer.add_string buffer hints;
  UNSOLVED [Buffer.contents buffer]

let optimize_with_z3_tactics state timeout_ms enable_z3_simplify enable_scope enable_multi_solver enable_cascade_solver =
  let@ (state, learnt) = wrap "Effect Opt" (fun () -> Effect_optimizer.run state timeout_ms enable_z3_simplify enable_scope enable_multi_solver enable_cascade_solver) in
  let@ initial = make_initial_goal ~hints:learnt state in
  let tactic = "(apply (then split-clause simplify))" in
  let@ simp = wrap "Simplify" (fun () -> Z3_solver.apply_tactic state tactic initial timeout_ms) in
  let@ cvc5_remaining = wrap "CVC5" (fun () ->
    let (res,time) = get_time (fun _ -> Cvc5_solver.check_sat state timeout_ms simp) in
    debug_printf "  %s in %.2fms\n" (pp_result res) time;
    res
  ) in
  let final = wrap "Z3 Final" (fun () ->
    let (res,time) = get_time (fun _ -> Z3_solver.check_sat state cvc5_remaining timeout_ms) in
    debug_printf "  %s in %.2fms\n" (pp_result res) time;
    res
  ) in
  final

(** Main function for Z3 tactic + CVC5 workflow *)
let solve state timeout_ms ~enable_z3_simplify enable_scope enable_multi_solver enable_cascade_solver =
  let (final,_) = get_time (fun () -> optimize_with_z3_tactics state timeout_ms enable_z3_simplify enable_scope enable_multi_solver enable_cascade_solver) in
  final
