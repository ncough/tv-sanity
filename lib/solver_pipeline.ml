(** Solver pipeline orchestration for combining Z3 tactics and CVC5 *)

open Data_structures
open Utilities
open Smtlib_output

let z3_config   = ("timeout",    "z3", ["z3"; "-in"])
let cvc5_config = ("tlimit-per", "cvc5", ["cvc5"; "--incremental"; "--repeat-simp"])
let bw_config   = ("time-limit-per", "bitwuzla", ["bitwuzla"; "--rewrite-no-mul"; "--abstraction-bv-size"; "16"])

(** Run the incremental solver from an initial unconfigured state *)
let run (module S : Solver.Solver) state timeout_ms ~topo =
  S.set_logic "QF_UFBV";
  S.set_timeout timeout_ms;
  emit_fun_defs (module S) state.funs;
  emit_variable_declarations (module S) state.source;
  emit_variable_declarations (module S) state.target;
  emit_block_assertions (module S) state.source "source";
  emit_block_assertions (module S) state.target "target";
  emit_assignment_assertions (module S) state.source;
  emit_assignment_assertions (module S) state.target;
  emit_arbitrary_assertions (module S) state;
  let res = Effect_optimizer.run ~topo (module S) state.effects in
  S.close ();
  res

(** Main function for solving process *)
let solve state ~timeout_ms ~use_async ~resolution_ms ~enable_z3 ~enable_cvc5 ~enable_bitwuzla ~topo =
  let configs = [] in
  let configs = if enable_z3       then z3_config   :: configs else configs in
  let configs = if enable_bitwuzla then bw_config   :: configs else configs in
  let configs = if enable_cvc5     then cvc5_config :: configs else configs in
  let solver = match configs with
  | [] -> failwith "No solvers enabled!"
  | [s] -> Smtlib_solver.make s
  | _ when use_async -> Async_solver.make resolution_ms configs
  | _ -> Round_robin.make resolution_ms (List.map Smtlib_solver.make configs)
  in
  get_time (fun _ -> run solver state timeout_ms ~topo)
