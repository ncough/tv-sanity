(** Solver pipeline orchestration for combining Z3 tactics and CVC5 *)

open Data_structures
open Utilities
open Smtlib_output

(*
  TODO:
    - Biggest slow down is large effect list
    - Can easily take multiple minutes for ~1000 effects
    - Possible improvements:
      1. Use the Z3 to preprocess the incremental solver state on a regular basis.
      2. Batch a sequential series of effects into a single request.
*)

(** Generate initial goal from state *)
let make_initial_goal state =
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer (generate_block_assertions state.source "source");
  Buffer.add_string buffer (generate_block_assertions state.target "target");
  Buffer.add_string buffer (generate_assignment_assertions state.source);
  Buffer.add_string buffer (generate_assignment_assertions state.target);
  Buffer.add_string buffer (generate_initial_assertions state.initial);
  Buffer.add_string buffer (generate_effect_assertions state.effects);
  Buffer.add_string buffer (generate_final_assertions state.final);
  Buffer.add_string buffer (generate_arbitrary_assertions state);
  UNKNOWN [Buffer.contents buffer]

(** Print solver result *)
let print_result result =
  match result with
  | SAT -> "sat"
  | UNSAT -> "unsat"
  | UNKNOWN _ -> "unknown"

(** Join solver results *)
let join a b =
  match a, b with
  | SAT, _ | _, SAT -> SAT
  | UNSAT, a | a, UNSAT -> a
  | UNKNOWN l1, UNKNOWN l2 -> UNKNOWN (l1@l2)

(** Bind operation for solver result monads *)
let bind = fun res f ->
  match res with
  | UNSAT -> UNSAT
  | SAT -> SAT
  | UNKNOWN l -> List.fold_right join (List.map f l) UNSAT

(** Alternative bind syntax *)
let (let@) = fun res f ->
  match res with
  | UNSAT -> UNSAT
  | SAT -> SAT
  | UNKNOWN l -> List.fold_right join (List.map f l) UNSAT

(** Get complexity of solver result *)
let complexity = function
  | UNKNOWN l -> List.length l
  | _ -> 0

(** Extract bound PC variables from S-expressions *)
let rec bound_pc_vars sexp =
  let open Sexplib0.Sexp in
  match sexp with
  | List [Atom "="; Atom var; List [Atom "_"; Atom bv_pattern; Atom "64"]]
        when String.starts_with ~prefix:"source__SYNTH_PC" var ->
          [var,bv_pattern]
  | List (_::terms) -> List.flatten (List.map bound_pc_vars terms)
  | _ -> []

(** Get all bound PC variables from predicates *)
let all_bound_pc_vars preds =
  let l = List.flatten (List.map (fun pred -> bound_pc_vars pred.term) preds) in
  List.fold_left (fun acc (var,bv) ->
    match acc with
    | None -> Some (var,StringSet.singleton bv)
    | Some (var',l) when var = var' -> Some (var',StringSet.add bv l)
    | Some (var',_) -> failwith @@ "multiple vars:" ^ var ^ " " ^ var') None l

(** Create disjunction of possible values for a SYNTH_PC variable *)
let create_synth_pc_disjunction var_name possible_integers =
  match StringSet.elements possible_integers with
  | [] -> failwith "not possible"
  | multiple ->
      (* Multiple values: (or (= var_name (_ bv1 64)) (= var_name (_ bv2 64)) ...) *)
      let equalities = List.map (fun integer ->
        Sexplib0.Sexp.List [
          Sexplib0.Sexp.Atom "=";
          Sexplib0.Sexp.Atom var_name;
          Sexplib0.Sexp.List [
            Sexplib0.Sexp.Atom "_";
            Sexplib0.Sexp.Atom integer;
            Sexplib0.Sexp.Atom "64"
          ]
        ]
      ) multiple in
      Sexplib0.Sexp.List (Sexplib0.Sexp.Atom "or" :: equalities)

(** Create disjunction from predicates *)
let create_disj preds =
  let res = all_bound_pc_vars preds in
  match res with
  | None -> failwith "huh"
  | Some (var,res) ->
      { term = create_synth_pc_disjunction var res  ; sat = None }

(** Process initial and final predicates to inject disjunctions *)
let inject_synth_pc_disjunctions_in_state state =
  let initial_vars = create_disj state.initial in
  let final_vars = create_disj state.final in
  { state with arbitrary = state.arbitrary @ [initial_vars;final_vars] }

(** Main function for Z3 tactic + CVC5 workflow *)
let optimize_with_z3_tactics state timeout_ms =
  debug_printf "Starting Effect Optimization...\n";

  let (state,time) = get_time (fun () -> Effect_optimizer.run state timeout_ms) in
  match state with
  | Effect_optimizer.UNSAT state -> Printf.printf "unsat\n"; state
  | Effect_optimizer.SAT state -> Printf.printf "sat\n"; state
  | Effect_optimizer.UNKNOWN state ->

  debug_printf "Finished Effect Optimization in %.2fms\n" time;
  debug_printf "Starting Simplification...\n";
  let (split,time) = get_time (fun () ->
    let state = inject_synth_pc_disjunctions_in_state state in
    let initial = make_initial_goal state in
    let tactic = "(apply (then split-clause split-clause simplify))" in
    bind initial (Z3_solver.apply_tactic state tactic))
  in
  debug_printf "Finished Simplification and Splitting to %d goals in %.2fms\n" (complexity split) time;
  debug_printf "Starting Solving...\n";
  let final = bind split (fun query ->
    let (res,time) = get_time (fun _ -> Cvc5_solver.check_sat state timeout_ms query) in
    debug_printf "  %s in %.2fms\n" (print_result res) time;
    res
  ) in
  debug_printf "Finished Solving\n";
  Printf.printf "%s\n" (print_result final);
  state

