open Utilities

let make (res_ms: int) (solvers : (module Solver.Solver) list) : (module Solver.Solver) =
  let arr = Array.of_list solvers in
  let timeout_ms = ref 0 in
  (module struct
    let name = "rr"
    let set_timeout ms = begin
      Array.iter (fun (module M : Solver.Solver) -> M.set_timeout res_ms) arr;
      timeout_ms := ms
    end
    let set_logic l    = Array.iter (fun (module M : Solver.Solver) -> M.set_logic l) arr
    let set_option k v = Array.iter (fun (module M : Solver.Solver) -> M.set_option k v) arr
    let declare_const n s = Array.iter (fun (module M : Solver.Solver) -> M.declare_const n s) arr
    let add e    = Array.iter (fun (module M : Solver.Solver) -> M.add e) arr
    let push ()  = Array.iter (fun (module M : Solver.Solver) -> M.push ()) arr
    let pop ()   = Array.iter (fun (module M : Solver.Solver) -> M.pop ()) arr
    let close ()     = Array.iter (fun (module M : Solver.Solver) -> M.close ()) arr
    let check_sat_assuming assumptions =
      debug_printf "(";
      let n = Array.length arr in
      let tend = Unix.gettimeofday () +. ((float_of_int !timeout_ms) /. 1000.0) in
      let rec loop i =
        let (module M : Solver.Solver) = arr.(i) in
        let r = M.check_sat_assuming assumptions  in
        debug_printf "%s: %s" M.name (Solver.pp_r r);
        match r with
        | Solver.Unknown when i + 1 < n -> 
            debug_printf ", ";
            loop (i + 1)
        | Solver.Unknown when tend > Unix.gettimeofday () -> 
            debug_printf ", ";
            loop 0
        | _ ->
            debug_printf ") ";
            r
      in
      loop 0
  end)
