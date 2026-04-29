(** Incremental solver interface supporting single and multi-solver backends *)

open Utilities
open Data_structures
open Smtlib_output

(** Internal process handle — not exposed to callers *)
type solver_process = {
  stdin: out_channel;
  stdout: in_channel;
  stderr: in_channel;
  debug_log: out_channel option;
  pid: int option;  (* Some pid when started via create_process_env; None for open_process_full *)
}

(** Merge two check-sat responses. "unsat" beats "sat" beats "unknown".
    Disagreement between "sat" and "unsat" is a soundness bug — log and trust "unsat". *)
let merge_responses r1 r2 =
  match r1, r2 with
  | "unsat", _ | _, "unsat" -> "unsat"
  | "sat",   _ | _, "sat"   -> "sat"
  | _                        -> "unknown"

(** Wrap a raw solver process into the abstract solver interface.
    Sexp commands are rendered to SMT-LIB strings before being sent.
    [push_cmd] / [pop_cmd] allow backends to override scope commands. *)
let process_solver ~name
    ?(push_cmd = "(push)\n") ?(pop_cmd = "(pop)\n")
    (p : solver_process) : solver =
  let hist = Buffer.create 4096 in
  let send_str cmd =
    Buffer.add_string hist cmd;
    (match p.debug_log with Some l -> output_string l cmd; flush l | None -> ());
    output_string p.stdin cmd;
    flush p.stdin
  in
  let recv () = String.trim (input_line p.stdout) in
  let render = sexp_to_smtlib in
  (* Track when check_sat is in flight so interrupt only fires mid-query. *)
  let in_check_sat = ref false in
  {
    name;
    set_logic     = (fun l ->
      send_str (Printf.sprintf "(set-logic %s)\n" l));
    set_option    = (fun k v ->
      send_str (Printf.sprintf "(set-option %s %s)\n" k v));
    declare_const = (fun n s ->
      send_str (Printf.sprintf "(declare-const %s %s)\n" n (render s)));
    fun_def       = (fun ty n defs ->
      let kw = match ty with `Def -> "define-fun" | `Decl -> "declare-fun" in
      let args = String.concat " " (List.map render defs) in
      send_str (Printf.sprintf "(%s %s %s)\n" kw n args));
    assert_       = (fun e ->
      send_str (Printf.sprintf "(assert %s)\n" (render e)));
    assert_named  = (fun nm e ->
      send_str (Printf.sprintf "(assert (! %s :named %s))\n" (render e) nm));
    push          = (fun () -> send_str push_cmd);
    pop           = (fun () -> send_str pop_cmd);
    interrupt     = (fun () ->
      if !in_check_sat then
        match p.pid with
        | None     -> ()
        | Some pid -> (try Unix.kill pid Sys.sigint with Unix.Unix_error _ -> ()));
    check_sat     = (fun () ->
      in_check_sat := true;
      Fun.protect
        (fun () -> send_str "(check-sat)\n"; recv ())
        ~finally:(fun () -> in_check_sat := false));
    history       = (fun () -> Buffer.contents hist);
    close         = (fun () ->
      (match p.debug_log with Some l -> close_out l | None -> ());
      match p.pid with
      | None ->
          close_out p.stdin;
          ignore (Unix.close_process_full (p.stdout, p.stdin, p.stderr))
      | Some pid ->
          (try close_out p.stdin  with _ -> ());
          (try close_in  p.stdout with _ -> ());
          (try close_in  p.stderr with _ -> ());
          ignore (Unix.waitpid [] pid));
  }

(** Multi-solver: broadcasts to all backends; check_sat runs both and merges. *)
let multi_solver (primary : solver) (secondary : solver) : solver = {
  name          = primary.name ^ "+" ^ secondary.name;
  set_logic     = (fun l  -> primary.set_logic l; secondary.set_logic l);
  set_option    = (fun k v -> primary.set_option k v; secondary.set_option k v);
  declare_const = (fun n s -> primary.declare_const n s; secondary.declare_const n s);
  fun_def       = (fun ty n d -> primary.fun_def ty n d; secondary.fun_def ty n d);
  assert_       = (fun e  -> primary.assert_ e; secondary.assert_ e);
  assert_named  = (fun nm e -> primary.assert_named nm e; secondary.assert_named nm e);
  push          = (fun () -> primary.push (); secondary.push ());
  pop           = (fun () -> primary.pop  (); secondary.pop  ());
  interrupt     = (fun () -> primary.interrupt (); secondary.interrupt ());
  check_sat     = (fun () ->
    let r1 = primary.check_sat () in
    let r2 = secondary.check_sat () in
    merge_responses r1 r2);
  history       = primary.history;
  close         = (fun () -> primary.close (); secondary.close ());
}

(** Per-name version counters for dump_version *)
let version_counters : (string, int ref) Hashtbl.t = Hashtbl.create 8

(** Write a versioned snapshot of the solver's current history to the debug directory. *)
let dump_version ?(extra = "") (s : solver) name =
  let counter =
    match Hashtbl.find_opt version_counters name with
    | Some c -> c
    | None ->
        let c = ref 0 in
        Hashtbl.add version_counters name c;
        c
  in
  incr counter;
  let filename = Printf.sprintf "%s_v%03d.smt2" name !counter in
  let path = get_debug_file_path filename in
  let oc = open_out path in
  output_string oc (s.history ());
  if extra <> "" then output_string oc extra;
  close_out oc

(** Start a single incremental CVC5 solver using the native OCaml API. *)
let begin_solver state timeout_ms : solver =
  let s = Cvc5_backend.make_solver timeout_ms in
  emit_variable_declarations s state.source;
  emit_variable_declarations s state.target;
  s

(** Start a single incremental Z3 solver using the native OCaml API. *)
let begin_z3_solver state timeout_ms : solver =
  let s = Z3_backend.make_solver timeout_ms in
  emit_variable_declarations s state.source;
  emit_variable_declarations s state.target;
  s

(** Start a Bitwuzla solver using the native OCaml API. *)
let begin_bitwuzla_solver state timeout_ms : solver =
  let s = Bitwuzla_backend.make_solver timeout_ms in
  emit_variable_declarations s state.source;
  emit_variable_declarations s state.target;
  s

(** Start a multi-solver: CVC5, Z3, and Bitwuzla in parallel. *)
let begin_multi_solver state timeout_ms : solver =
  let cvc5 = begin_solver          state timeout_ms in
  let z3   = begin_z3_solver       state timeout_ms in
  let bw   = begin_bitwuzla_solver state timeout_ms in
  let run_timed solver =
    let result = ref ("unknown", 0.0) in
    let t = Thread.create (fun () ->
      let t0 = Unix.gettimeofday () in
      let r = solver.check_sat () in
      result := (r, (Unix.gettimeofday () -. t0) *. 1000.0)
    ) () in
    (t, result)
  in
  let timed_check () =
    let (t1, r1) = run_timed cvc5 in
    let (t2, r2) = run_timed z3 in
    let (t3, r3) = run_timed bw in
    Thread.join t1; Thread.join t2; Thread.join t3;
    let (res1, ms1) = !r1 in
    let (res2, ms2) = !r2 in
    let (res3, ms3) = !r3 in
    let res = merge_responses res1 (merge_responses res2 res3) in
    debug_printf "\n  [SOLVERS]: %s, %.2fms, %s, %.2fms, %s, %.2fms, %s\n"
      res ms1 res1 ms2 res2 ms3 res3;
    res
  in
  {
    name          = cvc5.name ^ "+" ^ z3.name ^ "+" ^ bw.name;
    set_logic     = (fun l  -> cvc5.set_logic l; z3.set_logic l; bw.set_logic l);
    set_option    = (fun k v -> cvc5.set_option k v; z3.set_option k v; bw.set_option k v);
    declare_const = (fun n s -> cvc5.declare_const n s; z3.declare_const n s; bw.declare_const n s);
    fun_def       = (fun ty n d -> cvc5.fun_def ty n d; z3.fun_def ty n d; bw.fun_def ty n d);
    assert_       = (fun e  -> cvc5.assert_ e; z3.assert_ e; bw.assert_ e);
    assert_named  = (fun nm e -> cvc5.assert_named nm e; z3.assert_named nm e; bw.assert_named nm e);
    push          = (fun () -> cvc5.push (); z3.push (); bw.push ());
    pop           = (fun () -> cvc5.pop  (); z3.pop  (); bw.pop  ());
    interrupt     = (fun () -> cvc5.interrupt (); z3.interrupt (); bw.interrupt ());
    check_sat     = timed_check;
    history       = cvc5.history;
    close         = (fun () -> cvc5.close (); z3.close (); bw.close ());
  }

(** Sequential first-wins solver: CVC5 first, then Z3, then Bitwuzla. *)
let begin_cascade_solver state timeout_ms : solver =
  let sb = begin_solver          state timeout_ms in
  let sc = begin_z3_solver       state timeout_ms in
  let sa = begin_bitwuzla_solver state timeout_ms in
  let solvers = [| sa; sb; sc |] in
  let cascade_check () =
    let t0 = Unix.gettimeofday () in
    let r0 = sa.check_sat () in
    let t1 = Unix.gettimeofday () in
    if r0 <> "unknown" then r0
    else begin
      let r1 = sb.check_sat () in
      let t2 = Unix.gettimeofday () in
      if r1 <> "unknown" then begin
        debug_printf "(fallback: %.2fms, %.2fms)"
          ((t1 -. t0) *. 1000.0) ((t2 -. t1) *. 1000.0);
        r1
      end else begin
        let r2 = sc.check_sat () in
        let t3 = Unix.gettimeofday () in
        debug_printf "(fallback: %.2fms, %.2fms, %.2fms)"
          ((t1 -. t0) *. 1000.0) ((t2 -. t1) *. 1000.0) ((t3 -. t2) *. 1000.0);
        r2
      end
    end
  in
  {
    name          = sa.name ^ "+" ^ sb.name ^ "+" ^ sc.name;
    set_logic     = (fun l  -> Array.iter (fun s -> s.set_logic l) solvers);
    set_option    = (fun k v -> Array.iter (fun s -> s.set_option k v) solvers);
    declare_const = (fun n t -> Array.iter (fun s -> s.declare_const n t) solvers);
    fun_def       = (fun ty n d -> Array.iter (fun s -> s.fun_def ty n d) solvers);
    assert_       = (fun e  -> Array.iter (fun s -> s.assert_ e) solvers);
    assert_named  = (fun nm e -> Array.iter (fun s -> s.assert_named nm e) solvers);
    push          = (fun () -> Array.iter (fun s -> s.push ()) solvers);
    pop           = (fun () -> Array.iter (fun s -> s.pop  ()) solvers);
    interrupt     = (fun () -> Array.iter (fun s -> s.interrupt ()) solvers);
    check_sat     = cascade_check;
    history       = sa.history;
    close         = (fun () -> Array.iter (fun s -> s.close ()) solvers);
  }

(** First-wins concurrent solver: runs CVC5, Z3, and Bitwuzla in parallel.
    Returns as soon as any backend produces sat/unsat, then cancels the others.
    Cancellation is per-backend: CVC5 polls at [poll_ms] intervals (default 100ms),
    Z3 receives SIGINT, Bitwuzla uses its native interrupt callback. *)
let begin_concurrent_solver state timeout_ms : solver =

  let z3 = begin_z3_solver state timeout_ms in
  let bw = begin_bitwuzla_solver state timeout_ms in
  let cvc5 = begin_solver state timeout_ms in

  let solvers = [| bw; z3; cvc5 |] in

  let concurrent_check () =
    let result    = ref "unknown" in
    let completed = ref 0 in
    let mu   = Mutex.create () in
    let cond = Condition.create () in
    let n = Array.length solvers in
    let run s () =
      let _t0 = Unix.gettimeofday () in
      let r  = s.check_sat () in
      (*let ms = (Unix.gettimeofday () -. t0) *. 1000.0 in
      debug_printf "\n[CONCURRENT] %s done in %.2fms (%s)\n" s.name ms r;*)
      Mutex.lock mu;
      incr completed;
      if r <> "unknown" && !result = "unknown" then begin
        result := r;
        debug_printf "(%s : %s) " s.name r;
        Array.iter (fun s2 -> s2.interrupt ()) solvers;
      end;
      Condition.signal cond;
      Mutex.unlock mu
    in
    let threads = Array.map (fun s -> Thread.create (run s) ()) solvers in
    Mutex.lock mu;
    while !result = "unknown" && !completed < n do
      Condition.wait cond mu
    done;
    Mutex.unlock mu;
    Array.iter Thread.join threads;
    !result
  in

  { name          = "concurrent";
    set_logic     = (fun l  -> Array.iter (fun s -> s.set_logic l) solvers);
    set_option    = (fun k v -> Array.iter (fun s -> s.set_option k v) solvers);
    declare_const = (fun n t -> Array.iter (fun s -> s.declare_const n t) solvers);
    fun_def       = (fun ty n d -> Array.iter (fun s -> s.fun_def ty n d) solvers);
    assert_       = (fun e  -> Array.iter (fun s -> s.assert_ e) solvers);
    assert_named  = (fun nm e -> Array.iter (fun s -> s.assert_named nm e) solvers);
    push          = (fun () -> Array.iter (fun s -> s.push ()) solvers);
    pop           = (fun () -> Array.iter (fun s -> s.pop  ()) solvers);
    interrupt     = (fun () -> Array.iter (fun s -> s.interrupt ()) solvers);
    check_sat     = concurrent_check;
    history       = z3.history;
    close         = (fun () -> Array.iter (fun s -> s.close ()) solvers) }

(** Scoped solve: push → emit assertions → check-sat → pop.
    [emit] is a thunk called between push and check-sat. *)
let scoped_solve ?cmt:_ (s : solver) (emit : solver -> unit) =
  s.push ();
  emit s;
  let result = s.check_sat () in
  s.pop ();
  match result with
  | "unsat"   -> UNSOLVED []
  | "sat"     -> SOLVED
  | _         -> UNSOLVED [()]

let scoped_probe solver emit =
  solver.push ();
  emit solver;
  let resp = solver.check_sat () in
  solver.pop ();
  resp
