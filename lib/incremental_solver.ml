(** Incremental solver interface supporting single and multi-solver backends *)

open Utilities
open Data_structures

(** Internal process handle — not exposed to callers *)
type solver_process = {
  stdin: out_channel;
  stdout: in_channel;
  stderr: in_channel;
  debug_log: out_channel option;
}

(** Abstract solver interface used by all callers.
    [send] is for assertion commands that produce no response.
    [push] and [pop] manage scope explicitly.
    [check] atomically sends (check-sat) to all backends and reads+merges
    all responses, ensuring no response is left unconsumed.
    [history] returns the full SMT2 transcript sent since initialisation. *)
type solver = {
  name      : string;
  send      : string -> unit;
  push      : unit -> unit;
  pop       : unit -> unit;
  check     : unit -> string;
  interrupt : unit -> unit;
  close     : unit -> unit;
  history   : unit -> string;
}

(** Merge two check-sat responses. "unsat" beats "sat" beats "unknown".
    Disagreement between "sat" and "unsat" is a soundness bug — log and trust "unsat". *)
let merge_responses r1 r2 =
  match r1, r2 with
  | "unsat", _ | _, "unsat" -> "unsat"
  | "sat",   _ | _, "sat"   -> "sat"
  | _                        -> "unknown"

(** Wrap a raw solver process into the abstract interface.
    When [name] is non-empty, each check prints its duration to debug output. *)
let process_solver ~name (p : solver_process) : solver =
  let hist = Buffer.create 4096 in
  let raw_send cmd =
    Buffer.add_string hist cmd;
    (match p.debug_log with Some log -> output_string log cmd; flush log | None -> ());
    output_string p.stdin cmd;
    flush p.stdin
  in
  let raw_recv () = String.trim (input_line p.stdout) in
  {
    name;
    send      = raw_send;
    push      = (fun () -> raw_send "(push)\n");
    pop       = (fun () -> raw_send "(pop)\n");
    check     = (fun () ->
      raw_send "(check-sat)\n";
      raw_recv ());
    interrupt = (fun () -> ());
    close     = (fun () ->
      (match p.debug_log with Some log -> close_out log | None -> ());
      close_out p.stdin;
      ignore (Unix.close_process_full (p.stdout, p.stdin, p.stderr)));
    history   = (fun () -> Buffer.contents hist);
  }

(** Multi-solver: broadcasts sends to all; [check] sends (check-sat) to both
    and reads both responses, so neither response is left unconsumed.
    Primary result is used unless it is "unknown", in which case secondary wins. *)
let multi_solver (primary : solver) (secondary : solver) : solver = {
  name      = primary.name ^ "+" ^ secondary.name;
  send      = (fun cmd -> primary.send cmd; secondary.send cmd);
  push      = (fun ()  -> primary.push (); secondary.push ());
  pop       = (fun ()  -> primary.pop  (); secondary.pop  ());
  check     = (fun () ->
    let r1 = primary.check () in
    let r2 = secondary.check () in
    merge_responses r1 r2);
  interrupt = (fun ()  -> primary.interrupt (); secondary.interrupt ());
  close     = (fun ()  -> primary.close (); secondary.close ());
  history   = primary.history;
}

(** Per-name version counters for dump_version *)
let version_counters : (string, int ref) Hashtbl.t = Hashtbl.create 8

(** Write a versioned snapshot of the solver's current history plus optional
    extra SMT2 content to [{name}_v{N:03d}.smt2] in the debug directory.
    The version number auto-increments per distinct [name]. *)
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

(** Send a command that produces no response *)
let send_to_solver (s : solver) cmd = s.send cmd

(** Push a scope on all backends *)
let push_solver (s : solver) = s.push ()

(** Pop a scope on all backends *)
let pop_solver (s : solver) = s.pop ()

(** Send (check-sat) to all backends and return the merged response *)
let check_solver (s : solver) = s.check ()

(** Close all solver backends *)
let close_solver (s : solver) = s.close ()


(** Start a raw CVC5 incremental process *)
let start_cvc5_process () =
  let env = Unix.environment () in
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let (proc_in, proc_out, proc_err) = Unix.open_process_full cvc5_path env in
  let debug_log =
    if is_debug_enabled () then
      Some (open_out (get_debug_file_path "incr_cvc5_debug.smt2"))
    else
      None
  in
  { stdin = proc_out; stdout = proc_in; stderr = proc_err; debug_log }

(** Start a raw Z3 incremental process *)
let start_z3_process () =
  let env = Unix.environment () in
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let (proc_in, proc_out, proc_err) = Unix.open_process_full (z3_path ^ " -in") env in
  let debug_log =
    if is_debug_enabled () then
      Some (open_out (get_debug_file_path "incr_z3_debug.smt2"))
    else
      None
  in
  { stdin = proc_out; stdout = proc_in; stderr = proc_err; debug_log }

(** Build and send the CVC5 preamble + declarations + base query, return a solver *)
let send_cvc5_preamble p state timeout_ms base_query =
  let s = process_solver ~name:"cvc5" p in
  let buf = Buffer.create 4096 in
  if timeout_ms >= 0 then
    Buffer.add_string buf (Printf.sprintf "(set-option :tlimit-per %d)\n" timeout_ms);
  Buffer.add_string buf "(set-option :incremental true)\n";
  Buffer.add_string buf "(set-option :repeat-simp true)\n";
  (*Buffer.add_string buf "(set-option :solve-bv-as-int iand)\n";*)
  Buffer.add_string buf "(set-logic QF_UFBV )\n";
  Buffer.add_string buf (Smtlib_output.generate_fun_defs state.funs);
  Buffer.add_string buf (Smtlib_output.generate_variable_declarations state.source);
  Buffer.add_string buf (Smtlib_output.generate_variable_declarations state.target);
  Buffer.add_string buf base_query;
  s.send (Buffer.contents buf);
  s

(** Build and send the Z3 preamble + declarations + base query, return a solver *)
let send_z3_preamble p state timeout_ms base_query =
  let s = process_solver ~name:"z3" p in
  let buf = Buffer.create 4096 in
  if timeout_ms >= 0 then
    Buffer.add_string buf (Printf.sprintf "(set-option :timeout %d)\n" timeout_ms);
  Buffer.add_string buf "(set-logic QF_UFBV )\n";
  Buffer.add_string buf (Smtlib_output.generate_fun_defs state.funs);
  Buffer.add_string buf (Smtlib_output.generate_variable_declarations state.source);
  Buffer.add_string buf (Smtlib_output.generate_variable_declarations state.target);
  Buffer.add_string buf base_query;
  s.send (Buffer.contents buf);
  s

(** Start a raw Bitwuzla process (non-incremental; use with stack_wrapper) *)
let start_bitwuzla_process () =
  let env = Unix.environment () in
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let (proc_in, proc_out, proc_err) = Unix.open_process_full bitwuzla_path env in
  let debug_log =
    if is_debug_enabled () then
      Some (open_out (get_debug_file_path "incr_bitwuzla_debug.smt2"))
    else
      None
  in
  { stdin = proc_out; stdout = proc_in; stderr = proc_err; debug_log }

(** Build and send the Bitwuzla preamble + declarations + base query, return a solver *)
let send_bitwuzla_preamble p state timeout_ms base_query =
  let s = process_solver ~name:"bitwuzla" p in
  let buf = Buffer.create 4096 in
  if timeout_ms >= 0 then
    Buffer.add_string buf (Printf.sprintf "(set-option :time-limit-per %d)\n" timeout_ms);
  Buffer.add_string buf "(set-option :incremental true)\n";
  Buffer.add_string buf "(set-logic QF_UFBV )\n";
  Buffer.add_string buf (Smtlib_output.generate_fun_defs state.funs);
  Buffer.add_string buf (Smtlib_output.generate_variable_declarations state.source);
  Buffer.add_string buf (Smtlib_output.generate_variable_declarations state.target);
  Buffer.add_string buf base_query;
  s.send (Buffer.contents buf);
  s

(** Start a single incremental CVC5 solver *)
let begin_solver state timeout_ms base_query : solver =
  send_cvc5_preamble (start_cvc5_process ()) state timeout_ms base_query

(** Start a single incremental Z3 solver *)
let begin_z3_solver state timeout_ms base_query : solver =
  send_z3_preamble (start_z3_process ()) state timeout_ms base_query

(** Start a single incremental Bitwuzla solver.
    Bitwuzla requires an explicit frame count on push/pop: (push 1) / (pop 1). *)
let begin_bitwuzla_solver state timeout_ms base_query : solver =
  let s = send_bitwuzla_preamble (start_bitwuzla_process ()) state timeout_ms base_query in
  { s with
    push = (fun () -> s.send "(push 1)\n");
    pop  = (fun () -> s.send "(pop 1)\n");
  }

(** Start a multi-solver: CVC5, Z3, and Bitwuzla in parallel.
    In debug mode, each check prints a single combined timing line:
    [SOLVERS]: T1ms, T2ms, T3ms *)
let begin_multi_solver state timeout_ms base_query : solver =
  let cvc5 = begin_solver          state timeout_ms base_query in
  let z3   = begin_z3_solver       state timeout_ms base_query in
  let bw   = begin_bitwuzla_solver state timeout_ms base_query in
  let run_timed solver =
    let result = ref ("unknown", 0.0) in
    let t = Thread.create (fun () ->
      let t0 = Unix.gettimeofday () in
      let r = solver.check () in
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
    let res =     merge_responses res1 (merge_responses res2 res3) in
    debug_printf "\n  [SOLVERS]: %s, %.2fms, %s, %.2fms, %s, %.2fms, %s\n" res ms1 res1 ms2  res2 ms3 res3;
    res
  in
  {
    name      = cvc5.name ^ "+" ^ z3.name ^ "+" ^ bw.name;
    send      = (fun cmd -> cvc5.send cmd; z3.send cmd; bw.send cmd);
    push      = (fun ()  -> cvc5.push (); z3.push (); bw.push ());
    pop       = (fun ()  -> cvc5.pop  (); z3.pop  (); bw.pop  ());
    check     = timed_check;
    interrupt = (fun ()  -> cvc5.interrupt (); z3.interrupt (); bw.interrupt ());
    close     = (fun ()  -> cvc5.close (); z3.close (); bw.close ());
    history   = cvc5.history;
  }

(** Sequential first-wins solver: Bitwuzla → Z3 → CVC5.
    All solvers receive every send/push/pop to keep state in sync.
    check short-circuits after the first sat/unsat result. *)
let begin_cascade_solver state timeout_ms base_query : solver =
  let sb   = begin_bitwuzla_solver state timeout_ms base_query in
  let sc   = begin_z3_solver       state timeout_ms base_query in
  let sa   = begin_solver          state timeout_ms base_query in
  let solvers = [| sa; sb; sc |] in
  let cascade_check () =
    let t0 = Unix.gettimeofday () in
    let r0 = sa.check () in
    let t1 = Unix.gettimeofday () in
    if r0 <> "unknown" then begin
      r0
    end else begin
      let r1 = sb.check () in
      let t2 = Unix.gettimeofday () in
      if r1 <> "unknown" then begin
        debug_printf "(fallback: %.2fms, %.2fms)"
          ((t1 -. t0) *. 1000.0) ((t2 -. t1) *. 1000.0);
        r1
      end else begin
        let r2 = sc.check () in
        let t3 = Unix.gettimeofday () in
        debug_printf "(fallback: %.2fms, %.2fms, %.2fms)"
          ((t1 -. t0) *. 1000.0) ((t2 -. t1) *. 1000.0) ((t3 -. t2) *. 1000.0);
        r2
      end
    end
  in
  {
    name      = sa.name ^ "+" ^ sb.name ^ "+" ^ sc.name;
    send      = (fun cmd -> Array.iter (fun s -> s.send cmd) solvers);
    push      = (fun ()  -> Array.iter (fun s -> s.push ()) solvers);
    pop       = (fun ()  -> Array.iter (fun s -> s.pop  ()) solvers);
    check     = cascade_check;
    interrupt = (fun ()  -> ());
    close     = (fun ()  -> Array.iter (fun s -> s.close ()) solvers);
    history   = sa.history;
  }

(** Scoped solve: push → query → check-sat → pop, returns a result *)
let scoped_solve ?cmt s query =
  ignore (Option.map (fun c ->
    send_to_solver s "; ";
    send_to_solver s c;
    send_to_solver s "\n") cmt);
  push_solver s;
  send_to_solver s query;
  let result = check_solver s in
  pop_solver s;
  match result with
  | "unsat"   -> UNSOLVED []
  | "sat"     -> SOLVED
  | "unknown" -> UNSOLVED [query]
  | error_msg ->
      Printf.printf "Solver error: %s\n" error_msg;
      UNSOLVED [query]
