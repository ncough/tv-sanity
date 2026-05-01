type process = {
  pid:       int;
  stdin:     out_channel;
  stdout:    in_channel;
  stderr:    in_channel;
  debug_log: out_channel option;
}

type worker = {
  proc:           process;
  pending:        string list Atomic.t;
  timeout_option: string;
  solver_name:    string;
}

type shared = {
  mutable current_id:    int;
  mutable current_q:     string; (* Change to string *)
  mutable result:        Solver.result;
  mutable result_solver: string;
  mutable closed:        bool;
  mutex:                 Mutex.t;
  new_query:             Condition.t;
  got_result:            Condition.t;
}

let launch name argv =
  let debug_name = "async_" ^ name ^ "_debug.smt2" in
  let debug_log = Option.map open_out (Utilities.get_debug_file_path debug_name) in
  let (stdout_r, stdout_w) = Unix.pipe () in
  let (stdin_r,  stdin_w)  = Unix.pipe () in
  let (stderr_r, stderr_w) = Unix.pipe () in
  let pid = Unix.create_process_env
    (List.nth argv 0) (Array.of_list argv) (Unix.environment ())
    stdin_r stdout_w stderr_w in
  Unix.close stdin_r;
  Unix.close stdout_w;
  Unix.close stderr_w;
  { pid;
    stdin  = Unix.out_channel_of_descr stdin_w;
    stdout = Unix.in_channel_of_descr  stdout_r;
    stderr = Unix.in_channel_of_descr  stderr_r;
    debug_log }

let log_enabled = ref false

let send_strs p strs =
  List.iter (fun s ->
    (match p.debug_log with Some l -> output_string l s; flush l | None -> ());
    output_string p.stdin s
  ) strs;
  flush p.stdin

let recv p = String.trim (input_line p.stdout)

let parse_result = function
  | "sat"   -> Solver.Sat
  | "unsat" -> Solver.Unsat
  | "unknown" -> Solver.Unknown
  | msg      -> 
      (* Z3 nonsense? *)
      if String.ends_with ~suffix:"canceled\")" msg then Solver.Unknown else begin
        Utilities.debug_printf "unknown solver msg: %s\n" msg;
        Solver.Unknown
      end

let render = Smtlib_output.sexp_to_smtlib

let format_check_sat = function
  | [] -> "(check-sat)\n"
  | assumptions ->
    let lits = String.concat " " (List.map render assumptions) in
    Printf.sprintf "(check-sat-assuming (%s))\n" lits

let rec worker_loop w sh qid assumptions =
  let log fmt =
    if !log_enabled then Utilities.debug_printf ("[async %s] " ^^ fmt ^^ "\n") w.solver_name
    else Printf.ksprintf (fun _ -> ()) fmt
  in
  let drained = List.rev (Atomic.exchange w.pending []) in
  send_strs w.proc (drained @ [assumptions]);
  log "query %d: solving" qid;
  let r = parse_result (recv w.proc) in
  Mutex.lock sh.mutex;
  let closed = sh.closed in
  match r, sh.result with
  | _, _ when closed ->
      Mutex.unlock sh.mutex;
  | _, _ when sh.current_id <> qid ->
      Mutex.unlock sh.mutex;
      log "query %d: result %s discarded (current query now %d)" qid (Solver.pp_r r) sh.current_id
  | Unknown, _ ->
      Condition.signal sh.got_result;
      Mutex.unlock sh.mutex;
      log "query %d: result %s discarded (not useful)" qid (Solver.pp_r r);
      worker_loop w sh qid assumptions
  | _, Unknown ->
      sh.result <- r;
      sh.result_solver <- w.solver_name;
      log "query %d: result %s accepted" qid (Solver.pp_r r);
      Condition.signal sh.got_result;
      Mutex.unlock sh.mutex
  | _, a ->
      Mutex.unlock sh.mutex;
      log "query %d: result %s discarded (already %s)" qid (Solver.pp_r r) (Solver.pp_r a)

let worker_fn sh w () =
  let my_query_id = ref 0 in
  let running = ref true in
  while !running do
    Mutex.lock sh.mutex;
    while sh.current_id = !my_query_id && not sh.closed do
      Condition.wait sh.new_query sh.mutex
    done;
    if sh.closed then begin
      Mutex.unlock sh.mutex;
      running := false
    end else begin
      let qid = sh.current_id in
      let assumptions = sh.current_q in
      let skip = sh.result <> Solver.Unknown in
      my_query_id := qid;
      Mutex.unlock sh.mutex;
      if not skip then worker_loop w sh qid assumptions
    end
  done

(* Each config is (timeout_option, argv) for one solver process. *)
let make (res_ms: int) configs : (module Solver.Solver) =
  let workers = List.map (fun (timeout_option, argv) ->
    let solver_name = List.nth argv 0 in
    let proc = launch solver_name argv in
    { proc; pending = Atomic.make []; timeout_option; solver_name }
  ) configs in
  let timeout = ref None in
  let sh = {
    current_id    = 0;
    current_q     = "";
    result        = Solver.Unknown;
    result_solver = "";
    closed        = false;
    mutex         = Mutex.create ();
    new_query     = Condition.create ();
    got_result    = Condition.create ();
  } in
  let _threads = List.map (fun w -> Domain.spawn (worker_fn sh w)) workers in
  let enqueue w cmd =
    let rec push () =
      let old = Atomic.get w.pending in
      if Atomic.compare_and_set w.pending old (cmd :: old) then ()
      else push ()
    in push ()
  in
  let broadcast cmd = List.iter (fun w -> enqueue w cmd) workers in
  (module struct
    let name = "async"

    let set_timeout ms =
      timeout := (if ms = 0 then None else Some ms);
      List.iter (fun w -> 
        enqueue w (Printf.sprintf "(set-option :%s %d)\n" w.timeout_option res_ms)
      ) workers

    let set_logic l =
      broadcast (Printf.sprintf "(set-logic %s)\n" l)

    let set_option k v =
      broadcast (Printf.sprintf "(set-option %s %s)\n" k v)

    let declare_const n s =
      broadcast (Printf.sprintf "(declare-const %s %s)\n" n (render s))

    let declare_fun n defs =
      broadcast (Printf.sprintf "(declare-fun %s %s)\n" n (String.concat " " (List.map render defs)))

    let add e =
      broadcast (Printf.sprintf "(assert %s)\n" (render e))

    let push () = broadcast "(push 1)\n"
    let pop  () = broadcast "(pop 1)\n"

    let check_sat_assuming assumptions =
      Mutex.lock sh.mutex;
      sh.current_id <- sh.current_id + 1;
      sh.current_q  <- format_check_sat assumptions;
      sh.result     <- Solver.Unknown;
      Condition.broadcast sh.new_query;
      let deadline = Option.map
        (fun ms -> Unix.gettimeofday () +. float_of_int ms /. 1000.0)
        !timeout
      in
      let before_deadline () = match deadline with
        | None   -> true
        | Some t -> Unix.gettimeofday () < t
      in
      while sh.result = Solver.Unknown && before_deadline () do
        Condition.wait sh.got_result sh.mutex
      done;
      let r = sh.result in
      let solver = sh.result_solver in
      Mutex.unlock sh.mutex;
      Utilities.debug_printf "(%s : %s) " solver (Solver.pp_r r);
      r

    let close () =
      (* We are going to kill things, just ignore this *)
      Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
      Mutex.lock sh.mutex;
      sh.closed <- true;
      Condition.broadcast sh.new_query;
      Mutex.unlock sh.mutex;
      List.iter (fun w ->
        (try Unix.kill w.proc.pid Sys.sigkill with _ -> ());
        (match w.proc.debug_log with Some l -> (try close_out l with _ -> ()) | None -> ())
      ) workers
  end : Solver.Solver)
