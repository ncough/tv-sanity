type process = {
  stdin:     out_channel;
  stdout:    in_channel;
  stderr:    in_channel;
  debug_log: out_channel option;
}

let launch name argv =
  let cmd = String.concat " " argv in
  let name = "incr_" ^ name ^ "_debug.smt2" in
  let debug_log = Option.map open_out (Utilities.get_debug_file_path name) in
  let (stdout, stdin, stderr) = Unix.open_process_full cmd (Unix.environment ()) in
  { stdin; stdout; stderr; debug_log }

let make (timeout_option, argv) : (module Solver.Solver) =
  let name = List.nth argv 0 in
  let p = launch name argv in
  let send_str s =
    (match p.debug_log with Some l -> output_string l s; flush l | None -> ());
    output_string p.stdin s;
    flush p.stdin
  in
  let recv () = String.trim (input_line p.stdout) in
  let render = Smtlib_output.sexp_to_smtlib in
  let parse_result = function
    | "sat"   -> Solver.Sat
    | "unsat" -> Solver.Unsat
    | _       -> Solver.Unknown
  in
  (module struct
    let name = name

    let set_timeout ms =
      send_str (Printf.sprintf "(set-option :%s %d)\n" timeout_option ms)

    let set_logic l =
      send_str (Printf.sprintf "(set-logic %s)\n" l)

    let set_option k v =
      send_str (Printf.sprintf "(set-option %s %s)\n" k v)

    let declare_const n s =
      send_str (Printf.sprintf "(declare-const %s %s)\n" n (render s))

    let add e =
      send_str (Printf.sprintf "(assert %s)\n" (render e))

    let push () = send_str "(push 1)\n"
    let pop  () = send_str "(pop 1)\n"

    let check_sat_assuming assumptions =
      (match assumptions with
       | [] ->
         send_str "(check-sat)\n"
       | _  ->
         let lits = String.concat " " (List.map render assumptions) in
         send_str (Printf.sprintf "(check-sat-assuming (%s))\n" lits));
      parse_result (recv ())

    let close () =
      (match p.debug_log with Some l -> close_out l | None -> ());
      close_out p.stdin;
      ignore (Unix.close_process_full (p.stdout, p.stdin, p.stderr))
  end : Solver.Solver)
