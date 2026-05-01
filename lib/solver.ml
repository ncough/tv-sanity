type result = Sat | Unsat | Unknown

let pp_r = function
  | Sat -> "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"

let and_r a b =
  match a, b with
  | Sat, _ -> Sat
  | _, Sat -> Sat
  | Unsat, Unsat -> Unsat
  | _ -> Unknown

module type Solver = sig
  val name : string
  val set_timeout   : int -> unit
  val set_logic     : string -> unit
  val set_option    : string -> string -> unit
  val declare_const : string -> Sexplib0.Sexp.t -> unit
  val add           : Sexplib0.Sexp.t -> unit
  val push          : unit -> unit
  val pop           : unit -> unit
  val check_sat_assuming : Sexplib0.Sexp.t list -> result
  val close         : unit -> unit
end
