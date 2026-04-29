type result = Sat | Unsat | Unknown

module type Solver = sig
  type t

  val build         : unit -> t
  val set_timeout   : t -> int -> unit
  val set_logic     : t -> string -> unit
  val set_option    : t -> string -> string -> unit
  val declare_const : t -> string -> Sexplib0.Sexp.t -> unit
  val add           : t -> Sexplib0.Sexp.t -> unit
  val push          : t -> unit
  val pop           : t -> unit
  val check_sat     : t -> result
  val interrupt     : t -> unit
  val close         : t -> unit
end
