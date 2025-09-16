(** Core data structures for SMT parsing and analysis *)
open Utilities

(** S-expression type alias for clarity *)
type sexp = Sexplib0.Sexp.t

(** Represents a logical predicate with satisfaction status *)
type predicate = {
  term : sexp;
  sat : bool option; (** None = unknown, Some true = sat, Some false = unsat *)
}

(** Represents a declared variable in the SMT-LIB2 file *)
type variable = {
  name : string;
  sort : sexp; (** Keep sorts as S-expressions to handle complex types *)
  undefined : bool;
  value : string option; (** Value from Z3 model if available *)
}

type call_op = {
  vars: StringSet.t;
  name: string;
  args: StringSet.t;
  queries: StringSet.t;
}

(** Represents block operations *)
type operation = 
  | Assume of sexp
  | Call of call_op
  | Assignment of {
      var : string;
      expr : sexp;
    }

(** Represents some global constraint with requirements and ensures *)
type query = {
  qname : string;
  req : predicate list;
  ens : predicate list;
  preds : StringSet.t;
  source_location : string option;
  target_location : string option;
}

(** Represents a basic block in the program *)
type block = {
  preds : string list;
  phis  : (string * sexp) list StringMap.t; (** var -> (block, expr) list *)
  ops   : operation list;
  reachable : bool option; (** From model analysis *)
}

(** Represents the control flow of a program *)
type program = {
  name : string;
  blocks : block StringMap.t;
  entry : string option;
  exit : string option;
  variables : variable StringMap.t;
}

(** Complete state of the SMT problem *)
type state = {
  source : program;
  target : program;
  initial : predicate list;
  effects : query list;
  final : predicate list;
  arbitrary : predicate list;
  funs: (string * sexp list) list;
}

let empty_block = {
  preds = [];
  phis = StringMap.empty;
  ops = [];
  reachable = None;
}

let empty_program name = {
  name;
  blocks = StringMap.empty;
  entry = None;
  exit = None;
  variables = StringMap.empty;
}

let add_block program var preds ops =
  if StringMap.mem var program.blocks then
    failwith (Printf.sprintf "Block already exists: %s" var);
  let block = {empty_block with preds ; ops} in
  { program with blocks = StringMap.add var block program.blocks }

let add_entry program var =
  match program.entry with
  | Some existing -> 
      failwith (Printf.sprintf "Entry already defined: %s, cannot add %s" existing var)
  | None ->
      let program = add_block program var [] [] in
      { program with entry = Some var }

let set_exit program var =
  match program.exit with
  | Some existing -> 
      failwith (Printf.sprintf "Exit already defined: %s, cannot add %s" existing var)
  | None ->
      { program with exit = Some var }

let get_entry program = Option.get program.entry
let get_exit program = Option.get program.exit


(** Add variable to program *)
let add_variable program name sort value =
  if StringMap.mem name program.variables then
    failwith (Printf.sprintf "Variable already exists: %s" name);
  let var = { name; sort; value; undefined = false } in
  { program with variables = StringMap.add name var program.variables }

(** Set variable value from model *)
let set_variable_value program name value =
  match StringMap.find_opt name program.variables with
  | None -> failwith (Printf.sprintf "Cannot set value for undefined variable: %s" name)
  | Some var ->
      let updated_var = { var with value = Some value } in
      { program with variables = StringMap.add name updated_var program.variables }

(** Get variable value *)
let get_variable_value program name =
  match StringMap.find_opt name program.variables with
  | None -> None
  | Some var -> var.value

(** Topological sort of blocks *)
let topo_sort program =
  let entry_block = get_entry program in
  let visited = ref StringSet.empty in
  let order = ref [] in
  let rec dfs block_name =
    if not (StringSet.mem block_name !visited) then begin
      visited := StringSet.add block_name !visited;
      StringMap.iter (fun cand_name block ->
        if List.exists (fun pred_name -> pred_name = block_name) block.preds then
          dfs cand_name
      ) program.blocks;
      order := block_name :: !order
    end
  in
  dfs entry_block;
  StringMap.iter (fun name _ -> dfs name) program.blocks;
  !order

(** Reverse topological sort for backward dataflow analysis *)
let rev_topo_sort program =
  let exit_block = get_exit program in
  let visited = ref StringSet.empty in
  let order = ref [] in
  let rec dfs block_name =
    if not (StringSet.mem block_name !visited) then begin
      visited := StringSet.add block_name !visited;
      let block = StringMap.find block_name program.blocks in
      List.iter dfs block.preds;
      order := block_name :: !order
    end
  in
  dfs exit_block;
  StringMap.iter (fun name _ -> dfs name) program.blocks;
  !order

(** Get program by variable name prefix *)
let get_program_by_name state name =
  if String.starts_with ~prefix:"source__" name then
    state.source
  else if String.starts_with ~prefix:"target__" name then
    state.target
  else
    failwith (Printf.sprintf "Cannot resolve program for variable: %s" name)

(** Convert StringSet to comma-separated string *)
let pp_op = function
  | Assignment { var; expr } -> Printf.sprintf "%s := %s" var (pp_sexp expr)
  | Call { vars; name; args; queries } -> Printf.sprintf "%s := %s(%s) [queries: %s]" (pp_set vars) name (pp_set args) (pp_set queries)
  | Assume expr -> Printf.sprintf "assume %s" (pp_sexp expr)

let op_defs = function
  | Assignment { var ; _ } -> StringSet.singleton var
  | Call { vars ; _ } -> vars
  | _ -> StringSet.empty

let op_fvs = function
  | Assignment { expr ; _ } -> free_vars expr
  | Call { args ; _ } -> args
  | Assume expr -> free_vars expr

let pp_phi var cases =
  Printf.sprintf "%s := phi(%s)" var (String.concat ", " (List.map (fun (block,exp) ->
    Printf.sprintf "%s -> %s" block (pp_sexp exp)) cases))

(** Helper to print an operation *)
let pp_block block =
  let phis = List.map (fun (a,b) -> pp_phi a b) (StringMap.bindings block.phis) in
  String.concat ";\n" (phis @ List.map pp_op block.ops)

let dump_program program =
  List.iter (fun name ->
      let block = StringMap.find name program.blocks in
      Printf.printf "%s:\n%s\n\n" name (pp_block block)
  ) (topo_sort program)


(** Topological sort of queries based on their predecessors *)
let query_topo_sort queries =
  let query_map = List.fold_left (fun acc query ->
    StringMap.add query.qname query acc
  ) StringMap.empty queries in
  let visited = ref StringSet.empty in
  let order = ref [] in
  let rec dfs query_name =
    if not (StringSet.mem query_name !visited) then begin
      visited := StringSet.add query_name !visited;
      StringMap.iter (fun name (query : query) ->
        if StringSet.mem query_name query.preds then
          dfs name
      ) query_map;
      order := query_name :: !order
    end
  in
  dfs "entry";
  (* Start DFS from queries with no unvisited predecessors *)
  List.iter (fun query -> dfs query.qname) queries;
  List.filter_map (fun name -> StringMap.find_opt name query_map) !order

(** Update program with new operations for a block *)
let update_block program block_name fn =
  let fn = function
    | Some v -> Some (fn v) 
    | _ -> failwith ("Unknown block: " ^ block_name)
  in
  { program with blocks = StringMap.update block_name fn program.blocks }
