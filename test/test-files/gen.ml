let generate_rules base =
  Printf.printf
    {|
        (rule
         (alias runtest)
         (action (run tv-sanity ../%s.smt2)))
     |}
    base

let () =
  Sys.readdir ".."
  |> Array.to_list
  |> List.sort String.compare
  |> List.filter_map (Filename.chop_suffix_opt ~suffix:".smt2")
  |> List.iter generate_rules
