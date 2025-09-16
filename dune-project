(lang dune 3.19)

(name tv-sanity)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name tv-sanity)
 (synopsis "OCaml translation of SMT-LIB2 parser and visualizer")
 (description "A translation of the Python SMT-LIB2 parsing and visualization tool to OCaml")
 (depends 
  ocaml
  dune
  parsexp
  sexplib0)
 (tags
  ("smt" "parsing" "visualization")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
