(lang dune 2.7)

(name "subml")
(authors
  "Rodolphe Lepigre <lepigre@mpi-sws.org>"
  "Christophe Raffalli <christophe@raffalli.eu")
(maintainers
  "Rodolphe Lepigre <lepigre@mpi-sws.org>"
  "Christophe Raffalli <christophe@raffalli.eu")
(source (github rlepigre/subml))
(license "LGPL-3.0")

(generate_opam_files true)

(package
 (name subml)
 (synopsis "SubML prototype language")
 (depends
   (ocaml (>= 4.07.0))
   (earley (= 3.0.0))
   (bindlib (= 5.0.1)))
 (depopts
   (js_of_ocaml (>= 4.0.0))
   (js_of_ocaml-ppx (>= 4.0.0))))
