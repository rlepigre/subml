all: genex

genex: genex.ml
	ocamlfind ocamlc -pp pa_ocaml -package earley,earley.str -o genex earley.cma unix.cma str.cma earleyStr.cma $<

clean:
	rm -rf genex.cmi genex.cmo

distclean: clean
	rm -rf genex
