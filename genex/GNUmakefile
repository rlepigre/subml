all: genex

genex: genex.ml
	ocamlc -pp pa_ocaml -I +decap -o genex unix.cma str.cma decap.cma $<

clean:
	rm -rf genex.cmi genex.cmo

distclean: clean
	rm -rf genex
