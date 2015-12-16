all: main.native main.byte

MLFILES=util.ml ast.ml eval.ml print.ml multi_print.ml latex.ml \
				trace.ml typing.ml dparser.ml main.ml

main.native: $(MLFILES)
	ocamlbuild -use-ocamlfind $@

main.byte: $(MLFILES)
	ocamlbuild -use-ocamlfind $@

run: all
	ledit ./main.native

test: all
	ledit ./main.native lib/all.typ

clean:
	rm -rf _build main.native main.byte

distclean: clean
	rm -f *~ lib/*~
