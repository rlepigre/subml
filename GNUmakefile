all: subml.byte subml.native

DESTDIR=/usr/local/bin
MLFILES=util.ml timed_ref.ml ast.ml eval.ml print.ml multi_print.ml latex.ml sct.ml \
	proof_trace.ml raw.ml typing.ml print_trace.ml latex_trace.ml dparser.ml subml.ml

subml.native: $(MLFILES)
	ocamlbuild -cflags -w,-30 -use-ocamlfind $@

subml.byte: $(MLFILES)
	ocamlbuild -cflags -w,-30 -use-ocamlfind $@

run: all
	ledit ./subml.native

test: all
	ledit ./subml.native lib/all.typ

clean:
	ocamlbuild -clean

distclean: clean
	rm -f *~ lib/*~

install: all
	install ./subml.native $(DESTDIR)/subml
