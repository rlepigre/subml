all: subml.byte subml.native

DESTDIR=/usr/local/bin
MLFILES=bindlib.ml input.ml decap.ml util.ml timed_ref.ml ast.ml eval.ml print.ml latex.ml sct.ml \
	proof_trace.ml raw.ml typing.ml print_trace.ml latex_trace.ml parser.ml subml.ml

parser.ml: parser.dml
	pa_ocaml --ascii --impl parser.dml > parser.ml

subml.native: $(MLFILES)
	ocamlbuild -cflags -w,-30 -use-ocamlfind $@

subml.byte: $(MLFILES)
	ocamlbuild -cflags -w,-30 -use-ocamlfind $@

run: all
	ledit ./subml.native

test: all
	./subml.native --quit lib/all.typ

clean:
	ocamlbuild -clean

distclean: clean
	rm -f *~ lib/*~

install: all
	install ./subml.native $(DESTDIR)/subml
