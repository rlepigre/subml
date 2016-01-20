all: subml.byte subml.native

DESTDIR=/usr/local/bin
MLFILES=bindlib/bindlib_util.ml bindlib/bindlib.ml \
        decap/ahash.ml decap/ptmap.ml decap/input.ml decap/decap.ml \
        util.ml io.ml timed_ref.ml ast.ml eval.ml print.ml latex.ml sct.ml \
	proof_trace.ml raw.ml typing.ml print_trace.ml latex_trace.ml parser.ml

parser.ml: parser.dml
	pa_ocaml --ascii --impl parser.dml > parser.ml

subml.native: $(MLFILES) subml.ml
	ocamlbuild -cflags -w,-3-30 -use-ocamlfind $@

subml.byte: $(MLFILES) subml.ml
	ocamlbuild -cflags -w,-3-30 -use-ocamlfind $@

submljs.byte: $(MLFILES) submljs.ml
	ocamlbuild -pkgs lwt.syntax,js_of_ocaml,js_of_ocaml.syntax -cflags -syntax,camlp4o,-w,-3-30 -use-ocamlfind $@

subml.js: submljs.byte
	js_of_ocaml --pretty +weak.js submljs.byte -o subml.js

installjs: subml.js
	cp subml.js ../subml/subml/
	scp subml.js lama.univ-savoie.fr:/home/rlepi/WWW/subml/subml/

rodinstalljs: subml.js
	scp subml.js rlepi@lama.univ-savoie.fr:/home/rlepi/WWW/subml/subml/

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
