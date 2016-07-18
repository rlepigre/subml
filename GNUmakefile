all: subml.byte subml.native

.PHONY: www
www: subml.js clean tutorial.typ subml-latest.tar.gz
	rm -rf www/subml/*
	cp -r lib www/subml/lib
	cp tutorial.typ www/subml
	cd genex && make && ./genex ../lib/all.typ > ../www/examples.html
	cp subml.js www/subml
	cp subml-latest.tar.gz www/docs/

LOGIN:=raffalli
ifeq ($(shell whoami), rodolphe)
	LOGIN:=rlepi
endif

.PHONY: deploy
deploy: www
	ssh $(LOGIN)@lama.univ-savoie.fr rm -rf /home/rlepi/WWW/subml/*
	scp -r www/* $(LOGIN)@lama.univ-savoie.fr:/home/rlepi/WWW/subml

DESTDIR=/usr/local/bin
MLFILES=bindlib/ptmap.ml bindlib/ptmap.mli bindlib/bindlib_util.ml \
	bindlib/bindlib.ml decap/ahash.ml decap/input.ml decap/decap.ml \
	system.ml io.ml timed.ml refinter.ml position.ml ast.ml compare.ml \
  type.ml eval.ml print.ml latex.ml sct.ml raw.ml typing.ml parser.ml \
  proof.ml graph.ml

subml.native: $(MLFILES) subml.ml
	ocamlbuild -cflags -w,-3-30 $@

subml.byte: $(MLFILES) subml.ml
	ocamlbuild -cflags -w,-3-30 $@

submljs.byte: $(MLFILES) submljs.ml
	ocamlbuild -pkgs lwt.syntax,js_of_ocaml,js_of_ocaml.syntax -cflags -syntax,camlp4o,-w,-3-30 -use-ocamlfind $@

subml.js: submljs.byte
	js_of_ocaml --pretty --noinline +weak.js submljs.byte -o subml.js

run: all
	ledit ./subml.native --verbose

validate: clean
	@ wc -L *.ml
	@ echo ""
	@ grep -n -P '\t' *.ml || exit 0

test: all
	./subml.native --quit lib/all.typ
	@ echo -n "Lines with a tabulation in .ml: "
	@ grep -P '\t' *.ml | wc -l
	@ echo -n "Lines with a tabulation in .typ: "
	@ grep -P '\t' lib/*.typ lib/*/*.typ | wc -l
	@ echo -n "Longest line:           "
	@ wc -L *.ml | tail -n 1 | colrm 1 3 | colrm 4 10
	@ echo "(Use \"grep -n -P '\t' *.ml\" to find the tabulations...)"
	@ echo "(Use \"wc -L *.ml\" to find longest line stats on all files...)"

clean:
	ocamlbuild -clean

distclean: clean
	rm -f *~ lib/*~
	rm -rf subml-latest subml-latest.tar.gz
	rm -f subml.js
	rm -f www/examples.html
	cd genex && make distclean

install: all
	install ./subml.native $(DESTDIR)/subml

subml-latest.tar.gz: $(MLFILES)
	rm -rf subml-latest
	mkdir subml-latest
	cp -r decap subml-latest
	cp -r bindlib subml-latest
	pa_ocaml --ascii parser.ml > subml-latest/parser.ml
	cp io.ml timed.ml ast.ml eval.ml print.ml subml-latest
	cp subml.ml latex.ml proof.ml sct.ml raw.ml typing.ml subml-latest
	cp Makefile_minimum subml-latest/Makefile
	cp _tags subml-latest
	rm -f lib/*~
	cp -r lib subml-latest
	cp README subml-latest
	tar zcvf subml-latest.tar.gz subml-latest
	rm -r subml-latest
