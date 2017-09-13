include Makefile.config

MLFILES = $(wildcard *.ml *.mli) config.ml

all: subml.byte subml.native

.PHONY: update_docs
update_docs: subml.js tutorial.typ subml-latest.tar.gz
	rm -rf docs/subml/*
	cp -r lib docs/subml/lib
	cp tutorial.typ docs/subml
	cd genex && make && ./genex ../lib/all.typ > ../docs/examples.html
	cp subml.js docs/subml
	cp subml-latest.tar.gz docs/docs/

doc: config.ml
	ocamlbuild -use-ocamlfind -ocamldoc 'ocamldoc -charset utf8' subml.docdir/index.html

subml.native: $(MLFILES) subml.ml
	ocamlbuild -use-ocamlfind -cflags -w,-3-30 $@

subml.p.native: $(MLFILES) subml.ml
	ocamlbuild -use-ocamlfind -cflags -w,-3-30 $@

subml.byte: $(MLFILES) subml.ml
	ocamlbuild -use-ocamlfind -cflags -g,-w,-3-30 $@

config.ml: config.tmpl
	sed -e 's!_PATH_!\"$(LIBDIR)/subml\"!' $< > $@

submljs.byte: $(MLFILES) submljs.ml
	ocamlbuild -cflags -w,-3-30 -use-ocamlfind $@

subml.js: submljs.byte
	js_of_ocaml --pretty --noinline +weak.js submljs.byte -o subml.js

run: all
	ledit ./subml.native --verbose

validate: clean
	@ wc -L *.ml *.mli
	@ echo ""
	@ grep -n -P '\t' *.ml *.mli || exit 0

test: all
	@ echo normal test
	./subml.native --quit lib/all.typ
	@ echo -n "Lines with a tabulation in .ml: "
	@ grep -P '\t' *.ml *.mli | wc -l
	@ echo -n "Lines with a tabulation in .typ: "
	@ grep -P '\t' lib/*.typ lib/*/*.typ | wc -l
	@ echo -n "Longest line:           "
	@ wc -L *.ml *.mli | tail -n 1 | colrm 1 3 | colrm 4 10
	@ echo "(Use \"grep -n -P '\t' *.ml *.mli\" to find the tabulations...)"
	@ echo "(Use \"wc -L *.ml *.mli\" to find longest line stats on all files...)"

clean:
	ocamlbuild -clean

distclean: clean
	rm -f config.ml
	find -type f \( -name "*~" -o -name "#*#" -o -name ".#*" \) -exec rm {} \;
	rm -rf subml-latest subml-latest.tar.gz
	rm -f subml.js
	cd genex && make distclean

install: all
	install ./subml.native $(BINDIR)/subml
	install -d $(LIBDIR)/subml $(LIBDIR)/subml/church $(LIBDIR)/subml/scott $(LIBDIR)/subml/munu
	install ./lib/*.typ	$(LIBDIR)/subml
	install ./lib/church/*.typ	$(LIBDIR)/subml/church
	install ./lib/scott/*.typ	$(LIBDIR)/subml/scott
	install ./lib/munu/*.typ	$(LIBDIR)/subml/munu

subml-latest.tar.gz: $(MLFILES)
	rm -rf subml-latest
	mkdir subml-latest
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
