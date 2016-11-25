include Makefile.config

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

MLFILES=$(wildcard *.ml) config.ml

doc:
	ocamlbuild -use-ocamlfind -ocamldoc 'ocamldoc -charset utf8' subml.docdir/index.html

subml.native: $(MLFILES) subml.ml
	ocamlbuild -use-ocamlfind -cflags -w,-3-30 $@

subml.p.native: $(MLFILES) subml.ml
	ocamlbuild -use-ocamlfind -cflags -w,-3-30 $@

subml.byte: $(MLFILES) subml.ml
	ocamlbuild -use-ocamlfind -cflags -w,-3-30 $@

config.ml: config.tmpl
	sed -e 's!_PATH_!\"$(LIBDIR)\"!' $< > $@

submljs.byte: $(MLFILES) submljs.ml
	ocamlbuild -cflags -w,-3-30 -use-ocamlfind $@

subml.js: submljs.byte
	js_of_ocaml --pretty --noinline +weak.js submljs.byte -o subml.js

run: all
	ledit ./subml.native --verbose

validate: clean
	@ wc -L *.ml
	@ echo ""
	@ grep -n -P '\t' *.ml || exit 0

test: all
	@ echo normal test
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
	rm -f config.ml
	rm -f *~ lib/*~
	rm -rf subml-latest subml-latest.tar.gz
	rm -f subml.js
	rm -f www/examples.html
	cd genex && make distclean

install: all
	install ./subml.native $(BINDIR)/subml
	install -d $(LIBDIR) $(LIBDIR)/church $(LIBDIR)/scott $(LIBDIR)/munu
	install ./lib/*.typ	$(LIBDIR)
	install ./lib/church/*.typ	$(LIBDIR)/church
	install ./lib/scott/*.typ	$(LIBDIR)/scott
	install ./lib/munu/*.typ	$(LIBDIR)/munu

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
