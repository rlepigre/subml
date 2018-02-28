LIBDIR=$(shell opam config var share)
BINDIR=$(shell opam config var bin)

VERSION=devel

OBUILD = ocamlbuild -use-ocamlfind -cflags -w,-3-30 -quiet

MLFILES = $(wildcard src/*.ml src/*.mli) src/config.ml

all: _build/src/subml.native

.PHONY: www
www: docs/subml/subml.js tutorial.typ _build/src/subml.docdir/index.html
	@rm -rf docs/subml/*
	@rm -rf docs/ocamldoc/*
	@cp -r lib docs/subml/lib
	@cp -r _build/src/subml.docdir/* docs/ocamldoc
	@cp tutorial.typ docs/subml
	@ocaml genex.ml lib/all.typ > docs/example.html

_build/src/subml.docdir/index.html: src/config.ml
	@echo "[DOC] $@"
	@$(OBUILD) -ocamldoc 'ocamldoc -charset utf8' src/subml.docdir/index.html

_build/src/subml.native: $(MLFILES)
	@echo "[OPT] $@"
	@$(OBUILD) src/subml.native

_build/src/subml.p.native: $(MLFILES)
	@echo "[OPT] $@"
	@$(OBUILD) src/subml.p.native

_build/src/submljs.byte: $(MLFILES)
	@echo "[BYT] $@"
	@$(OBUILD) src/submljs.byte

src/config.ml:
	@echo "[GEN] $@"
	@echo 'let default_path = ["."; "./lib"; "$(LIBDIR)/subml"]' > $@
	@echo 'let version = "$(VERSION)"' >> $@

docs/subml/subml.js: _build/src/submljs.byte
	@echo "[JSO] $@"
	@js_of_ocaml --pretty --noinline +weak.js -o $@ $<

run: all
	ledit ./subml.native --verbose

validate: src/config.ml
	@ wc -L $(MLFILES)
	@ echo ""
	@ grep -n -P '\t' $(MLFILES) || exit 0

test: all
	@ echo normal test
	./subml.native --quit lib/all.typ
	@ echo -n "Lines with a tabulation in .ml : "
	@ grep -P '\t' src/*.ml src/*.mli | wc -l
	@ echo -n "Lines with a tabulation in .typ: "
	@ grep -P '\t' lib/*.typ lib/*/*.typ | wc -l
	@ echo -n "Longest line:           "
	@ wc -L src/*.ml src/*.mli | tail -n 1 | colrm 1 3 | colrm 4 10
	@ echo "(Use \"grep -n -P '\t' src/*.ml src/*.mli\" to find the tabulations...)"
	@ echo "(Use \"wc -L src/*.ml src/*.mli\" to find longest line stats on all files...)"

#### Cleaning targets ########################################################

.PHONY: clean
clean:
	@$(OBUILD) -clean

.PHONY: distclean
distclean: clean
	@rm -f src/config.ml
	@find -type f -name "*~"  -exec rm {} \;
	@find -type f -name "#*#" -exec rm {} \;
	@find -type f -name ".#*" -exec rm {} \;

#### Installation targets ####################################################

.PHONY: uninstall
uninstall:
	rm -f  $(BINDIR)/subml
	rm -rf $(LIBDIR)/subml

.PHONY: install
install: _build/src/subml.native
	install -m 755 -d $(BINDIR)
	install -m 755 -d $(LIBDIR)
	install -m 755 -d $(LIBDIR)/subml
	install -m 755 -d $(LIBDIR)/subml/church
	install -m 755 -d $(LIBDIR)/subml/scott
	install -m 755 -d $(LIBDIR)/subml/munu
	install -m 755 $^ $(BINDIR)/subml
	install -m 644 ./lib/*.typ        $(LIBDIR)/subml
	install -m 644 ./lib/church/*.typ $(LIBDIR)/subml/church
	install -m 644 ./lib/scott/*.typ  $(LIBDIR)/subml/scott
	install -m 644 ./lib/munu/*.typ   $(LIBDIR)/subml/munu
