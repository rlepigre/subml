VERSION = devel
PREFIX  = /usr/local
LIBDIR  = $(shell opam config var share)
BINDIR  = $(shell opam config var bin)
OBUILD  = ocamlbuild -use-ocamlfind -cflags -w,-3-30 -quiet

all: depchecks _build/src/subml.native

#### Checking for dependencies ###############################################

# Check for ocamlfind, ocamlbuild and pa_ocaml on the system.
HAS_OCAMLFIND  := $(shell which ocamlfind 2> /dev/null)
HAS_OCAMLBUILD := $(shell which ocamlbuild 2> /dev/null)
HAS_PA_OCAML   := $(shell which pa_ocaml 2> /dev/null)

# Check for the bindlib and earley library.
HAS_BINDLIB    := $(shell ocamlfind query -format %p bindlib 2> /dev/null)
HAS_EARLEY     := $(shell ocamlfind query -format %p earley 2> /dev/null)

.PHONY: depchecks
depchecks:
	@echo "$(LIBDIR) $(BINDIR)"
ifndef HAS_OCAMLBUILD
	$(error "The ocamlbuild program is required...")
endif
ifndef HAS_OCAMLFIND
	$(error "The ocamlfind program is required...")
endif
ifndef HAS_PA_OCAML
	$(error "The pa_ocaml (earley-ocaml) is required...")
endif
ifndef HAS_BINDLIB
	$(error "The bindlib library is required...")
endif
ifndef HAS_EARLEY
	$(error "The earley library is required...")
endif

#### Source files and compilation ############################################

MLFILES = $(wildcard src/*.ml src/*.mli) src/config.ml

src/config.ml:
	@echo "[GEN] $@"
	@echo 'let default_path = ["."; "./lib"; "$(LIBDIR)/subml"]' > $@
	@echo 'let version = "$(VERSION)"' >> $@

_build/src/subml.native: $(MLFILES)
	@echo "[OPT] $@"
	@$(OBUILD) src/subml.native

_build/src/subml.p.native: $(MLFILES)
	@echo "[OPT] $@"
	@$(OBUILD) src/subml.p.native

_build/src/submljs.byte: $(MLFILES)
	@echo "[BYT] $@"
	@$(OBUILD) src/submljs.byte

#### Tests and source code validation ########################################

.PHONY: validate
validate: src/config.ml
	@echo -n "Lines with tabs in .ml : "
	@grep -P '\t' src/*.ml src/*.mli | wc -l
	@echo -n "Lines with tabs in .typ: "
	@grep -P '\t' lib/*.typ lib/*/*.typ | wc -l
	@echo -n "Longest line           : "
	@wc -L src/*.ml src/*.mli | tail -n 1 | colrm 1 4 | colrm 4 10

.PHONY: tests
tests: _build/src/subml.native validate
	@echo "Running tests... "
	@./$< --quit lib/all.typ > /dev/null
	@echo "All tests succeeded!"

#### Documentation and webpage ###############################################

.PHONY: www
www: docs/subml.js _build/src/subml.docdir/index.html
	@rm -rf docs/subml/*
	@rm -rf docs/ocamldoc/*
	@cp -r lib docs/subml/lib
	@cp -r _build/src/subml.docdir/* docs/ocamldoc
	@cp tutorial.typ docs/subml
	@ocaml genex.ml lib/all.typ > docs/example.html

docs/subml.js: _build/src/submljs.byte
	@echo "[JSO] $@"
	@js_of_ocaml --pretty --noinline +weak.js -o $@ $<

_build/src/subml.docdir/index.html: src/config.ml
	@echo "[DOC] $@"
	@$(OBUILD) -ocamldoc 'ocamldoc -charset utf8' src/subml.docdir/index.html

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
