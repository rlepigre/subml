HAS_OPAM := $(shell which opam 2> /dev/null)

ifdef HAS_OPAM
PREFIX := $(shell opam config var prefix)
LIBDIR := $(shell opam config var share)
BINDIR := $(shell opam config var bin)
else
PREFIX := /usr/local
LIBDIR := $(PREFIX)/lib
BINDIR : = $(PREFIX)/bin
endif

VERSION  = devel
VIMDIR   = $(HOME)/.vim
EMACSDIR = $(PREFIX)/share/emacs/site-lisp

OBUILD   = ocamlbuild -use-ocamlfind -quiet

#### Main target #############################################################

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

GENERATED_TESTS = tests/munu2.typ tests/munu3.typ

tests/munu2.typ: tests/munu.ml
	@ocaml $^ 2 > $@

tests/munu3.typ: tests/munu.ml
	@ocaml $^ 3 > $@

.PHONY: tests
tests: _build/src/subml.native $(GENERATED_TESTS) validate
	@echo "Running libraries and examples... "
	@./$< --quit all_libs.typ > /dev/null
	@echo "Running tests... "
	@./$< --quit all_tests.typ > /dev/null
	@echo "All good!"

#### Documentation and webpage ###############################################

.PHONY: www
www: docs/subml.js docs/examples.html _build/src/subml.docdir/index.html
	@rm -rf docs/subml/*
	@rm -rf docs/ocamldoc/*
	@cp -r lib docs/subml/lib
	@cp -r _build/src/subml.docdir/* docs/ocamldoc
	@cp tutorial.typ docs/subml

docs/examples.html: all_libs.typ genex.ml
	@ocaml genex.ml $< > $@

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
	@rm -f $(GENERATED_TESTS)
	@find -type f -name "*~"  -exec rm {} \;
	@find -type f -name "#*#" -exec rm {} \;
	@find -type f -name ".#*" -exec rm {} \;

#### Installation targets ####################################################

.PHONY: uninstall
uninstall:
	rm -f  $(BINDIR)/subml
	rm -rf $(LIBDIR)/subml
ifneq ($(wildcard $(VIMDIR)/.),)
	rm -rf $(VIMDIR)/syntax/subml.vim
	rm -rf $(VIMDIR)/ftdetect/subml.vim
endif
ifneq ($(wildcard $(EMACSDIR)/.),)
	rm -rf $(EMACSDIR)/subml
endif

.PHONY: install
install: _build/src/subml.native
	install -m 755 -d $(BINDIR)
	install -m 755 -d $(LIBDIR)
	install -m 755 -d $(LIBDIR)/subml
	install -m 755 -d $(LIBDIR)/subml/church
	install -m 755 -d $(LIBDIR)/subml/scott
	install -m 755 $< $(BINDIR)/subml
	install -m 644 ./lib/*.typ        $(LIBDIR)/subml
	install -m 644 ./lib/church/*.typ $(LIBDIR)/subml/church
	install -m 644 ./lib/scott/*.typ  $(LIBDIR)/subml/scott

.PHONY: install_vim
install_vim: editors/vim/syntax/subml.vim editors/vim/ftdetect/subml.vim
ifneq ($(wildcard $(VIMDIR)/.),)
	install -m 755 -d $(VIMDIR)/syntax
	install -m 755 -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/subml.vim $(VIMDIR)/syntax
	install -m 644 editors/vim/ftdetect/subml.vim $(VIMDIR)/ftdetect
	@echo -e "\e[36mVim mode installed.\e[39m"
else
	@echo -e "\e[36mWill not install vim mode.\e[39m"
endif

.PHONY: install_emacs
install_emacs: editors/emacs/subml-mode.el
ifneq ($(wildcard $(EMACSDIR)/.),)
	install -m 755 -d $(EMACSDIR)/subml
	install -m 644 editors/emacs/subml-mode.el $(EMACSDIR)/subml
	@echo -e "\e[36mEmacs mode installed.\e[39m"
else
	@echo -e "\e[36mWill not install emacs mode.\e[39m"
endif



