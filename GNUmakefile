PREFIX := $(shell opam var prefix)
LIBDIR := $(shell opam var share)
BINDIR := $(shell opam var bin)

VIMDIR   = $(HOME)/.vim
EMACSDIR = $(PREFIX)/share/emacs/site-lisp

all:
	@dune build
.PHONY: all

doc:
	@dune build @doc
.PHONY: doc

GENERATED_TESTS = tests/munu2_generated.typ tests/munu3_generated.typ

tests/munu2_generated.typ: tests/munu.ml
	@ocaml $^ 2 > $@

tests/munu3_generated.typ: tests/munu.ml
	@ocaml $^ 3 > $@

tests: $(GENERATED_TESTS)
	@echo "Running libraries and examples... "
	@dune exec -- subml --quit all_libs.typ > /dev/null
	@echo "Running tests... "
	@dune exec -- subml --quit all_tests.typ > /dev/null
	@echo "All good!"
.PHONY: tests

www: docs/subml.js docs/examples.html doc
	@rm -rf docs/subml/*
	@rm -rf docs/ocamldoc/*
	@cp -r lib docs/subml/lib
	@cp -r _build/default/_doc/_html/* docs/ocamldoc/
	@cp tutorial.typ docs/subml
.PHONY: www

serve: www
	@cd docs && python3 -m http.server
.PHONY: serve

docs/examples.html: gen_list.ml all_libs.typ
	@ocaml $^ > $@

_build/default/src/submljs.bc.js:
	@dune build $@

docs/subml.js: _build/default/src/submljs.bc.js
	@cp $< $@

.PHONY: clean
clean:
	@dune clean

.PHONY: distclean
distclean: clean
	@rm -f $(GENERATED_TESTS)
	@rm -f tests/latex_generation.tex
	@find -type f -name "*~"  -exec rm {} \;
	@find -type f -name "#*#" -exec rm {} \;
	@find -type f -name ".#*" -exec rm {} \;

.PHONY: uninstall
uninstall:
	@dune uninstall
ifneq ($(wildcard $(VIMDIR)/.),)
	rm -rf $(VIMDIR)/syntax/subml.vim
	rm -rf $(VIMDIR)/ftdetect/subml.vim
endif
ifneq ($(wildcard $(EMACSDIR)/.),)
	rm -rf $(EMACSDIR)/subml
endif

.PHONY: install
install:
	@dune install

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
