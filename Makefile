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

distclean: clean
	@rm -f $(GENERATED_TESTS)
	@rm -f tests/latex_generation.tex
.PHONY: distclean

uninstall:
	@dune uninstall
.PHONY: uninstall

install:
	@dune install
.PHONY: install

VIMDIR = $(HOME)/.vim
install_vim: editors/vim/syntax/subml.vim editors/vim/ftdetect/subml.vim
	@install -m 755 -d $(VIMDIR)/syntax
	@install -m 755 -d $(VIMDIR)/ftdetect
	@install -m 644 editors/vim/syntax/subml.vim $(VIMDIR)/syntax
	@install -m 644 editors/vim/ftdetect/subml.vim $(VIMDIR)/ftdetect
	@echo "Vim mode installed to [$(VIMDIR)]."
.PHONY: install_vim

NVIMDIR = $(HOME)/.config/nvim
install_nvim: editors/vim/syntax/subml.vim editors/vim/ftdetect/subml.vim
	@install -m 755 -d $(NVIMDIR)/syntax
	@install -m 755 -d $(NVIMDIR)/ftdetect
	@install -m 644 editors/vim/syntax/subml.vim $(NVIMDIR)/syntax
	@install -m 644 editors/vim/ftdetect/subml.vim $(NVIMDIR)/ftdetect
	@echo "Neovim mode installed to [$(NVIMDIR)]."
.PHONY: install_nvim

EMACSDIR = $(shell opam var prefix)/share/emacs/site-lisp
install_emacs: editors/emacs/subml-mode.el
	@install -m 755 -d $(EMACSDIR)/subml
	@install -m 644 editors/emacs/subml-mode.el $(EMACSDIR)/subml
	@echo "Emacs mode installed ot [$(EMACSDIR)]."
.PHONY: install_emacs

uninstall_editor_modes:
	@rm -f $(VIMDIR)/syntax/subml.vim
	@rm -f $(VIMDIR)/ftdetect/subml.vim
	@rm -f $(NVIMDIR)/syntax/subml.vim
	@rm -f $(NVIMDIR)/ftdetect/subml.vim
	@rm -rf $(EMACSDIR)/subml
.PHONY: uninstall_editor_modes
