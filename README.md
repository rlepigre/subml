[![Build Status](https://travis-ci.org/rlepigre/subml.svg?branch=master)](https://travis-ci.org/rlepigre/subml)

### Dependencies

To install `subml`, you will need `OCaml >= 4.03` with:
 - `ocamlbuild` (build)
 - `ocamlfind` (build)
 - `earley` (https://github.com/rlepigre/ocaml-earley)
 - `bindlib` (version 5.0.1, https://github.com/rlepigre/ocaml-bindlib)
 - `GNU make` and other standard utilities

Obtaining the dependencies with `opam`:

```bash
opam switch 4.06 # or whatever version >= 4.03
opam install ocamlbuild ocamlfind bindlib.5.0.1 earley.2.0.0
```

Compilation:

```bash
make
make install # optional
```

### Running the program

Run the command `subml` (or `./subml.native` if you did not install)
Type `subml lib/nat.typ` to load the file `lib/nat.typ`.

**Note:** you must run the program in the main directory (where the `lib`
directory is accessible) if you did not install `subml`.

### Documentation

 - See file `tutorial.typ` for in introduction to the language and its syntax
 - Online interpreter: https://rlepigre.github.io/subml/
 - OCamlDoc: https://rlepigre.github.io/subml/ocamldoc/

### Editor support

#### Vim (or Neovim)

Just use the `install_vim` target.

```bash
make install_vim
```

**Note:** the syntax coloring and automatic format detection for `.typ` files
is user-specific by default. Files are installed under `$HOME/.vim` in the
standard way.

#### Emacs

Just use the `install_emacs` target.

```bash
make install_emacs
```

**Note:** the mode is installed under the standard `share/emacs/site-lisp`
folder, according the the `$PREFIX`.
