SubML (prototype) language
==========================

The SubML language provides polymorphic types and subtyping, but also
existential types, inductive types and coinductive types.


Online interpreter
------------------

The easyest way to try SubML is to use our online interpreter, which
can be found [here](https://rlepigre.github.io/subml/).


Compiling from source
---------------------

If you prefer, you can also compile SubML from source, and run it on
your machine. To do so, you will need a working version of OCaml (at
least 4.07.0) and [opam](https://opam.ocaml.org/doc/Install.html).

You can run the following commands to get the source and install the
dependencies (SubML itself will not be installed).
```bash
git clone git@github.com:rlepigre/subml.git
cd subml
opam install . --deps-only
make
```
You can then run Subml using `dune exec -- subml`. For example, you
can run file `lib/nat.typ` with `dune exec -- subml lib/nat.typ`.

**Note:** you must run the program in the main directory (where the
`lib` directory is accessible).


Documentation
-------------

Useful links:
- File [tutorial.typ](./tutorial.typ) gives an introduction to the
  language and its syntax.
- The [online interpreter](https://rlepigre.github.io/subml/) lets
  you evaluate existing programs, and also write new ones.
- The [documentation](https://rlepigre.github.io/subml/ocamldoc/)
  of the code gives some informations on the implementation.


Editor support
--------------

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
