OCAMLC = ocamlfind ocamlc -package bindlib
OCAMLO = ocamlfind ocamlopt -package bindlib

all: typing.cmo

util.cmo: util.ml
	$(OCAMLC) -c $<

util.cmx: util.ml util.cmo
	$(OCAMLO) -c $<

ast.cmo: ast.ml util.cmo
	$(OCAMLC) -c $<

ast.cmx: ast.ml ast.cmo util.cmx
	$(OCAMLO) -c $<

print.cmo: print.ml ast.cmo
	$(OCAMLC) -c $<

print.cmx: print.ml ast.cmx print.cmo
	$(OCAMLO) -c $<

typing.cmo: typing.ml ast.cmo
	$(OCAMLC) -c $<

typing.cmx: typing.ml ast.cmx typing.cmo
	$(OCAMLO) -c $<

clean:
	rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	rm -f *~
