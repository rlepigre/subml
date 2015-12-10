OCAMLC = ocamlc -I +decap -I +bindlib -I +compiler-libs

all: main

main: util.cmo ast.cmo eval.cmo print.cmo typing.cmo dparser.cmo main.cmo
	$(OCAMLC) -o $@ $(CMA) \
		bindlib.cma unix.cma str.cma ocamlcommon.cma decap.cma decap_ocaml.cma \
		$^

main.cmo: main.ml util.cmo ast.cmo eval.cmo print.cmo typing.cmo dparser.cmo
	$(OCAMLC) -c $<

util.cmo: util.ml
	$(OCAMLC) -c $<

ast.cmo: ast.ml util.cmo
	$(OCAMLC) -c $<

eval.cmo: eval.ml ast.cmo
	$(OCAMLC) -c $<

print.cmi: print.mli ast.cmo
	$(OCAMLC) -c $<

print.cmo: print.ml print.cmi ast.cmo
	$(OCAMLC) -c $<

typing.cmo: typing.ml ast.cmo
	$(OCAMLC) -c $<

dparser.cmo: dparser.ml ast.cmo print.cmo eval.cmo typing.cmo
	$(OCAMLC) -pp pa_ocaml -c $<

run: all
	ledit ./main

test: all
	ledit ./main lib/all.typ

clean:
	rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	rm -f *~ main