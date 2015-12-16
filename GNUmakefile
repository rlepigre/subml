OCAMLC = ocamlc -I +decap -I +bindlib -I +compiler-libs

all: main

main: util.cmo ast.cmo eval.cmo print.cmo latex.cmo multi_print.cmo trace.cmo typing.cmo dparser.cmo main.cmo
	$(OCAMLC) -o $@ $(CMA) \
		bindlib.cma unix.cma str.cma ocamlcommon.cma decap.cma decap_ocaml.cma \
		$^

main.cmo: main.ml util.cmo ast.cmo eval.cmo multi_print.cmo typing.cmo dparser.cmo
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

latex.cmi: latex.mli ast.cmo
	$(OCAMLC) -c $<

latex.cmo: latex.ml latex.cmi print.cmo ast.cmo
	$(OCAMLC) -c $<

multi_print.cmi: multi_print.mli ast.cmo
	$(OCAMLC) -c $<

multi_print.cmo: multi_print.ml multi_print.cmi latex.cmo print.cmo ast.cmo
	$(OCAMLC) -c $<

trace.cmo: trace.ml ast.cmo
	$(OCAMLC) -c $<

typing.cmo: typing.ml ast.cmo trace.cmo
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
	rm -f *~ lib/*~ main
