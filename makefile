# assumes Coq version 8.16.1 or compatible
#
all: lir.vo dyn.vo precision.vo simprec.vo pallene.vo pall2lir.vo lua.vo example.vo

%.vo: %.v
	coqc -Q . LIR $<


lir.vo: lir.v maps.vo
dyn.vo: dyn.v maps.vo lir.vo
precision.vo: precision.v maps.vo lir.vo dyn.vo
simprec.vo: simprec.v precision.vo maps.vo lir.vo
pallene.vo: pallene.v maps.vo lir.vo
pall2lir.vo: pall2lir.v pallene.vo maps.vo lir.vo
lua.vo: lua.v maps.vo pallene.vo pall2lir.vo lir.vo dyn.vo
example.vo: example.v maps.vo pallene.vo lir.vo

