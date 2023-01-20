lir.vo: lir.v

%.vo: %.v
	coqc -Q . LIR $<


lir.vo: lir.v maps.vo
dyn.vo: dyn.v maps.vo lir.vo
precision.vo: precision.v maps.vo lir.vo dyn.vo
simprec.vo: simprec.v precision.vo maps.vo lir.vo
pallene.vo: pallene.v maps.vo lir.vo
pall2lir.vo: pall2lir.v pallene.vo maps.vo lir.vo
lua.vo: lua.v maps.vo pallene.vo pall2lir.vo lir.vo dyn.vo

