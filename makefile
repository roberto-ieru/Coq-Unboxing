lir.vo: lir.v

%.vo: %.v
	coqc -Q . LIR $<


lir.vo: maps.vo
dyn.vo: maps.vo lir.vo
precision.vo: maps.vo lir.vo dyn.vo
pallene.vo: maps.vo lir.vo
lua.vo: maps.vo pallene.vo lir.vo dyn.vo

