lir.vo: lir.v

%.vo: %.v
	coqc -Q . LIR $<


lir.vo: maps.vo
biglir.vo: maps.vo lir.vo
dyn.vo: maps.vo lir.vo biglir.vo
pallene.vo: maps.vo lir.vo
lua.vo: maps.vo pallene.vo lir.vo biglir.vo dyn.vo

