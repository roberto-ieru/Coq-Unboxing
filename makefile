lir.vo: lir.v

%.vo: %.v
	coqc -Q . LIR $<


biglir.vo: maps.vo lir.vo dyn.vo
dyn.vo: maps.vo lir.vo
lir.vo: maps.vo
lua.vo: maps.vo pallene.vo lir.vo dyn.vo biglir.vo
pallene.vo: maps.vo lir.vo

