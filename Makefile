TARGET=snake.vo four.vo five.vo
FILESFORDEP=`LC_ALL=C ls *.v`

allok: $(TARGET)

all: $(TARGET)

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

AbGroup.vo: AbGroup.v
	coqc -w none $<

.PHONY: all allok clean depend

include .depend
