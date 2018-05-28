TARGET=snake.vo
FILESFORDEP=`LC_ALL=C ls *.v`

allok: $(TARGET)

all: $(TARGET) five.vo

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc -w none $<

.PHONY: all

include .depend
