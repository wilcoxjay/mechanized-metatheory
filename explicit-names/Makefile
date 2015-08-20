COQC ?= coqc

.PHONY: all clean STLC

FILES = SystemF.v

EMPTY = ""

FLAGS = -R ../tactics $(EMPTY) -R ../util $(EMPTY) -R ../explicit-names $(EMPTY)

all: .depend $(FILES:%.v=%.vo) STLC

STLC: 
	make -C STLC

%.vo: %.v
	$(COQC) $(FLAGS) $*.v

clean:
	rm -f *.vo *.glob *.aux .depend *~ *.v.d

.depend: $(FILES)
	coqdep $(FLAGS) $(FILES) > .depend

include .depend
