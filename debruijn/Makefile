COQC ?= coqc

.PHONY: all clean

FILES = STLC.v SystemF.v

EMPTY = ""

FLAGS = -R ../tactics $(EMPTY) -R ../util $(EMPTY) -R ../debruijn $(EMPTY)

all: .depend $(FILES:%.v=%.vo)

%.vo: %.v
	$(COQC) $(FLAGS) $*.v

clean:
	rm -f *.vo *.glob *.aux .depend *~ *.v.d

.depend: $(FILES)
	coqdep $(FLAGS) $(FILES) > .depend

include .depend
