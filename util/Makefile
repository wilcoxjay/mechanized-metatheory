COQC ?= coqc

.PHONY: all clean

FILES = EQ.v ANY.v MAP.v Alist.v EqMapFacts.v

EMPTY = ""

FLAGS = -R ../tactics $(EMPTY) -R ../util $(EMPTY)

all: $(FILES:%.v=%.vo)

%.vo: %.v
	$(COQC) $(FLAGS) $*.v

clean:
	rm -f *.vo *.glob *.aux .depend *~ *.v.d

.depend: $(FILES)
	coqdep $(FLAGS) $(FILES) > .depend

include .depend
