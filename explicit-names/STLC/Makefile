COQC ?= coqc

.PHONY: all clean 

FILES = BasicTheorems.v SafetyViaLogicalPredicates.v ContextualEquivalence.v SyntaxAndSemantics.v MultiSubstitutions.v TypeSoundness.v Normalization.v

EMPTY = ""

FLAGS = -R ../../tactics $(EMPTY) -R ../../util $(EMPTY) -R ../../explicit-names $(EMPTY)

all: .depend $(FILES:%.v=%.vo) 

%.vo: %.v
	$(COQC) $(FLAGS) $*.v

clean:
	rm -f *.vo *.glob *.aux .depend *~ *.v.d

.depend: $(FILES)
	coqdep $(FLAGS) $(FILES) > .depend

include .depend
