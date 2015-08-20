.PHONY: all tactics util explicit-names debruijn

all: tactics util explicit-names debruijn

debruijn:
	make -C debruijn

explicit-names:
	make -C explicit-names

util:
	make -C util

tactics:
	make -C tactics
