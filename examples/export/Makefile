FSTAR_HOME=../..
include $(FSTAR_HOME)/src/gmake/fstar.mk

TESTDIRS=$(wildcard *.dir)
TESTS=$(patsubst %.dir,%.test,$(TESTDIRS))

.PHONY: all

all: $(TESTS)

clean:
	rm -f $(TESTS)

%.test:
	cd $(addsuffix .dir,$(basename $@)) && $(FSTAR) test.fst && cd .. && touch $@
