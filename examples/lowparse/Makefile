FSTAR_HOME=../..
include ../Makefile.include

include Makefile.include

FST_FILES := $(FSTAR_SOURCE_FILES)

OTHERFLAGS+=$(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --z3rlimit_factor 4

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(OTHERFLAGS)

extract-ocaml: $(EXTRACT_FILES)
	$(FSTAR_HOME)/bin/fstar.exe $(addprefix -I , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --lax --codegen OCaml $(EXTRACT_FILES)

extract-c: $(EXTRACT_C_FILE)
	$(KREMLIN_HOME)/krml $(addprefix -I , $(INCLUDE_PATHS)) -skip-linking -warn-error +11 -bundle $(patsubst %.fst,%,$(EXTRACT_C_FILE))=LowParseExamples,LowParse.* $(EXTRACT_C_FILE)

clean:
	rm -f *.c *.h *.o *.ml *.krml
