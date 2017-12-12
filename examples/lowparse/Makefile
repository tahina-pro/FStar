FSTAR_HOME=../..
include ../Makefile.include

include Makefile.include

FST_FILES := $(FSTAR_SOURCE_FILES)

OTHERFLAGS+=$(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN)

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(OTHERFLAGS)

extract-ocaml: $(EXTRACT_OCAML_FILE)
	$(FSTAR_HOME)/bin/fstar.exe $(addprefix -I , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --lax --codegen OCaml $(EXTRACT_OCAML_FILE)

extract-c: $(EXTRACT_C_BASENAME).fst
	$(KREMLIN_HOME)/krml $(addprefix -I , $(INCLUDE_PATHS)) -skip-linking -warn-error +11 -bundle $(EXTRACT_C_BASENAME)=$(EXTRACT_C_BASENAME).*,LowParse.* $(EXTRACT_C_BASENAME).fst

clean:
	rm -f *.c *.h *.o *.ml *.krml
