FSTAR_HOME=../..
include ../Makefile.include

FST_FILES :=	\
	LowParse.Slice.fst \
	LowParse.Base.fst \
	LowParse.Int.fst \
	LowParse.VLBytes.fst \
	LowParse.Enum.fst \
	LowParse.Sum.fst \
	LowParse.List.fst \
	LowParse.fst \
	LowParse.Examples.fst \
	LowParse.Examples.Extract.fst \


EXTRACT_FILES := \
	LowParse.Examples.Extract.fst \


INCLUDE_PATHS:=

ifeq ($(KREMLIN_HOME),)
  INCLUDE_KREMLIN=
else
  INCLUDE_KREMLIN=--include $(KREMLIN_HOME)/kremlib
endif

OTHERFLAGS+=$(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --z3rlimit_factor 4

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(OTHERFLAGS)

extract-ocaml: $(EXTRACT_FILES)
	$(FSTAR_HOME)/bin/fstar.exe $(addprefix -I , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --lax --codegen OCaml $(EXTRACT_FILES)

extract-c: $(EXTRACT_FILES)
	$(KREMLIN_HOME)/krml $(addprefix -I , $(INCLUDE_PATHS)) -skip-linking -warn-error +11 $(patsubst %.fst,-bundle %=LowParse.*,$(EXTRACT_FILES)) $(EXTRACT_FILES)

clean:
	rm -f *.c *.h *.o *.ml *.krml
