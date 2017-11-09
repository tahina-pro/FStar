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


EXTRACT_FILES := \
	LowParse.Examples.fst \


FSTAR_INCLUDE_PATHS:=--include $(KREMLIN_HOME)/kremlib

OTHERFLAGS+=$(FSTAR_INCLUDE_PATHS) --z3rlimit_factor 4

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(OTHERFLAGS)


extract-c: $(EXTRACT_FILES)
	krml -skip-compilation -warn-error +11 $(EXTRACT_FILES)
