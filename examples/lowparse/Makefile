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


extract-c: $(EXTRACT_FILES)
	$(KREMLIN_HOME)/krml $(addprefix -I , $(INCLUDE_PATHS)) -skip-compilation -warn-error +11 $(EXTRACT_FILES)
