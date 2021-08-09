all: world

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

INCLUDE_PATH = $(FSTAR_HOME)/ulib/experimental

world: verify

FSTAR_OPTIONS = --cache_checked_modules \
		--cmi \
		$(addprefix --include ,$(INCLUDE_PATH)) \
		$(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

ALL_SOURCE_FILES = PointStruct.fst # $(wildcard *.fst *.fsti)

.depend: $(ALL_SOURCE_FILES) Makefile
	$(FSTAR) --dep full $(ALL_SOURCE_FILES) > $@.tmp
	mv $@.tmp $@

depend: .depend

-include .depend

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	echo $*

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PRECIOUS: %.ml
%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PRECIOUS: %.krml
%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

CURATED_KRML_FILES=$(filter-out FStar_NMST.krml Steel_Effect.krml Steel_Effect_Atomic.krml,$(ALL_KRML_FILES))

PointStruct.c: $(CURATED_KRML_FILES)
	krml -skip-makefiles -skip-compilation -bundle PointStruct=Prims,FStar.\*,Steel.\* $^

extract: PointStruct.c

clean:
	-rm -rf *.checked *.krml .depend kremlin.rsp *.tmp *.o compile_flags.txt

.PHONY: all world verify clean depend test extract
