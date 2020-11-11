#IDRIS_SOURCES = $(wildcard src/idris/*.idr)
#IDRIS_OBJECTS = $(patsubst %.idr,%.ibc,$(IDRIS_SOURCES))
COQ_SOURCES = $(wildcard src/coq/Control/*.v)
COQ_SOURCES += $(wildcard src/coq/Data/*.v)
COQ_SOURCES += $(wildcard src/coq/App/*.v)
COQ_SOURCES += $(wildcard src/coq/Theorems/*.v)
COQ_SOURCES += $(wildcard src/coq/*.v)
COQ_OBJECTS = $(patsubst %.v,%.vo,$(COQ_SOURCES))
COQ_GLOBS = $(patsubst %.v,%.glob,$(COQ_SOURCES))

.PHONY: ALL clean

ALL: $(IDRIS_OBJECTS) $(COQ_OBJECTS)

%.ibc : %.idr $(IDRIS_SOURCES)
	idris -i src/idris -c --check $<

%.vo : %.v $(COQ_SOURCES)
	coqc -R src/coq CPidgin $<

clean:
	rm -f $(IDRIS_OBJECTS) $(COQ_OBJECTS) $(COQ_GLOBS)

#List depends on Maybe
src/coq/Data/List.vo : src/coq/Data/Maybe.vo
src/coq/Data/List.vo : src/coq/Data/Semigroup.vo

#MList depends on Maybe
src/coq/Data/MList.vo : src/coq/Data/Maybe.vo

#Monoid depends on Semigroup
src/coq/Data/Monoid.vo : src/coq/Data/Semigroup.vo

#Machine depends on Instruction
src/coq/App/Machine.vo : src/coq/App/Instruction.vo
