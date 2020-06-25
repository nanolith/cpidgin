IDRIS_SOURCES = $(wildcard src/idris/*.idr)
IDRIS_OBJECTS = $(patsubst %.idr,%.ibc,$(IDRIS_SOURCES))
COQ_SOURCES = $(wildcard src/coq/Control/*.v)
COQ_SOURCES += $(wildcard src/coq/Data/*.v)
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
