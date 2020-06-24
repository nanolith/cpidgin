SOURCES = $(wildcard src/idris/*.idr)
OBJECTS = $(patsubst %.idr,%.ibc,$(SOURCES))

.PHONY: ALL clean

ALL: $(OBJECTS)

%.ibc : %.idr $(SOURCES)
	idris -i src/idris -c --check $<

clean:
	rm -f $(OBJECTS)
