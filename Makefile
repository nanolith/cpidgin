SOURCES = $(wildcard src/*.idr)
OBJECTS = $(patsubst %.idr,%.ibc,$(SOURCES))

.PHONY: ALL clean

ALL: $(OBJECTS)

%.ibc : %.idr $(SOURCES)
	idris -i src -c --check $<

clean:
	rm -f $(OBJECTS)
