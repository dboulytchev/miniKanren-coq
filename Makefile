COQMODULE    := semantics
COQTHEORIES  := src/*.v

.PHONY: all theories clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	(test -f Makefile.coq && $(MAKE) -f Makefile.coq clean) || true
	rm -f _CoqProject Makefile.coq

tounicode:
	sed -i 's/<</⟪/g' $(COQTHEORIES) 
	sed -i 's/>>/⟫/g' $(COQTHEORIES)
	sed -i 's/;;/⨾/g' $(COQTHEORIES)
	sed -i 's/<|/⦗/g' $(COQTHEORIES)
	sed -i 's/|>/⦘/g' $(COQTHEORIES)

archive: clean
	tar czf ../certified-semantics-src.tgz .
