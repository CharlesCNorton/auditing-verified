all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d

doc: Makefile.coq
	$(MAKE) -f Makefile.coq html

.PHONY: all clean doc
