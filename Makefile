SHELL=/bin/bash

again: clean all


all:
	cd pcl; make all
	cd doc; make all
	ocamlc -w -8 -o luck -I pcl pcl/pcl.cma str.cma unix.cma misc.ml ast.ml log.ml prs.ml \
        typ.ml gen.ml prj.ml ntr.ml
	./luck bootstrap/ntr.lu

clean:
	rm -f luck *.mli *.o *.cmo *.cmx *.cmi a.out
	cd pcl; make clean
	cd doc; make clean
	for executable in `find testsuite -executable -type f`; do rm "$$executable"; done

luck: clean all
	cd luck_1.0; ../luck charm

test: again
	./luck -test

tdd: again
	./luck testsuite/examples/operators.lu

testsuite: again
	SUCCESS=0; ERROR=0; for filename in `find testsuite -name *.lu -size +0`; do \
		if ./luck $$filename; \
		then let SUCCESS+=1; else let ERROR+=1; fi \
	;done ;echo "SUCCESS: $$SUCCESS ERROR: $$ERROR"
testsuited: again
	SUCCESS=0; ERROR=0; for filename in `find testsuite -name *.lu -size +0`; do \
		if ./luck $$filename; \
		then let SUCCESS+=1; else let ERROR+=1; fi \
	;done ;echo "SUCCESS: $$SUCCESS ERROR: $$ERROR"
