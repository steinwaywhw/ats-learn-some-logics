PATSCC=$(PATSHOME)/bin/patscc -DATS_MEMALLOC_LIBC
PATSOPT=$(PATSHOME)/bin/patsopt 
PATSOLVE=$(PATSHOME)/bin/patsolve_smt
RMF=rm -f

# all:: intset

# intset:: intset.dats; $(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i
# intset:: intset.dats; $(PATSCC) --constraint-ignore -o $@ $<
# regress:: intset; ./intset 
# cleanall:: ; $(RMF) intset


# testall:: all
# testall:: regress
# testall:: cleanall

# clean:: ; $(RMF) *~
# clean:: ; $(RMF) *_?ats.c

# cleanall:: clean


tc: sequent cml


cmld: cml_disj.dats
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -t:2000 -smt2 -in 2>&1 | tee output | em -fgreen "^unsat" | em "^sat|^timeout|^unknown" #| grep -B1 "unknown"

sequent: sequent.dats 
	# $(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -smt2 -in
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | cvc4 --lang smt2

cml: cml.dats
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -t:2000 -smt2 -in 2>&1 | tee output | em -fgreen "^unsat" | em "^sat|^timeout|^unknown" #| grep -B1 "unknown"

clml: clml.dats
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -t:2000 -smt2 -in 2>&1 | tee output | em -fgreen "^unsat" | em "^sat|^timeout|^unknown" #| grep -B1 "unknown"

see: output
	cat output | em -fgreen "^unsat" | em "^sat|^unknown"
