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


tc: sequent_tc cml_tc



sequent_tc: sequent.dats 
	# $(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -smt2 -in
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | cvc4 --lang smt2

cml_tc: cml.dats
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -smt2 -in

cml2_tc: cml2.dats
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -smt2 -in


list_tc: list.dats 
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -smt2 -in
