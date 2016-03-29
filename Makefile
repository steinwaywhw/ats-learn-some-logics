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


tc: sequent_tc

sequence_tc: sequence.dats
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i


sequent_tc: sequent.dats 
	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./constraints | z3 -smt2 -in
