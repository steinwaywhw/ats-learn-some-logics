

sortdef elt = int

stacst elt_eq: (elt, elt) -> bool 
stadef == = elt_eq 

praxi lemma_eq_elt {e:elt} (): [e == e] unit_p


datasort seq = 
| seq_empty of ()
| seq_more of (elt, seq)

stadef nil = seq_empty
stadef :: = seq_more
//infixr seq_more

stacst seq_head: seq -> elt 
stacst seq_tail: seq -> seq
stacst seq_take: (seq, int) -> seq 
stacst seq_drop: (seq, int) -> seq
stacst seq_length: seq -> int
stacst seq_append: (seq, seq) -> seq
stacst seq_get: (seq, int) -> elt 	
stacst seq_eq: (seq, seq) -> bool
stacst seq_member: (seq, elt) -> bool

stadef head = seq_head
stadef tail = seq_tail
stadef take = seq_take
stadef drop = seq_drop
stadef len = seq_length
stadef append = seq_append
stadef get = seq_get 
stadef ==  = seq_eq
stadef mem = seq_member

praxi lemma_eq_seq_id {g:seq} (): [g == g] unit_p
praxi lemma_eq_seq_sym {g1,g2:seq|g1 == g2} (): [g2 == g1] unit_p
praxi lemma_eq_seq_trans {g1,g2,g3:seq|g1 == g2 && g2 == g3} (): [g1 == g3] unit_p

//praxi lemma_eq_seq_ind {e:elt} {g:seq} (): [(e::g) == (e::g)] unit_p
//praxi lemma_eq_seq_swap {e1,e2:elt} {g:seq} (): [e1::e2::g == e2::e1::g] unit_p
//praxi lemma_eq_seq_def {e:elt} {g1,g2:seq} 

//praxi lemma_head {e:elt} {g:seq} (): [head(e::g) == e] unit_p
//praxi lemma_tail {e:elt} {g:seq} (): [tail(e::g) == g] unit_p

//praxi lemma_length_base (): [len(nil) == 0] unit_p
//praxi lemma_length_ind {e:elt} {g:seq} (): [len(e::g) == len(g) + 1] unit_p
//praxi lemma_length_nat {g:seq} (): [len(g) >= 0] unit_p

//praxi lemma_get_base {e:elt} {g:seq} (): [get(e::g, 0) == e] unit_p
//praxi lemma_get_ind {e:elt} {g:seq} {n:pos} (): [get(e::g, n) == get(g, n-1)] unit_p

//praxi lemma_append_base {g:seq} (): [append(g,nil) == g] unit_p
//praxi lemma_append_ind {e:elt} {g1,g2:seq} (): [append(g1, e::g2) == append(e::g1, g2)] unit_p

praxi lemma_mem_base {e:elt} {g:seq} (): [mem(e::g,e) == true] unit_p
praxi lemma_mem_ind {e1,e2:elt|e1 != e2} {g:seq} (): [mem(e1::g,e2) == mem(g,e2)] unit_p

