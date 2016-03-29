staload "sequence.sats"

local 


prval () = $solver_assert (lemma_eq_elt)

prval () = $solver_assert (lemma_eq_seq_id)
prval () = $solver_assert (lemma_eq_seq_sym)
prval () = $solver_assert (lemma_eq_seq_trans)
//val _ = $solver_assert (lemma_eq_seq_ind)
//val _ = $solver_assert (lemma_eq_seq_swap)

//val _ = $solver_assert (lemma_head)
//val _ = $solver_assert (lemma_tail)

//val _ = $solver_assert (lemma_length_base)
//val _ = $solver_assert (lemma_length_ind)
//val _ = $solver_assert (lemma_length_nat)

//val _ = $solver_assert (lemma_get_base)
//val _ = $solver_assert (lemma_get_ind)

//val _ = $solver_assert (lemma_append_base)
//val _ = $solver_assert (lemma_append_ind)

val _ = $solver_assert (lemma_mem_base)
//val _ = $solver_assert (lemma_mem_ind)


abstype seq (seq)

extern fun test1 (): seq (1 :: 2 :: nil)
extern fun test2 (): seq (1 :: 1 :: nil)
extern fun require {g1,g2:seq|mem(g1,1)} (seq g1, seq g2): void 

in 


val a = test1()
val b = test2()
//prval _ = lemma_eq_seq_id {nil} ()
//prval _ = lemma_length_base ()
//prval _ = lemma_length_ind {2} {nil} ()
//prval _ = lemma_length_ind {1} {2::nil} ()
val _ = require (a, b)

end
