
staload "sequent.sats"

primplement lemma_lem {a} () = let 
	prval pf = draxi {mk(a)+nil} {a} ()
	prval pf = drnegr {nil,mk(a)+nil} {a} pf 
	prval pf = drdisjr2 {nil,mk(a)+nil} {a,neg(a)} pf 
	prval pf = drdisjr1 {nil,mk(a \disj neg(a))+nil} {a,neg(a)} pf 
	prval pf = drcr {nil,mk(a \disj neg(a))+nil+mk(a \disj neg(a))} {a \disj neg(a)} pf 
in 
	pf 
end


////
propdef eqiv (p1: prop, p2: prop) = (p1 -> p2, p2 -> P1)
//infix <=> 
stadef == = eqiv

datasort formula = 
| atom of (prop)
| conj of (formula, formula)
| disj of (formula, formula)
| impl of (formula, formula)
| neg  of (formula)

datasort seqs = 
| empty of ()
| more of (formula, seqs)

dataprop seqs_mem (formula, seqs) =
| {g:seqs} {a:formula} mem_base (a, more (a, g)) of ()
| {g:seqs} {a1,a2:formula} mem_ind (a1, more (a2, g)) of mem (a1, g)

dataprop seqs_eq (seqs, seqs) = 
| {g:seqs} seqs_eq (g, g) of ()

praxi lemma_seqs_eq {g1,g2:seqs} ({f:formula} seqs_mem (f, g1) <=> seqs_mem (f, g2)): seqs_eq (g1, g2)


////
dataprop degree (formula, int) = 
| {a:atom}					  dgatom (atom (a), 1) 					 of ()
| {a:formula}     {d:nat}     dgneg  (neg a, d + 1)                  of (degree (a, d))
| {a1,a2:formula} {d1,d2:nat} dgconj (a1 \conj a2, max (d1, d2) + 1) of (degree (a1, d1), degree (a2, d2))
| {a1,a2:formula} {d1,d2:nat} dgdisj (a1 \disj a2, max (d1, d2) + 1) of (degree (a1, d1), degree (a2, d2))
| {a1,a2:formula} {d1,d2:nat} dgimpl (a1 \impl a2, max (d1, d2) + 1) of (degree (a1, d1), degree (a2, d2))

dataprop derive (seqs, seqs) = 
| {a:formula} draxiom (a +> nil, a +> nil) of ()
| {a:formula} {m,n,p,q:seqs} drcut (m ++ p, n ++ q) of (derive (m, a +> n), derive (p <+ a, q))
 
dataprop cutfree_derive (seqs, seqs) = 


