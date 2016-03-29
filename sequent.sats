
(* bag definition for patsolve_smt *)

datasort BagElt = (* *)
sortdef elt = BagElt

stacst eq_elt_elt: (elt, elt) -> bool
stadef == = eq_elt_elt
stadef neq_elt_elt (a:elt, b:elt) = ~(a==b)
stadef != = neq_elt_elt

praxi lemma_elt_eq {e:elt} (): [e == e] unit_p

datasort Bag = (* *)
sortdef bag = Bag 

stacst bag_emp: () -> bag
stacst bag_add: (bag, elt) -> bag
stacst bag_del: (bag, elt) -> bag
stacst bag_rmv: (bag, elt) -> bag
stacst bag_cap: (bag, bag) -> bag 
stacst bag_cup: (bag, bag) -> bag
stacst bag_dif: (bag, bag) -> bag
stacst bag_jon: (bag, bag) -> bag
stacst bag_mem: (bag, elt) -> bool
stacst bag_sub: (bag, bag) -> bool
stacst bag_eq: (bag, bag) -> bool
stacst bag_car: (bag, elt) -> int

stadef nil = bag_emp
stadef add (e:elt, s:bag) = bag_add (s, e)
stadef + = add 
stadef + = bag_add
stadef del = bag_del 
stadef - = del 
stadef rmv = bag_rmv
stadef + = bag_cup
stadef - = bag_dif
stadef * = bag_cap
stadef join = bag_jon
stadef mem = bag_mem
stadef sub = bag_sub
stadef == = bag_eq
stadef bag_neq (a:bag, b:bag) = ~(a==b)
stadef != = bag_neq
stadef car = bag_car

praxi lemma_car_nat {g:bag} {i:elt} (): [car (g, i) >= 0] unit_p

(* sort definition *)

datasort form = 
| atom of (prop)
| conj of (form, form)
| disj of (form, form)
| impl of (form, form)
| neg  of (form)

sortdef seqs = bag 

datasort seqt = 
| seqt of (seqs, seqs)

(* element definition for formula *)

stacst mk_elt: form -> elt 
stadef mk = mk_elt

praxi lemma_elt_fun {i:form} (): [mk(i) == mk(i)] unit_p

(* rules *)

dataprop derive (seqt) = 
(* axiom and cut *)
| {g:seqs} {a:form|mem(g,mk(a))} draxi (seqt (g, mk(a)+nil)) of ()
| {g,d,s,p:seqs} {a:form} drcut (seqt (g+s, d+p)) of (derive (seqt (g, mk(a)+d)), derive (seqt (mk(a)+s, p)))
(* structural rules *)
| {g,d:seqs} {a:form} drwl (seqt (mk(a)+g, d)) of (derive (seqt (g, d)))
| {g,d:seqs} {a:form} drwr (seqt (g, mk(a)+d)) of (derive (seqt (g, d)))
| {g,d:seqs} {a:form|car(g,mk(a))>1} drcl (seqt (mk(a)+rmv(g,mk(a)), d)) of (derive (seqt (g, d)))
| {g,d:seqs} {a:form|car(d,mk(a))>1} drcr (seqt (g, mk(a)+rmv(d,mk(a)))) of (derive (seqt (g, d)))
(* exchange is inexplicit as a property of bag *)
(* logical rules *)
| {g,d:seqs} {a,b:form} drconjl1 (seqt (mk(a \conj b)+g, d)) of (derive (seqt (mk(a)+g, d)))
| {g,d:seqs} {a,b:form} drconjl2 (seqt (mk(a \conj b)+g, d)) of (derive (seqt (mk(b)+g, d)))
| {g,d:seqs} {a,b:form} drdisjr1 (seqt (g, mk(a \disj b)+d)) of (derive (seqt (g, mk(a)+d)))
| {g,d:seqs} {a,b:form} drdisjr2 (seqt (g, mk(a \disj b)+d)) of (derive (seqt (g, mk(b)+d)))
| {g,d,s,p:seqs} {a,b:form} drdisjl (seqt (g+s+mk(a \disj b), d+p)) of (derive (seqt (g+mk(a), d)), derive (seqt (s+mk(b), p)))
| {g,d,s,p:seqs} {a,b:form} drconjr (seqt (g+s, mk(a \conj b)+d+p)) of (derive (seqt (g, mk(a)+d)), derive (seqt (s, mk(b)+p)))
| {g,d,s,p:seqs} {a,b:form} drimpll (seqt (g+s+mk(a \impl b), d+p)) of (derive (seqt (g, mk(a)+d)), derive (seqt (s+mk(b), p)))
| {g,d:seqs} {a,b:form} drimplr (seqt (g, mk(a \impl b)+d)) of (derive (seqt (g+mk(a), mk(b)+d)))
| {g,d:seqs} {a:form} drnegl (seqt (g+mk(neg a), d)) of (derive (seqt (g, mk(a)+d)))
| {g,d:seqs} {a:form} drnegr (seqt (g, mk(neg a)+d)) of (derive (seqt (g+mk(a), d)))


prfun lemma_lem {a:form} (): derive (seqt (nil, mk(a \disj neg(a))+nil))

