
//#include "sequence.hats"
#include "bag.sats"

(* sort definition *)

datasort form = 
| atom of ()
| bot  of ()
| conj of (form, form)
| disj of (form, form)
| impl of (form, form)
//| neg  of (form)

stadef neg (a:form) = a \impl bot

(* element definition for formula *)

stacst mk_elt: form -> elt 
stadef mk = mk_elt
stadef mks (f:form) = mk(f) + nil

praxi lemma_mk_inj {i,j:form|i==j} (): [mk(i)==mk(i)] unit_p
praxi lemma_mk_bij {i,j:form|not(i==j)} (): [not(mk(i)==mk(j))] unit_p

(* size definition for formula *)

stacst form_sz: form -> int 
stadef size = form_sz 

praxi lemma_form_size_nat {f:form} (): [size f >= 0] unit_p
praxi lemma_form_size_atom (): [size(atom()) == 1] unit_p
praxi lemma_form_size_bot  (): [size(bot()) == 0] unit_p 
praxi lemma_form_size_conj {p,q:form} (): [size(p \conj q) == size(p) + size(q) + 1] unit_p
praxi lemma_form_size_disj {p,q:form} (): [size(p \disj q) == size(p) + size(q) + 1] unit_p
praxi lemma_form_size_impl {p,q:form} (): [size(p \impl q) == size(p) + size(q) + 1] unit_p
//praxi lemma_form_size_neg  {p:form}   (): [size(neg(p)) == size(p) + 1] unit_p


(* rules *)

//dataprop LK (seqt) = 
//(* axiom and cut *)
//| {a:form} lk_axi (mks a |- mks a) of ()
//| {g,d:seqs} {s,p:seqs} {a:form} lk_cut (g+s |- d+p) of (LK (g |- d+mk(a)), LK (mk(a)+s |- p))
//(* structural rules *)
//| {g,d:seqs} {a:form} lk_wl (g+mk(a) |- d) of LK (g |- d)
//| {g,d:seqs} {a:form} lk_wr (g |- mk(a)+d) of LK (g |- d)
//| {g,d:seqs} {a:form|car(g,mk(a))>1} lk_cl ((g \rmv mk(a))+mk(a) |- d) of LK (g |- d)
//| {g,d:seqs} {a:form|car(d,mk(a))>1} lk_cr (g |- (d \rmv mk(a))+mk(a)) of LK (g |- d)
//(* exchange is inexplicit as a property of bag *)
//(* logical rules *)
//| {g,d:seqs} {a,b:form} lk_conjl1 (g+mk(a \conj b) |- d) of LK (g+mk(a) |- d)
//| {g,d:seqs} {a,b:form} lk_conjl2 (g+mk(a \conj b) |- d) of LK (g+mk(b) |- d)
//| {g,d:seqs} {a,b:form} lk_disjr1 (g |- mk(a \disj b)+d) of LK (g |- mk(a)+d)
//| {g,d:seqs} {a,b:form} lk_disjr2 (g |- mk(a \disj b)+d) of LK (g |- mk(b)+d)
//| {g,d:seqs} {s,p:seqs} {a,b:form} lk_disjl (g+s+mk(a \disj b) |- d+p) of (LK (g+mk(a) |- d), LK (s+mk(b) |- p))
//| {g,d:seqs} {s,p:seqs} {a,b:form} lk_conjr (g+s |- mk(a \conj b)+d+p) of (LK (g |- mk(a)+d), LK (s |- mk(b)+p))
//| {g,d:seqs} {s,p:seqs} {a,b:form} lk_impll (g+s+mk(a \impl b) |- d+p) of (LK (g |- mk(a)+d), LK (s+mk(b) |- p))
//| {g,d:seqs} {a,b:form} lk_implr (g |- mk(a \impl b)+d) of LK (g+mk(a) |- mk(b)+d)
//| {g,d:seqs} {a:form} lk_negl (g+mk(neg a) |- d) of LK (g |- mk(a)+d)
//| {g,d:seqs} {a:form} lk_negr (g |- mk(neg a)+d) of LK (g+mk(a) |- d)


dataprop G3 (seqt, int) =
(* axiom *) 
| {g:seqs} {a:form|mem(g,mk(a))}                              g3_axi    (g |- mks a, 0)               of ()
(* bottom *)
| {g:seqs|mem(g,mk(bot))} {c:form}                            g3_botl   (g |- mks c, 0)               of ()
(* conjunction *)
| {g:seqs} {a,b:form} {m,n:nat}                               g3_conjr  (g |- mks (a \conj b), m+n+1) of (G3 (g |- mks a, m), G3 (g |- mks b, n))
| {g:seqs} {a,b:form|mem(g,mk(a \conj b))} {c:form} {n:nat}   g3_conjl1 (g |- mks c, n+1)             of G3 (g+mk(a) |- mks c, n)
| {g:seqs} {a,b:form|mem(g,mk(a \conj b))} {c:form} {n:nat}   g3_conjl2 (g |- mks c, n+1)             of G3 (g+mk(b) |- mks c, n)
(* disjunction *)
| {g:seqs} {a,b:form} {n:nat}                                 g3_disjr1 (g |- mks(a \disj b), n+1)    of G3 (g |- mks a, n)
| {g:seqs} {a,b:form} {n:nat}                                 g3_disjr2 (g |- mks(a \disj b), n+1)    of G3 (g |- mks b, n)
| {g:seqs} {a,b:form|mem(g,mk(a \disj b))} {c:form} {m,n:nat} g3_disjl  (g |- mks c, m+n+1)           of (G3 (g+mk(a) |- mks c, m), G3 (g+mk(b) |- mks c, n))
(* implication *)
| {g:seqs} {a,b:form} {n:nat}                                 g3_implr  (g |- mks (a \impl b), n+1)   of G3 (g+mk(a) |- mks b, n)
| {g:seqs} {a,b:form|mem(g,mk(a \impl b))} {c:form} {m,n:nat} g3_impll  (g |- mks c, m+n+1)           of (G3 (g |- mks a, m), G3 (g+mk(b) |- mks c, n))
//(* negation *)
//| {g:seqs} {a:form} {n:nat}                                   g3_negr   (g |- mks (neg a), n+1)       of G3 (g+mk(a) |- mks bot, n)
//| {g:seqs} {a:form|mem(g,mk(neg a))} {c:form} {n:nat}         g3_negl   (g |- mks c, n+1)             of G3 (g |- mks a, n)

prfun g3_negr {g:seqs} {a:form} {n:nat} (G3 (g+mk(a) |- mks bot, n)): G3 (g |- mks(neg a), n+1)
prfun g3_negl {g:seqs} {a:form|mem(g,mk(neg a))} {n:nat} (G3 (g |- mks a, n)): G3 (g |- mks bot, n+1)

prfun lemma_g3_wk {g:seqs} {c:form} {wk:form} {n:nat} (G3 (g |- mks c, n)): G3 (g+mk(wk) |- mks c, n)
prfun lemma_g3_ctr {g:seqs} {c:form} {ctr:form|car(g,mk(ctr))>1} {n:nat} (G3 (g |- mks c, n)): G3 (g-mk(ctr) |- mks c, n)
prfun lemma_g3_dp {a,b:form} {n:nat} (G3 (nil |- mks (a \disj b), n)): [c:form|(c==a)+(c==b)] G3 (nil |- mks c, n-1)
prfun lemma_g3_cut {g:seqs} {c:form} {cut:form} {m,n:nat} (G3 (g |- mks cut, m), G3 (g+mk(cut) |- mks c, n)): [i:nat] G3 (g |- mks c, i)





