
#include "sequence.hats"

(* sort definition *)

datasort form = 
| atom of ()
| conj of (form, form)
| disj of (form, form)
| impl of (form, form)
| neg  of (form)


(* element definition for formula *)

stacst mk_elt: form -> elt 
stadef mk = mk_elt
stadef mks (f:form) = mk(f) + nil

//stacst eq_form_form: (form, form) -> bool
//stadef == = eq_form_form
//stadef neq_form_form (a:form, b:form) = not (a == b)
//stadef != = neq_form_form


praxi lemma_mk_inj {i,j:form|i==j} (): [mk(i)==mk(i)] unit_p
praxi lemma_mk_bij {i,j:form|not(i==j)} (): [not(mk(i)==mk(j))] unit_p

(* rules *)

dataprop LK (seqt) = 
(* axiom and cut *)
| {a:form} lk_axi (mks a |- mks a) of ()
| {g,d:seqs} {s,p:seqs} {a:form} lk_cut (g+s |- d+p) of (LK (g |- d+mk(a)), LK (mk(a)+s |- p))
(* structural rules *)
| {g,d:seqs} {a:form} lk_wl (g+mk(a) |- d) of LK (g |- d)
| {g,d:seqs} {a:form} lk_wr (g |- mk(a)+d) of LK (g |- d)
| {g,d:seqs} {a:form|car(g,mk(a))>1} lk_cl ((g \rmv mk(a))+mk(a) |- d) of LK (g |- d)
| {g,d:seqs} {a:form|car(d,mk(a))>1} lk_cr (g |- (d \rmv mk(a))+mk(a)) of LK (g |- d)
(* exchange is inexplicit as a property of bag *)
(* logical rules *)
| {g,d:seqs} {a,b:form} lk_conjl1 (g+mk(a \conj b) |- d) of LK (g+mk(a) |- d)
| {g,d:seqs} {a,b:form} lk_conjl2 (g+mk(a \conj b) |- d) of LK (g+mk(b) |- d)
| {g,d:seqs} {a,b:form} lk_disjr1 (g |- mk(a \disj b)+d) of LK (g |- mk(a)+d)
| {g,d:seqs} {a,b:form} lk_disjr2 (g |- mk(a \disj b)+d) of LK (g |- mk(b)+d)
| {g,d:seqs} {s,p:seqs} {a,b:form} lk_disjl (g+s+mk(a \disj b) |- d+p) of (LK (g+mk(a) |- d), LK (s+mk(b) |- p))
| {g,d:seqs} {s,p:seqs} {a,b:form} lk_conjr (g+s |- mk(a \conj b)+d+p) of (LK (g |- mk(a)+d), LK (s |- mk(b)+p))
| {g,d:seqs} {s,p:seqs} {a,b:form} lk_impll (g+s+mk(a \impl b) |- d+p) of (LK (g |- mk(a)+d), LK (s+mk(b) |- p))
| {g,d:seqs} {a,b:form} lk_implr (g |- mk(a \impl b)+d) of LK (g+mk(a) |- mk(b)+d)
| {g,d:seqs} {a:form} lk_negl (g+mk(neg a) |- d) of LK (g |- mk(a)+d)
| {g,d:seqs} {a:form} lk_negr (g |- mk(neg a)+d) of LK (g+mk(a) |- d)

dataprop G3 (seqt) =
(* axiom *) 
| {g:seqs} {a:form|mem(g,mk(a))}            		g3_axi (g |- mks a)            		of ()
(* cut *)
| {g:seqs} {a:form} {c:form} 						g3_cut (g |- mks c)                 of (G3 (g |- mks a), G3 (g+mk(a) |- mks c))
(* conjunction *)
| {g:seqs} {a,b:form} 		   						g3_conjr  (g |- mks (a \conj b))    of (G3 (g |- mks a), G3 (g |- mks b))
| {g:seqs} {a,b:form|mem(g,mk(a \conj b))} {c:form} g3_conjl1 (g |- mks c) 				of G3 (g+mk(a) |- mks c)
| {g:seqs} {a,b:form|mem(g,mk(a \conj b))} {c:form} g3_conjl2 (g |- mks c) 				of G3 (g+mk(b) |- mks c)
(* disjunction *)
| {g:seqs} {a,b:form}          						g3_disjr1 (g |- mks(a \disj b))     of G3 (g |- mks a)
| {g:seqs} {a,b:form}          						g3_disjr2 (g |- mks(a \disj b))     of G3 (g |- mks b)
| {g:seqs} {a,b:form|mem(g,mk(a \disj b))} {c:form} g3_disjl  (g |- mks c) 				of (G3 (g+mk(a) |- mks c), G3 (g+mk(b) |- mks c))
(* implication *)
| {g:seqs} {a,b:form} 		   						g3_implr (g |- mks (a \impl b))     of G3 (g+mk(a) |- mks b)
| {g:seqs} {a,b:form|mem(g,mk(a \impl b))} {c:form} g3_impll (g |- mks c)  				of (G3 (g |- mks a), G3 (g+mk(b) |- mks c))
(* negation *)
| {g:seqs} {a:form}            						g3_negr (g |- mks (neg a))          of G3 (g+mk(a) |- nil)
| {g:seqs} {a:form|mem(g,mk(neg a))} {c:form}       g3_negl (g |- mks c)         		of G3 (g |- mks a)

prfun g3_weakening {g:seqs} {d:seqs|size(d) <= 1} {a:form} (G3 (g |- d)): G3 (g+mk(a) |- d)
prfun g3_contraction {g:seqs} {d:seqs|size(d) <= 1} {a:form|car(g,mk(a))>1} (G3 (g |- d)): G3 (g-mk(a) |- d)
praxi g3_disjunction {a,b:form} (G3 (nil |- mks (a \disj b))): [c:form|c==a||c==b] G3 (nil |- mks c)

prfun lemma_g3_cut {g:seqs} {a:form} {c:form} (G3 (g |- mks a), G3 (g+mk(a) |- mks c)): G3 (g |- mks c)

//praxi lemma_com_disj {g:seqs} {a,b:form} (derive (g |- mks (a \disj b))): derive (g |- mks (b \disj a))
//prfun lemma_lem {a:form} (): derive (nil |- mks (neg(a) \disj a))

//prfun lemma_cut {g,d:seqs} {s,p:seqs} {a:form} (derive (g |- d+mk(a)), derive (mk(a)+s |- p)): derive (g+s |- d+p)

