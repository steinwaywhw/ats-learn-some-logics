
#include "./set.sats"
#include "./bag.sats"

(* some custom sta *)
stadef emp = snil 
stadef nil = bnil
stadef disj (a:set, b:set) = a*b==emp
stadef disj (a:set, b:set, c:set) = (a*b==emp)&&(b*c==emp)&&(a*c==emp)
stadef disj (a:bag, b:bag) = a*b==nil 
stadef disj (a:bag, b:bag, c:bag) = (a*b==nil)&&(b*c==nil)&&(a*c==nil)
stadef sub (u:set, a:set, b:set) = sub(u,a) && sub(u,b)
stadef sub (u:set, a:set, b:set, c:set) = sub(u,a) && sub(u,b) && sub(u,c)
stadef disjunion (u:set, a:set, b:set) = sub(u,a,b) && (u==a+b) && disj(a,b)
stadef disjunion (u:set, a:set, b:set, c:set) = sub(u,a,b,c) && (u==a+b+c) && disj(a,b,c)


(* roles *)
sortdef role  = int 
sortdef roles = set

(* formulae *)
datasort form = 
| atom of ()
| mconj of (role, form, form)
| aconj of (role, form, form)
//| bang of (role, form)

datasort iform = iform of (roles, form)

praxi lemma_form_iform {r:roles} {f:form} (): [iform(r,f) == iform(r,f)] unit_p

stacst mk_iform: iform -> belt 
stacst mk_role: role -> selt 
stadef mk = mk_iform
stadef mk = mk_role

stadef mki (R:roles, A:form) = mk(iform(R, A))

praxi lemma_mk_iform_inj {i:iform} (): [mk(i)==mk(i)] unit_p
praxi lemma_mk_iform_bij {i,j:iform|not(i==j)} (): [not(mk(i)==mk(j))] unit_p
praxi lemma_mk_role_inj {i:role} (): [mk(i)==mk(i)] unit_p
praxi lemma_mk_role_bij {i,j:role|not(i==j)} (): [not(mk(i)==mk(j))] unit_p

stacst size_form: form -> int
stadef size = size_form
stadef is_atom (f:form) = size(f)==1

praxi lemma_form_size_nat {f:form} (): [size f >= 0] unit_p
praxi lemma_form_size_atom (): [size(atom)==1] unit_p
praxi lemma_form_size_mconj  {r:role} {p,q:form} (): [size(mconj(r,p,q))==size(p)+size(q)+1] unit_p
praxi lemma_form_size_aconj  {r:role} {p,q:form} (): [size(aconj(r,p,q))==size(p)+size(q)+1] unit_p
//praxi lemma_form_size_bang   {r:role} {p:form} (): [size(bang(r,p))==size(p)+1] unit_p


(* sequent *)
sortdef seqs = bag 
datasort seqt = seqt of (seqs, seqs)
infix |- 
stadef |- = seqt
//

(* CLML encoding *)
dataprop CLML_INIT (roles, seqs, form) = 
| {p:form|is_atom(p)} clml_init_zero (emp, nil, p) of ()
| {R:roles} {G:seqs} {p:form|is_atom(p)} {R0:roles} {disj(R,R0)&&not(mem(G,mki(R0,p)))} clml_init_more (R+R0, G+mki(R0,p), p) of CLML_INIT (R, G, p)

prfun lemma_init_form {U:roles} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mki(R,A))} (CLML_INIT (U,G,p)): [A==p] unit_p
prfun lemma_init_form_neg {U:roles} {G:seqs} {p:form} {R:roles} {A:form} {not(A==p)} (CLML_INIT (U,G,p)): [not(mem(G,mki(R,A)))] unit_p
prfun lemma_init_role {U:roles} {G:seqs} {p:form} {R1,R2:roles} {mem(G,mki(R1,p))&&mem(G,mki(R2,p))} (CLML_INIT (U,G,p)): [disj(R1,R2)] unit_p
prfun lemma_init_role_neg {U:roles} {G:seqs} {p:form} {R:roles} {A:form} {disj(R,U)} (CLML_INIT (U,G,p)): [not(mem(G,mki(R,A)))] unit_p
prfun lemma_init_seqs {U1,U2:roles|disj(U1,U2)} {G1,G2:seqs} {p:form} (CLML_INIT (U1,G1,p), CLML_INIT (U2,G2,p)): [disj(G1,G2)] unit_p

prfun lemma_init_member {U:roles} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} (CLML_INIT (U,G,p)): bool (mem(G,mki(R,A)))
prfun lemma_init_remove {U:roles} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form|mem(G,mki(R,A))} (CLML_INIT (U,G,p)): CLML_INIT (U-R,G-mki(R,A),p)
prfun lemma_init_merge  {U1,U2:roles|disj(U1,U2)} {G1,G2:seqs|disj(G1,G2)} {p:form|is_atom(p)} (CLML_INIT (U1,G1,p), CLML_INIT (U2,G2,p)): CLML_INIT (U1+U2, G1+G2, p)

dataprop CLML (roles, int, seqt) = 
(* axiom *)
| {U:roles} {G:seqs} {Gi:seqs|sub(G,Gi)} {p:form|is_atom(p)} 
	clml_axi (U, 0, nil |- G) of CLML_INIT (U, Gi, p)

(* logical rules *)
| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form} {M:nat} clml_mconj_n
	(U, M+1, nil |- G + mki(R,mconj(r,A,B))) of CLML (U, M, nil |- G + mki(R,A) + mki(R,B))

| {U:roles} {G1,G2:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))} {A,B:form} {M,N:nat} clml_mconj_p 
	(U, M+N+1, nil |- G1 + G2 + mki(R,mconj(r,A,B))) of (CLML (U, M, nil |- G1 + mki(R,A)), CLML (U, N, nil |- G2 + mki(R,B)))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form} {M:nat} clml_aconj_n1 
	(U, M+1, nil |- G + mki(R,aconj(r,A,B))) of CLML (U, M, nil |- G + mki(R,A))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form} {M:nat} clml_aconj_n2 
	(U, M+1, nil |- G + mki(R,aconj(r,A,B))) of CLML (U, M, nil |- G + mki(R,B))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))} {A,B:form} {M,N:nat} clml_aconj_p 
	(U, M+N+1, nil |- G + mki(R,aconj(r,A,B))) of (CLML (U, M, nil |- G + mki(R,A)), CLML (U, N, nil |- G + mki(R,B)))


prfun lemma_full {U:roles} {G:seqs} {A:form} (): [M:nat] CLML (U, M, nil |- G + mki(U,A)) 
prfun lemma_empty {U:roles} {G:seqs} {A:form} {M:nat} (CLML (U, M, nil |- G + mki(emp,A))): [I:nat|I <= M] CLML (U, I, nil |- G)
//prfun lemma_wk {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} (CLML (U, M, nil |- G)): CLML (U, M, nil |- G + mki(R,A))
//prfun lemma_ctr {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mki(R,A))>1} (CLML (U, M, nil |- G)): CLML (U, M, nil |- G - mki(R,A))
//prfun lemma_id {U:roles} {G:seqs} {R1,R2:roles|disjunion(U,R1,R2)} {A:form} (): [M:nat] CLML (U, M, nil |- G + mki(R1,A) + mki(R2,A))


prfun lemma_2cut {U:roles} {G1,G2:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,U-R1,U-R2)} {A:form} {M,N:nat} (CLML (U, M, nil |- G1 + mki(R1,A)), CLML (U, N, nil |- G2 + mki(R2,A))): [I:nat] CLML (U, I, nil |- G1 + G2)
prfun lemma_2cut_spill {U:roles} {G1,G2:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(U-R1,U-R2)} {A:form} {M,N:nat} (CLML (U, M, nil |- G1 + mki(R1,A)), CLML (U, N, nil |- G2 + mki(R2,A))): [I:nat] CLML (U, I, nil |- G1 + G2 + mki(R1*R2,A))

prfun lemma_split {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(R1,R2)} {A:form} {M:nat} (CLML (U, M, nil |- G + mki(R1+R2,A))): [I:nat] CLML (U, I, nil |- G + mki(R1,A) + mki(R2,A))
prfun lemma_3cut {U:roles} {G1,G2,G3:seqs} {R1,R2,R3:roles|sub(U,R1,R2,R3)&&disjunion(U,U-R1,U-R2,U-R3)} {A:form} {M,N,L:nat} (CLML (U, M, nil |- G1 + mki(R1,A)), CLML (U, N, nil |- G2 + mki(R2,A)), CLML (U, L, nil |- G3 + mki(R3,A))): [I:nat] CLML (U, I, nil |- G1 + G2 + G3)










