
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
| conn of (role, form, form)

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
praxi lemma_form_size_conn  {r:role} {p,q:form} (): [size(conn(r,p,q))==size(p)+size(q)+1] unit_p

(* sequent *)
sortdef seqs = bag 
datasort seqt = seqt of (seqs, seqs)
infix |- 
stadef |- = seqt
//

(* CML encoding *)
dataprop CMLD_INIT (roles, roles, seqs, form) = 
| {U:roles} {p:form|is_atom(p)} cmld_init_zero (U, emp, nil, p) of ()
| {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R0:roles|sub(U,R0)} {disj(U0,U-R0)&&not(mem(G,mki(R0,p)))} cmld_init_more (U, U0+(U-R0), G+mki(R0,p), p) of CMLD_INIT (U, U0, G, p)

praxi lemma_init_form {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mki(R,A))} (CMLD_INIT (U,U0,G,p)): [A==p] unit_p
praxi lemma_init_form_neg {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {not(A==p)} (CMLD_INIT (U,U0,G,p)): [not(mem(G,mki(R,A)))] unit_p
praxi lemma_init_role {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R1,R2:roles} {mem(G,mki(R1,p))&&mem(G,mki(R2,p))} (CMLD_INIT (U,U0,G,p)): [disj(U-R1,U-R2)] unit_p
praxi lemma_init_role_neg {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {disj(U0,U-R)} (CMLD_INIT (U,U0,G,p)): [not(mem(G,mki(R,A)))] unit_p
praxi lemma_init_seqs {U:roles} {U1,U2:roles|sub(U,U1,U2)&&disj(U1,U2)} {G1,G2:seqs} {p:form} (CMLD_INIT (U,U1,G1,p), CMLD_INIT (U,U2,G2,p)): [disj(G1,G2)] unit_p

prfun lemma_init_member {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} (CMLD_INIT (U,U0,G,p)): bool (mem(G,mki(R,A)))
prfun lemma_init_remove {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} {mem(G,mki(R,A))} (CMLD_INIT (U,U0,G,p)): CMLD_INIT (U,U0-(U-R),G-mki(R,A),p)
prfun lemma_init_merge  {U:roles} {U1,U2:roles|sub(U,U1,U2)&&disj(U1,U2)} {G1,G2:seqs|disj(G1,G2)} {p:form|is_atom(p)} (CMLD_INIT (U,U1,G1,p), CMLD_INIT (U,U2,G2,p)): CMLD_INIT (U,U1+U2,G1+G2,p)

dataprop CMLD (roles, int, seqt) = 
(* axiom *)
| {U:roles} {G:seqs} {Gi:seqs|sub(G,Gi)} {p:form|is_atom(p)} 
	cmld_axi (U, 0, nil |- G) of CMLD_INIT (U, U, Gi, p)

(* logical rules *)
| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))} {A,B:form|mem(G,mki(R,conn(r,A,B)))} {M:nat}   cmld_conn_p1 
	(U, M+1, nil |- G) of CMLD (U, M, nil |- G + mki(R,A))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))} {A,B:form|mem(G,mki(R,conn(r,A,B)))} {N:nat}   cmld_conn_p2 
	(U, N+1, nil |- G) of CMLD (U, N, nil |- G + mki(R,B))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))}   {A,B:form|mem(G,mki(R,conn(r,A,B)))} {M,N:nat} cmld_conn_n 
	(U, M+N+1, nil |- G) of (CMLD (U, M, nil |- G + mki(R,A)), CMLD (U, N, nil |- G + mki(R,B)))


prfun lemma_empty {U:roles} {G:seqs} {A:form} (): [M:nat] CMLD (U, M, nil |- G + mki(emp,A)) 
prfun lemma_full {U:roles} {G:seqs} {A:form} {M:nat} (CMLD (U, M, nil |- G + mki(U,A))): [I:nat|I <= M] CMLD (U, I, nil |- G)
prfun lemma_wk {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} (CMLD (U, M, nil |- G)): CMLD (U, M, nil |- G + mki(R,A))
prfun lemma_ctr {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mki(R,A))>1} (CMLD (U, M, nil |- G)): CMLD (U, M, nil |- G - mki(R,A))
prfun lemma_id {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,U-R1,U-R2)} {A:form} (): [M:nat] CMLD (U, M, nil |- G + mki(R1,A) + mki(R2,A))


prfun lemma_2cut_spill {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(R1,R2)} {A:form} {M,N:nat} (CMLD (U, M, nil |- G + mki(R1,A)), CMLD (U, N, nil |- G + mki(R2,A))): [I:nat] CMLD (U, I, nil |- G + mki(R1+R2,A))
prfun lemma_split {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(U-R1,U-R2)} {A:form} {M:nat} (CMLD (U, M, nil |- G + mki(R1*R2,A))): [I:nat] CMLD (U, I, nil |- G + mki(R1,A) + mki(R2,A))

prfun lemma_2cut {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,R1,R2)} {A:form} {M,N:nat} (CMLD (U, M, nil |- G + mki(R1,A)), CMLD (U, N, nil |- G + mki(R2,A))): [I:nat] CMLD (U, I, nil |- G)
prfun lemma_3cut {U:roles} {G:seqs} {R1,R2,R3:roles|sub(U,R1,R2,R3)&&disjunion(U,R1,R2,R3)} {A:form} {M,N,L:nat} (CMLD (U, M, nil |- G + mki(R1,A)), CMLD (U, N, nil |- G + mki(R2,A)), CMLD (U, L, nil |- G + mki(R3,A))): [I:nat] CMLD (U, I, nil |- G)










