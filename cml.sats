
#include "./set.sats"
#include "./bag.sats"

(* some custom sta *)
stadef emp = snil 
stadef nil = bnil
stadef disj (a:set, b:set) = a*b==emp
stadef disj (a:set, b:set, c:set) = (a*b==emp)&&(b*c==emp)&&(a*c==emp)
stadef disj (a:bag, b:bag) = a*b==nil 
stadef fulljoin2 (u:set, a:set, b:set) = sub(u,a) && sub(u,b) && (u==a+b) && disj(a,b)
stadef fulljoin3 (u:set, a:set, b:set, c:set) = sub(u,a) && sub(u,b) && sub(u,c) && (u==a+b+c) && disj(a,b,c)
stadef fulljoin = fulljoin2 
stadef fulljoin = fulljoin3 

(* roles *)
sortdef role  = int 
sortdef roles = set

(* formulae *)
datasort form = 
| atom of ()
| conj of (role, form, form)

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
praxi lemma_form_size_conj  {r:role} {p,q:form} (): [size(conj(r,p,q))==size(p)+size(q)+1] unit_p

(* sequent *)
sortdef seqs = bag 
datasort seqt = seqt of (seqs, seqs)
infix |- 
stadef |- = seqt
//

(* CML encoding *)
dataprop CML_INIT (roles, seqs, form) = 
| {p:form|is_atom(p)} cml_init_zero (emp, nil, p) of ()
| {R:roles} {G:seqs} {p:form|is_atom(p)} {R0:roles} {disj(R,R0)&&not(mem(G,mki(R0,p)))} cml_init_more (R+R0, G+mki(R0,p), p) of CML_INIT (R, G, p)

prfun lemma_init_form {U:roles} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mki(R,A))} (CML_INIT (U,G,p)): [A==p] unit_p
prfun lemma_init_form_neg {U:roles} {G:seqs} {p:form} {R:roles} {A:form} {not(A==p)} (CML_INIT (U,G,p)): [not(mem(G,mki(R,A)))] unit_p
prfun lemma_init_role {U:roles} {G:seqs} {p:form} {R1,R2:roles} {mem(G,mki(R1,p))&&mem(G,mki(R2,p))} (CML_INIT (U,G,p)): [disj(R1,R2)] unit_p
prfun lemma_init_role_neg {U:roles} {G:seqs} {p:form} {R:roles} {A:form} {disj(R,U)} (CML_INIT (U,G,p)): [not(mem(G,mki(R,A)))] unit_p
prfun lemma_init_seqs {U1,U2:roles|disj(U1,U2)} {G1,G2:seqs} {p:form} (CML_INIT (U1,G1,p), CML_INIT (U2,G2,p)): [disj(G1,G2)] unit_p

prfun lemma_init_member {U:roles} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} (CML_INIT (U,G,p)): bool (mem(G,mki(R,A)))
prfun lemma_init_remove {U:roles} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form|mem(G,mki(R,A))} (CML_INIT (U,G,p)): CML_INIT (U-R,G-mki(R,A),p)
prfun lemma_init_merge  {U1,U2:roles|disj(U1,U2)} {G1,G2:seqs|disj(G1,G2)} {p:form|is_atom(p)} (CML_INIT (U1,G1,p), CML_INIT (U2,G2,p)): CML_INIT (U1+U2, G1+G2, p)

dataprop CML (roles, int, seqt) = 
(* axiom *)
| {U:roles} {G:seqs} {Gi:seqs|sub(G,Gi)} {p:form|is_atom(p)} 
	cml_axi (U, 0, nil |- G) of CML_INIT (U, Gi, p)

(* logical rules *)
| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form|mem(G,mki(R,conj(r,A,B)))} {M:nat}   cml_conj_n1 
	(U, M+1, nil |- G) of CML (U, M, nil |- G + mki(R,A))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form|mem(G,mki(R,conj(r,A,B)))} {N:nat}   cml_conj_n2 
	(U, N+1, nil |- G) of CML (U, N, nil |- G + mki(R,B))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))}   {A,B:form|mem(G,mki(R,conj(r,A,B)))} {M,N:nat} cml_conj_p 
	(U, M+N+1, nil |- G) of (CML (U, M, nil |- G + mki(R,A)), CML (U, N, nil |- G + mki(R,B)))


//prfun lemma_full {U:roles} {G:seqs} {A:form} (): [M:nat] CML (U, M, nil |- G + mki(U,A)) 
//prfun lemma_empty {U:roles} {G:seqs} {A:form} {M:nat} (CML (U, M, nil |- G + mki(emp,A))): [I:nat|I <= M] CML (U, I, nil |- G)
prfun lemma_wk {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} (CML (U, M, nil |- G)): CML (U, M, nil |- G + mki(R,A))
prfun lemma_ctr {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form|car(G,mki(R,A))>1} {M:nat} (CML (U, M, nil |- G)): CML (U, M, nil |- G - mki(R,A))
//prfun lemma_id {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} (): [M:nat] CML (U, M, nil |- G + mki(R1,A) + mki(R2,A))


prfun lemma_2cut_spill {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(U-R1,U-R2)} {A:form} {M,N:nat} (CML (U, M, nil |- G + mki(R1,A)), CML (U, N, nil |- G + mki(R2,A))): [I:nat] CML (U, I, nil |- G + mki(R1*R2,A))
//prfun lemma_split {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(R1,R2)} {A:form} {M:nat} (CML (U, M, nil |- G + mki(R1+R2,A))): [I:nat] CML (U, I, nil |- G + mki(R1,A) + mki(R2,A))

prfun lemma_2cut {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} {M,N:nat} (CML (U, M, nil |- G + mki(R1,A)), CML (U, N, nil |- G + mki(R2,A))): [I:nat] CML (U, I, nil |- G)

//prfun lemma_2cut {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} {M,N:nat} (CML (U, M, nil |- G + mki(R1,A)), CML (U, N, nil |- G + mki(R2,A))): [I:nat] CML (U, I, nil |- G)
//prfun lemma_3cut {U:roles} {G:seqs} {R1,R2,R3:roles|fulljoin(U,R1,R2,R3)} {A:form} {M,N,L:nat} (CML (U, M, nil |- G + mki(R1,A)), CML (U, N, nil |- G + mki(R2,A)), CML (U, L, nil |- G + mki(R3,A))): [I:nat] CML (U, I, nil |- G)







(* role and roles *)
//sortdef role  = int 
//sortdef roles = bag

//stacst mk_role: role -> elt 
//stadef mk = mk_role

//praxi lemma_mk_role_inj {i:role} (): [mk(i)==mk(i)] unit_p
//praxi lemma_mk_role_bij {i,j:role|not(i==j)} (): [not(mk(i)==mk(j))] unit_p

//(* form and iform *)
//datasort form =
//| atom of ()
//| conj of (role, form, form)

//datasort iform = 
//| iform of (roles, form)

//stadef i = iform

//(* seqs and seqt *)
//datasort seqs = 
//| seqs_nil of ()
//| seqs_cons of (iform, seqs)

//stadef nil = seqs_nil 
//stadef + (s:seqs, p:iform) = seqs_cons (p, s)

//stacst seqs_hd: seqs -> iform 
//stacst seqs_tl: seqs -> seqs 
//stacst seqs_append: (seqs, seqs) -> seqs
//stadef hd = seqs_hd 
//stadef tl = seqs_tl

//praxi lemma_seqs_hd {s:iform} {ss:seqs} (): [hd(ss+s)==s]  unit_p
//praxi lemma_seqs_tl {s:iform} {ss:seqs} (): [tl(ss+s)==ss] unit_p

//datasort seqt = 
//| seqt of (seqs, seqs)

//stadef |- = seqt 
//infix |-


//dataprop CML_INIT (seqs, roles, form) = 
//| {A:form} cml_init_zero (nil, emp, A) of ()
//| {G:seqs} {R:roles} {A:form} {R1:roles|R1*R==emp} cml_init_more (G+i(R1,A), R+R1, A) of (CML_INIT (G, R, A))


//dataprop CML (roles, int, seqt) = 
//(* axiom *)
//| {U:roles} {G:seqs} {p:form} 
//	cml_axi (U, 0, nil |- G) of CML_INIT (G, U, p)

//(* logical rules *)
//| {U:roles} {G:seqs} {r:role} {R:roles|not(mem(R, mk r))} {A,B:form} {m:nat}
//	cml_conj_n1 (U, m+1, nil |- G + i(R,conj(r,A,B))) of CML (U, m, nil |- G + i(R,conj(r,A,B)) + i(R,A))

//| {U:roles} {G:seqs} {r:role} {R:roles|not(mem(R, mk r))} {A,B:form} {m:nat}
//	cml_conj_n2 (U, m+1, nil |- G + i(R,conj(r,A,B))) of CML (U, m, nil |- G + i(R,conj(r,A,B)) + i(R,B))

//| {U:roles} {G:seqs} {r:role} {R:roles|mem(R, mk r)}  {A,B:form} {m,n:nat}
//	cml_conj_p (U, m+n+1, nil |- G + i(R,conj(r,A,B))) of (CML (U, m, nil |- G + i(R,conj(r,A,B)) + i(R,A)), CML (U, n, nil |- G + i(R,conj(r,A,B)) + i(R,B)))


//prfun lemma_31 {U:roles} {G:seqs} {A:form} (): [m:nat] CML (U, m, nil |- G + i(U,A)) 
//prfun lemma_32 {U:roles} {G:seqs} {A:form} {m:nat} (CML (U, m, nil |- G + i(emp,A))): CML (U, m, nil |- G)





(* CML related definition *)













