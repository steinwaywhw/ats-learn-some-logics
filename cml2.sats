
#include "./set.sats"
#include "./list.sats"
infixr (::) ++
infixl (+) + 


(* some custom sta *)
stadef emp = snil 
stadef nil = lnil
stadef fulljoin2 (u:set, a:set, b:set) = sub(u,a) && sub(u,b) && (u==a+b) && (a*b==emp)
stadef fulljoin3 (u:set, a:set, b:set, c:set) = sub(u,a) && sub(u,b) && sub(u,c) && (u==a+b+c) && (a*b==emp) && (a*c==emp) && (b*c==emp)
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

stacst mk_iform: iform -> lelt 
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

praxi lemma_form_size_nat {f:form} (): [size f >= 0] unit_p
praxi lemma_form_size_atom (): [size(atom()) == 1] unit_p
praxi lemma_form_size_conj {p,q:form} {r:role} (): [size(conj(r,p,q)) == size(p) + size(q) + 1] unit_p

(* sequent *)
sortdef seqs = list 
datasort seqt = seqt of (seqs, seqs)
stadef |- = seqt

infix |- 


(* CML encoding *)
dataprop CML_INIT (roles, seqs, form) = 
| {p:form|size(p)==1} cml_init_zero (emp, nil, p) of ()
| {R:roles} {G:seqs} {p:form|size(p)==1} {R1:roles|R1*R==emp} cml_init_more (R+R1, mki(R1,p)++G, p) of (CML_INIT (R, G, p))

dataprop CML (roles, int, seqt) = 
(* axiom *)
| {U:roles} {G,Gi:seqs} {p:form|size(p)==1} 
	cml_axi (U, 0, nil |- G + Gi) 
	of CML_INIT (U, Gi, p)

(* logical rules *)
| {U:roles} {G:seqs} {r:role|mem(U,mk(r))} {R:roles|not(mem(R,mk(r))) && sub(U,R)} {A,B:form} {m:nat} cml_conj_n1 
	(U, m+1, nil |- mki(R,conj(r,A,B)) ++ G) 
	of CML (U, m, nil |- mki(R,A) ++ mki(R,conj(r,A,B)) ++ G)

| {U:roles} {G:seqs} {r:role|mem(U,mk(r))} {R:roles|not(mem(R,mk(r))) && sub(U,R)} {A,B:form} {m:nat} cml_conj_n2 
	(U, m+1, nil |- mki(R,conj(r,A,B)) ++ G) 
	of CML (U, m, nil |- mki(R,B) ++ mki(R,conj(r,A,B)) ++ G)

| {U:roles} {G:seqs} {r:role|mem(U,mk(r))} {R:roles|mem(R,mk(r)) && sub(U,R)} {A,B:form} {m,n:nat} cml_conj_p 
	(U, m+n+1, nil |- mki(R,conj(r,A,B)) ++ G) 
	of (CML (U, m, nil |- mki(R,A) ++ mki(R,conj(r,A,B)) ++ G), CML (U, n, nil |- mki(R,B) ++ mki(R,conj(r,A,B)) ++ G))


prfun lemma_full {U:roles} {G:seqs} {A:form} (): [m:nat] CML (U, m, nil |- mki(U,A) ++ G) 
prfun lemma_empty {U:roles} {G:seqs} {A:form} {m:nat} (CML (U, m, nil |- mki(emp,A) ++ G)): [i:nat|i <= m] CML (U, i, nil |- G)
prfun lemma_wk {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {m:nat} (CML (U, m, nil |- G)): CML (U, m, nil |- mki(R,A) ++ G)
prfun lemma_ctr {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {m:nat} (CML (U, m, nil |- mki(R,A) ++ mki(R,A) ++ G)): CML (U, m, nil |- mki(R,A) ++ G)
prfun lemma_id {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} (): [m:nat] CML (U, m, nil |- mki(R1,A) ++ mki(R2,A) ++ G)


prfun lemma_2cut_spill {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&((U-R1)*(U-R2)==emp)} {A:form} {m,n:nat} (CML (U, m, nil |- mki(R1,A) ++ G), CML (U, n, nil |- mki(R2,A) ++ G)): [i:nat] CML (U, i, nil |- mki(R1*R2,A) ++ G)
prfun lemma_split {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&(R1*R2==emp)} {A:form} {m:nat} (CML (U, m, nil |- mki(R1+R2,A) ++ G)): [i:nat] CML (U, i, nil |- mki(R1,A) ++ mki(R2,A) ++ G)

prfun lemma_2cut {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} {m,n:nat} (CML (U, m, nil |- mki(R1,A) ++ G), CML (U, n, nil |- mki(R2,A) ++ G)): [i:nat] CML (U, i, nil |- G)
prfun lemma_3cut {U:roles} {G:seqs} {R1,R2,R3:roles|fulljoin(U,R1,R2,R3)} {A:form} {m,n,l:nat} (CML (U, m, nil |- mki(R1,A) ++ G), CML (U, n, nil |- mki(R2,A) ++ G), CML (U, l, nil |- mki(R3,A) ++ G)): [i:nat] CML (U, i, nil |- G)







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













