
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
| neg  of (form)

datasort iform = 
| iformc of (roles, form)
| iformd of (roles, form)

//praxi lemma_form_iform {r:roles} {f:form} (): [iform(r,f) == iform(r,f)] unit_p

stacst mk_iform: iform -> belt 
stacst mk_role: role -> selt 
stadef mk = mk_iform
stadef mk = mk_role

stadef mkic (R:roles, A:form) = mk(iformc(R, A))
stadef mkid (R:roles, A:form) = mk(iformd(R, A))

praxi lemma_mk_iform_inj {i:iform} (): [mk(i)==mk(i)] unit_p
praxi lemma_mk_iform_bij {i,j:iform|not(i==j)} (): [not(mk(i)==mk(j))] unit_p
praxi lemma_mk_role_inj {i:role} (): [mk(i)==mk(i)] unit_p
praxi lemma_mk_role_bij {i,j:role|not(i==j)} (): [not(mk(i)==mk(j))] unit_p

stacst size_form: form -> int
stadef size = size_form
stadef is_atom (f:form) = size(f)==1

praxi lemma_form_size_nat {f:form} (): [size f >= 0] unit_p
praxi lemma_form_size_atom (): [size(atom)==1] unit_p
praxi lemma_form_size_conn {r:role} {p,q:form} (): [size(conn(r,p,q))==size(p)+size(q)+1] unit_p
praxi lemma_form_size_neg  {p:form} (): [size(neg p)==size(p)+1] unit_p

(* sequent *)
sortdef seqs = bag 
datasort seqt = seqt of (seqs, seqs)
infix |- 
stadef |- = seqt


(* DCML init related *)
dataprop DCMLC_INIT (roles, roles, seqs, form) = 
| {U:roles} {p:form|is_atom(p)} 
  dcmlc_init_zero (U, emp, nil, p) of ()
| {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R0:roles|sub(U,R0)} {disj(U0,R0)&&not(mem(G,mkic(R0,p)))} 
  dcmlc_init_more (U, U0+R0, G+mkic(R0,p), p) of DCMLC_INIT (U, U0, G, p)

dataprop DCMLD_INIT (roles, roles, seqs, form) = 
| {U:roles} {p:form|is_atom(p)} 
  dcmld_init_zero (U, emp, nil, p) of ()
| {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R0:roles|sub(U,R0)} {disj(U0,U-R0)&&not(mem(G,mkid(R0,p)))} 
  dcmld_init_more (U, U0+(U-R0), G+mkid(R0,p), p) of DCMLD_INIT (U, U0, G, p)

symintr lemma_init_form
symintr lemma_init_form_neg
symintr lemma_init_role
symintr lemma_init_role_neg
symintr lemma_init_seqs

praxi lemma_init_form_c     {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mkic(R,A))} (DCMLC_INIT (U,U0,G,p)): [A==p] unit_p
praxi lemma_init_form_d     {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mkid(R,A))} (DCMLD_INIT (U,U0,G,p)): [A==p] unit_p
praxi lemma_init_form_neg_c {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {not(A==p)} (DCMLC_INIT (U,U0,G,p)): [not(mem(G,mkic(R,A)))] unit_p
praxi lemma_init_form_neg_d {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {not(A==p)} (DCMLD_INIT (U,U0,G,p)): [not(mem(G,mkid(R,A)))] unit_p
praxi lemma_init_form_mix_c {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} (DCMLC_INIT (U,U0,G,p)): [not(mem(G,mkid(R,A)))] unit_p
praxi lemma_init_form_mix_d {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} (DCMLD_INIT (U,U0,G,p)): [not(mem(G,mkic(R,A)))] unit_p
praxi lemma_init_role_c     {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R1,R2:roles} {mem(G,mkic(R1,p))&&mem(G,mkic(R2,p))} (DCMLC_INIT (U,U0,G,p)): [disj(R1,R2)] unit_p
praxi lemma_init_role_d     {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R1,R2:roles} {mem(G,mkid(R1,p))&&mem(G,mkid(R2,p))} (DCMLD_INIT (U,U0,G,p)): [disj(U-R1,U-R2)] unit_p
praxi lemma_init_role_neg_c {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {disj(U0,R)}   (DCMLC_INIT (U,U0,G,p)): [not(mem(G,mkic(R,A)))] unit_p
praxi lemma_init_role_neg_d {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {disj(U0,U-R)} (DCMLD_INIT (U,U0,G,p)): [not(mem(G,mkid(R,A)))] unit_p
praxi lemma_init_seqs_c     {U:roles} {U1,U2:roles|sub(U,U1,U2)} {G1,G2:seqs} {p:form} {disj(U1,U2)} (DCMLC_INIT (U,U1,G1,p), DCMLC_INIT (U,U2,G2,p)): [disj(G1,G2)] unit_p
praxi lemma_init_seqs_d     {U:roles} {U1,U2:roles|sub(U,U1,U2)} {G1,G2:seqs} {p:form} {disj(U1,U2)} (DCMLD_INIT (U,U1,G1,p), DCMLD_INIT (U,U2,G2,p)): [disj(G1,G2)] unit_p

overload lemma_init_form with lemma_init_form_c
overload lemma_init_form with lemma_init_form_d
overload lemma_init_form_neg with lemma_init_form_neg_c
overload lemma_init_form_neg with lemma_init_form_neg_d
overload lemma_init_form_mix with lemma_init_form_mix_c
overload lemma_init_form_mix with lemma_init_form_mix_d
overload lemma_init_role with lemma_init_role_c
overload lemma_init_role with lemma_init_role_d
overload lemma_init_role_neg with lemma_init_role_neg_c
overload lemma_init_role_neg with lemma_init_role_neg_d
overload lemma_init_seqs with lemma_init_seqs_c
overload lemma_init_seqs with lemma_init_seqs_d

symintr lemma_init_member
symintr lemma_init_remove
symintr lemma_init_merge

prfun lemma_init_member_c {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} (DCMLC_INIT (U,U0,G,p)): bool (mem(G,mkic(R,A)))
prfun lemma_init_member_d {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} (DCMLD_INIT (U,U0,G,p)): bool (mem(G,mkid(R,A)))
prfun lemma_init_remove_c {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} {mem(G,mkic(R,A))} (DCMLC_INIT (U,U0,G,p)): DCMLC_INIT (U,U0-R,    G-mkic(R,A),p)
prfun lemma_init_remove_d {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form|is_atom(p)} {R:roles} {A:form} {mem(G,mkid(R,A))} (DCMLD_INIT (U,U0,G,p)): DCMLD_INIT (U,U0-(U-R),G-mkid(R,A),p)
prfun lemma_init_merge_c  {U:roles} {U1,U2:roles|sub(U,U1,U2)&&disj(U1,U2)} {G1,G2:seqs|disj(G1,G2)} {p:form|is_atom(p)} (DCMLC_INIT (U,U1,G1,p), DCMLC_INIT (U,U2,G2,p)): DCMLC_INIT (U,U1+U2,G1+G2,p)
prfun lemma_init_merge_d  {U:roles} {U1,U2:roles|sub(U,U1,U2)&&disj(U1,U2)} {G1,G2:seqs|disj(G1,G2)} {p:form|is_atom(p)} (DCMLD_INIT (U,U1,G1,p), DCMLD_INIT (U,U2,G2,p)): DCMLD_INIT (U,U1+U2,G1+G2,p)

overload lemma_init_member with lemma_init_member_c
overload lemma_init_member with lemma_init_member_d
overload lemma_init_remove with lemma_init_remove_c
overload lemma_init_remove with lemma_init_remove_d
overload lemma_init_merge with lemma_init_merge_c
overload lemma_init_merge with lemma_init_merge_d


(* DCML encoding *)

dataprop DCML (roles, int, seqt) = 
(* axiom *)
| {U:roles} {G:seqs} {Gi:seqs|sub(G,Gi)} {p:form|is_atom(p)} 
  dcml_axi_c (U, 0, nil |- G) of DCMLC_INIT (U, U, Gi, p)

| {U:roles} {G:seqs} {Gi:seqs|sub(G,Gi)} {p:form|is_atom(p)} 
  dcml_axi_d (U, 0, nil |- G) of DCMLD_INIT (U, U, Gi, p)

(* logical rules - conj *)
| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form} {M:nat}   {mem(G,mkic(R,conn(r,A,B)))}
  dcml_conn_n1 (U, M+1, nil |- G)  of DCML (U, M, nil |- G + mkic(R,A))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form} {N:nat}   {mem(G,mkic(R,conn(r,A,B)))}
  dcml_conn_n2 (U, N+1, nil |- G)  of DCML (U, N, nil |- G + mkic(R,B))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))}   {A,B:form} {M,N:nat} {mem(G,mkic(R,conn(r,A,B)))}
  dcml_conn_p (U, M+N+1, nil |- G) of (DCML (U, M, nil |- G + mkic(R,A)), DCML (U, N, nil |- G + mkic(R,B)))

(* logical rules - disj *)
| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))}   {A,B:form} {M:nat}   {mem(G,mkid(R,conn(r,A,B)))}
  dcml_conn_p1 (U, M+1, nil |- G)  of DCML (U, M, nil |- G + mkid(R,A))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(R,mk(r))}   {A,B:form} {N:nat}   {mem(G,mkid(R,conn(r,A,B)))}
  dcml_conn_p2 (U, N+1, nil |- G)  of DCML (U, N, nil |- G + mkid(R,B))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {r:role|mem(U-R,mk(r))} {A,B:form} {M,N:nat} {mem(G,mkid(R,conn(r,A,B)))}
  dcml_conn_n (U, M+N+1, nil |- G) of (DCML (U, M, nil |- G + mkid(R,A)), DCML (U, N, nil |- G + mkid(R,B)))

(* logical rules - neg *)
| {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {mem(G,mkic(R,neg(A)))}
  dcml_neg_c (U, M+1, nil |- G) of DCML (U, M, nil |- G + mkid(U-R,A))

| {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {mem(G,mkid(R,neg(A)))}
  dcml_neg_d (U, M+1, nil |- G) of DCML (U, M, nil |- G + mkic(U-R,A))

//symintr lemma_full
//symintr lemma_empty
//symintr lemma_wk
//symintr lemma_ctr
//symintr lemma_id
//symintr lemma_2cut
//symintr lemma_3cut
//symintr lemma_2cut_spill
//symintr lemma_split

prfun lemma_full_c       {U:roles} {G:seqs} {A:form} (): [M:nat] DCML (U, M, nil |- G + mkic(U,A))
prfun lemma_empty_c      {U:roles} {G:seqs} {A:form} {M:nat} (DCML (U, M, nil |- G + mkic(emp,A))): [I:nat|I <= M] DCML (U, I, nil |- G)

prfun lemma_full_d       {U:roles} {G:seqs} {A:form} {M:nat} (DCML (U, M, nil |- G + mkid(U,A))): [I:nat|I <= M] DCML (U, I, nil |- G)
prfun lemma_empty_d      {U:roles} {G:seqs} {A:form} (): [M:nat] DCML (U, M, nil |- G + mkid(emp,A))

prfun lemma_wk_c         {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} (DCML (U, M, nil |- G)): DCML (U, M, nil |- G + mkic(R,A))
prfun lemma_ctr_c        {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mkic(R,A))>1} (DCML (U, M, nil |- G)): DCML (U, M, nil |- G - mkic(R,A))
prfun lemma_id_c         {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,R1,R2)} {A:form} (): [M:nat] DCML (U, M, nil |- G + mkic(R1,A) + mkic(R2,A))

prfun lemma_wk_d         {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} (DCML (U, M, nil |- G)): DCML (U, M, nil |- G + mkid(R,A))
prfun lemma_ctr_d        {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mkid(R,A))>1} (DCML (U, M, nil |- G)): DCML (U, M, nil |- G - mkid(R,A))
prfun lemma_id_d         {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,U-R1,U-R2)} {A:form} (): [M:nat] DCML (U, M, nil |- G + mkid(R1,A) + mkid(R2,A))

prfun lemma_2cut_c       {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,U-R1,U-R2)} {A:form} {M,N:nat} (DCML (U, M, nil |- G + mkic(R1,A)), DCML (U, N, nil |- G + mkic(R2,A))): [I:nat] DCML (U, I, nil |- G)
prfun lemma_3cut_c       {U:roles} {G:seqs} {R1,R2,R3:roles|sub(U,R1,R2,R3)&&disjunion(U,U-R1,U-R2,U-R3)} {A:form} {M,N,L:nat} (DCML (U, M, nil |- G + mkic(R1,A)), DCML (U, N, nil |- G + mkic(R2,A)), DCML (U, L, nil |- G + mkic(R3,A))): [I:nat] DCML (U, I, nil |- G)
prfun lemma_2cut_spill_c {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(U-R1,U-R2)} {A:form} {M,N:nat} (DCML (U, M, nil |- G + mkic(R1,A)), DCML (U, N, nil |- G + mkic(R2,A))): [I:nat] DCML (U, I, nil |- G + mkic(R1*R2,A))
prfun lemma_split_c      {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(R1,R2)} {A:form} {M:nat} (DCML (U, M, nil |- G + mkic(R1+R2,A))): [I:nat] DCML (U, I, nil |- G + mkic(R1,A) + mkic(R2,A))

prfun lemma_2cut_d       {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,R1,R2)} {A:form} {M,N:nat} (DCML (U, M, nil |- G + mkid(R1,A)), DCML (U, N, nil |- G + mkid(R2,A))): [I:nat] DCML (U, I, nil |- G)
prfun lemma_3cut_d       {U:roles} {G:seqs} {R1,R2,R3:roles|sub(U,R1,R2,R3)&&disjunion(U,R1,R2,R3)} {A:form} {M,N,L:nat} (DCML (U, M, nil |- G + mkid(R1,A)), DCML (U, N, nil |- G + mkid(R2,A)), DCML (U, L, nil |- G + mkid(R3,A))): [I:nat] DCML (U, I, nil |- G)
prfun lemma_2cut_spill_d {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(R1,R2)} {A:form} {M,N:nat} (DCML (U, M, nil |- G + mkid(R1,A)), DCML (U, N, nil |- G + mkid(R2,A))): [I:nat] DCML (U, I, nil |- G + mkid(R1+R2,A))
prfun lemma_split_d      {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(U-R1,U-R2)} {A:form} {M:nat} (DCML (U, M, nil |- G + mkid(R1*R2,A))): [I:nat] DCML (U, I, nil |- G + mkid(R1,A) + mkid(R2,A))

//overload lemma_full with lemma_full_c
//overload lemma_full with lemma_full_d
//overload lemma_empty with lemma_empty_c
//overload lemma_empty with lemma_empty_d
//overload lemma_wk with lemma_wk_c
//overload lemma_wk with lemma_wk_d
//overload lemma_ctr with lemma_ctr_c
//overload lemma_ctr with lemma_ctr_d
//overload lemma_id with lemma_id_c
//overload lemma_id with lemma_id_d
//overload lemma_2cut with lemma_2cut_c
//overload lemma_2cut with lemma_2cut_d
//overload lemma_3cut with lemma_3cut_c
//overload lemma_3cut with lemma_3cut_d
//overload lemma_2cut_spill with lemma_2cut_spill_c
//overload lemma_2cut_spill with lemma_2cut_spill_d
//overload lemma_split with lemma_split_c
//overload lemma_split with lemma_split_d
