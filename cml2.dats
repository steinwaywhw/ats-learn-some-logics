staload "cml2.sats"

prval _ = $solver_assert lemma_set_size_nat
prval _ = $solver_assert lemma_set_size_empty
prval _ = $solver_assert lemma_set_size_add1
prval _ = $solver_assert lemma_set_size_add2
prval _ = $solver_assert lemma_set_sub_emp
prval _ = $solver_assert lemma_set_sub_sub
prval _ = $solver_assert lemma_set_sub_cap
prval _ = $solver_assert lemma_set_sub_cup
prval _ = $solver_assert lemma_set_sub_cap2
prval _ = $solver_assert lemma_set_sub_cup2
prval _ = $solver_assert lemma_set_sub_self
prval _ = $solver_assert lemma_set_com

prval _ = $solver_assert lemma_mk_iform_inj
prval _ = $solver_assert lemma_mk_iform_bij
prval _ = $solver_assert lemma_mk_role_inj
prval _ = $solver_assert lemma_mk_role_bij

prval _ = $solver_assert lemma_form_size_nat
prval _ = $solver_assert lemma_form_size_atom
prval _ = $solver_assert lemma_form_size_conj

prval _ = $solver_assert lemma_list_len_nil
prval _ = $solver_assert lemma_list_len_cons
prval _ = $solver_assert lemma_list_append_nil
prval _ = $solver_assert lemma_list_append_cons



extern prfun lemma_seqs_pop {G:seqs} {R:roles} {A:form|mem(G,mki(R,A))} (): [G0:seqs] unit_p
extern prfun lemma_seqs_contains {G:seqs} {R:roles} {A:form} (): bool (mem(G,mki(R,A)))
extern prfun lemma_init_contains {U:roles} {G:seqs} {p:form|size(p)==1} {R0:roles} {p0:form|size(p0)==1} (CML_INIT (U, G, p)): bool (mem(G,mki(R0,p0)))

primplement lemma_seqs_contains {G}{R}{A} () = 
	sif G == lnil 
	then let prval _ = lemma_list_mem_nil {mki(R,A)} () in false end 
	else 
		sif hd G == mki(R,A)
		then let prval _ = lemma_list_mem_cons {mki(R,A)}{hd G}{tl G} () in true end 
		else let prval _ = lemma_list_mem_cons {mki(R,A)}{hd G}{tl G} () in lemma_seqs_contains {tl G}{R}{A} () end 

primplement lemma_init_contains {U}{G}{p}{R0}{p0} (init) = 
	case+ init of 
	| cml_init_zero {p} => let prval _ = lemma_list_mem_nil {mki(R0,p0)} () in false end 
	| cml_init_more {r}{g}{p}{r0} init => 
		sif r0 == R0 && p == p0
		then let prval _ = lemma_list_mem_cons {mki(R0,p0)}{mki(r0,p)}{g} () in true end 
		else let prval _ = lemma_list_mem_cons {mki(R0,p0)}{mki(r0,p)}{g} () in lemma_init_contains {r}{g}{p}{R0}{p0} init end 


primplement lemma_2cut {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 
	prfun ih {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} {M,N:nat} .<size(A),M,N>. 
		(fst: CML (U, m, nil |- mki(R1,A) ++ G), snd: CML (U, n, nil |- mki(R2,A) ++ G)): [i:nat] CML (U, i, nil |- G) = 

		case- fst of 
		| cml_axi {U}{g0,gi0}{p} pf0 => 
			(*
				pf0: CML_INIT (gi0, U, p)
				------------------------
				fst: A(R1) ++ G = g0 + gi0(p's)   snd: G + A(R2)
				-----------------------------------------------
				goal: G
			*)
			if lemma_seqs_contains {g0}{R1}{A} ()
			then 









