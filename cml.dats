
staload "./cml.sats"
infix |- 

//extern praxi lemma_consistency_test {1==2} (): unit_p

prval _ = $solver_assert lemma_bag_car_nat
prval _ = $solver_assert lemma_bag_size_nat
prval _ = $solver_assert lemma_bag_size_empty
//prval _ = $solver_assert lemma_bag_size_add
//prval _ = $solver_assert lemma_bag_size_cup

prval _ = $solver_assert lemma_set_size_nat
prval _ = $solver_assert lemma_set_size_empty
//prval _ = $solver_assert lemma_set_size_add



prval _ = $solver_assert lemma_mk_iform_inj
prval _ = $solver_assert lemma_mk_iform_bij
prval _ = $solver_assert lemma_mk_role_inj
prval _ = $solver_assert lemma_mk_role_bij

prval _ = $solver_assert lemma_form_size_nat
prval _ = $solver_assert lemma_form_size_atom
prval _ = $solver_assert lemma_form_size_conj



primplement lemma_init_member {U}{G}{p}{R}{A} (init) = 
	case+ init of 
	| cml_init_zero {p} => false 
	| cml_init_more {r}{g}{p}{r0} init => 
		sif mki(r0,p) == mki(R,A)
		then true
		else lemma_init_member {r}{g}{p}{R}{A} init

primplement lemma_init_remove {U}{G}{p}{R}{A} (init) = let 
	prval _ = lemma_init_form {U}{G}{p}{R}{A} init 
in 
	case+ init of 
	| cml_init_zero {p} =/=> ()
	| cml_init_more {r}{g}{p}{r0} pf => 
		sif R == r0 
		then pf 
		else let 
			prval _ = lemma_init_role {U}{G}{p}{R,r0} init
		in 
			cml_init_more {r-R}{g-mki(R,A)}{p}{r0} (lemma_init_remove {r}{g}{p}{R}{A} pf)
		end 
end

primplement lemma_init_merge {U1,U2}{G1,G2}{p} (fst, snd) = 
	case+ fst of 
	| cml_init_zero {p} => snd 
	| cml_init_more {r}{g}{p}{r0} fst => cml_init_more {r+U2}{g+G2}{p}{r0} (lemma_init_merge {r,U2}{g,G2}{p} (fst, snd))


primplement lemma_wk {U}{G}{R}{A}{M} (pf) = let 
	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} .<M>. (pf: CML (U, M, nil |- G)): CML (U, M, nil |- G + mki(R,A)) = 
		case+ pf of 
		| cml_axi {U}{g}{gi}{p} pf => cml_axi {U}{g+mki(R,A)}{gi}{p} pf 
		| cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf => 
			cml_conj_n1 {U}{g+mki(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mki(r,a)}{R}{A}{m} pf)
		| cml_conj_n2 {U}{g}{r}{rr}{a,b}{m} pf => 
			cml_conj_n2 {U}{g+mki(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mki(r,b)}{R}{A}{m} pf)
		| cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			cml_conj_p {U}{g+mki(R,A)}{r}{rr}{a,b}{m,n} (
				ih {U}{g+mki(r,a)}{R}{A} pf1, 
				ih {U}{g+mki(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 


primplement lemma_ctr {U}{G}{R}{A}{M} (pf) = let 

	prfun lemma_init_car {U:roles} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mki(R,A))&&not(R==emp)} .<size(G)>. (init: CML_INIT (U,G,p)): [car(G,mki(R,A))==1] unit_p = 
		case+ init of 
		| cml_init_zero {p} =/=> ()
		| cml_init_more {u}{g}{p}{r} (init) => 
			sif not (R == r)
			then let prval _ = lemma_bag_size_add {g}{mki(r,p)} () in lemma_init_car {u}{g}{p}{R}{A} init end
			else lemma_init_role_neg {u}{g}{p}{R}{A} init

	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mki(R,A))>1} .<M>. 
		(pf: CML (U, M, nil |- G)): CML (U, M, nil |- G - mki(R,A)) = 

		case+ pf of 
		| cml_axi {U}{g}{gi}{p} init => 
			sif mem (g-gi, mki(R,A))
			then cml_axi {U}{g-mki(R,A)}{gi}{p} init
			else 
				let 
					prval _ = lemma_init_member {U}{gi}{p}{R}{A} init 
					prval _ = lemma_init_form {U}{gi}{p}{R}{A} init
				in 
					sif not (R == emp)
					then let prval _ = lemma_init_car {U}{gi}{p}{R}{A} init in false_elim () end
					else cml_axi {U}{g-mki(R,A)}{gi-mki(R,A)}{p} (lemma_init_remove {U}{gi}{p}{R}{A} init)
				end 
		| cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf => 
			cml_conj_n1 {U}{g-mki(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mki(r,a)}{R}{A}{m} pf)
		| cml_conj_n2 {U}{g}{r}{rr}{a,b}{m} pf => 
			cml_conj_n2 {U}{g-mki(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mki(r,b)}{R}{A}{m} pf)
		| cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			cml_conj_p {U}{g-mki(R,A)}{r}{rr}{a,b}{m,n} (ih {U}{g+mki(r,a)}{R}{A} pf1, ih {U}{g+mki(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 


primplement lemma_3cut {U}{G}{R1,R2,R3}{A}{M,N,L} (fst, snd, trd) = let 
	prval [i:int] pf = lemma_2cut_spill {U}{G}{R1,R2}{A}{M,N} (fst, snd)
in 
	lemma_2cut {U}{G}{R1*R2,R3}{A}{i,L} (pf, trd)
end

primplement lemma_split {U}{G}{R1,R2}{A}{M} (pf) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(R1,R2)} {A:form} {M:nat} .<size(A),M>. 
		(pf: CML (U, M, nil |- G + mki(R1+R2,A))): [I:nat] CML (U, I, nil |- G + mki(R1,A) + mki(R2,A)) = 

		case+ pf of 
 		| cml_axi {U}{g}{gi}{p} init => 
 			(*
				init: init (U,gi,p)
				------------------
				pf: G + A[R1+R2] = g(gi)
				------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if not (lemma_init_member {U}{gi}{p}{R1+R2}{A} init)
 			then cml_axi {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{gi}{p} init
 			else 
 				let 
 					prval _ = lemma_init_form {U}{gi}{p}{R1+R2}{A} init 
 					prval init = lemma_init_remove {U}{gi}{p}{R1+R2}{A} init

 					prval _ = lemma_init_role_neg {U-(R1+R2)}{gi-mki(R1+R2,A)}{p}{R1}{A} init
 					prval init = cml_init_more {U-(R1+R2)}{gi-mki(R1+R2,A)}{p}{R1} init

 					prval _ = lemma_init_role_neg {U-R2}{gi-mki(R1+R2,A)+mki(R1,A)}{p}{R2}{A} init 
 					prval init = cml_init_more {U-R2}{gi-mki(R1+R2,A)+mki(R1,A)}{p}{R2} init
 				in 
 					cml_axi {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{gi-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{A} init
 				end

 		| cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conj(rr,a,b)[r]) + a[r]
				------------------------------
				pf: g(conj(rr,a,b)[r]) = G + A[R1+R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,conj(rr,a,b))}{mki(R1+R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mki(r,a)}{R1,R2}{A}{m} pf0
 				in cml_conj_n1 {U}{G+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					(* split conj(rr,a,b)[r] first, for the sake of termination checks *)
 					prval [i:int] pf = ih {U}{G+mki(r,a)}{R1,R2}{A}{m} pf0
 					(* split a[r] *)
 					prval [i:int] pf = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{a}{i} pf

 					prval pf = cml_conj_n1 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,a)}{R1}{rr}{a,b}{i} pf
 					prval pf = cml_conj_n1 {U}{G+mki(R1,A)+mki(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

		| cml_conj_n2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conj(rr,a,b)[r]) + b[r]
				------------------------------
				pf: g(conj(rr,a,b)[r]) = G + A[R1+R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,conj(rr,a,b))}{mki(R1+R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mki(r,b)}{R1,R2}{A}{m} pf0
 				in cml_conj_n2 {U}{G+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					prval [i:int] pf = ih {U}{G+mki(r,b)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{b}{i} pf

 					prval pf = cml_conj_n2 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,b)}{R1}{rr}{a,b}{i} pf
 					prval pf = cml_conj_n2 {U}{G+mki(R1,A)+mki(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

 		| cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
 			(*
				pf0: g(conj(rr,a,b)[r]) + a[r]
				pf1: g(conj(rr,a,b)[r]) + b[r]
				------------------------------
				pf:  g(conj(rr,a,b)[r]) = G + A[R1+R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,conj(rr,a,b))}{mki(R1+R2,A)} ()
 			then 
 				let 
 				 	prval [i:int] pf0 = ih {U}{G+mki(r,a)}{R1,R2}{A}{m} pf0
 					prval [j:int] pf1 = ih {U}{G+mki(r,b)}{R1,R2}{A}{n} pf1
 				in 
 					cml_conj_p {U}{G+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
 				end
 			else 
 				let 
 					(* G + A[R1] + A[R2] + a[R1] + a[R2] *)
 					prval [i:int] pf0 = ih {U}{G+mki(r,a)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf0 = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{a}{i} pf0

 					(* G + A[R1] + A[R2] + b[R1] + b[R2] *)
 					prval [j:int] pf1 = ih {U}{G+mki(r,b)}{R1,R2}{A}{n} pf1
 					prval [j:int] pf1 = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{b}{j} pf1
 				in 
 					sif not (mem (R1, mk(rr)))
 					then  
 						let 
		 					prval pf0 = cml_conj_n1 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,a)}{R1}{rr}{a,b}{i} pf0
		 					prval pf1 = cml_conj_n2 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,b)}{R1}{rr}{a,b}{j} pf1
		 				in 
		 					cml_conj_p {U}{G+mki(R1,A)+mki(R2,A)}{R2}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 			else 
		 				let 
		 					prval pf0 = cml_conj_n1 {U}{G+mki(R1,A)+mki(R2,A)+mki(R1,a)}{R2}{rr}{a,b}{i} pf0
		 					prval pf1 = cml_conj_n2 {U}{G+mki(R1,A)+mki(R2,A)+mki(R1,b)}{R2}{rr}{a,b}{j} pf1
		 				in 
		 					cml_conj_p {U}{G+mki(R1,A)+mki(R2,A)}{R1}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 		end
in 
	ih {U}{G}{R1,R2}{A}{M} pf 
end 



primplement lemma_2cut_spill {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 
	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(U-R1,U-R2)} {A:form} {M,N:nat} .<size(A),M+N>.
		(fst: CML (U, M, nil |- G + mki(R1,A)), snd: CML (U, N, nil |- G + mki(R2,A))): [I:nat] CML (U, I, nil |- G + mki(R1*R2,A)) = 

		sif is_atom A 
		then 
			case+ (fst, snd) of 
			| (cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				(*
					pf: g(conj(rr,a,b)[r]) + a[r]                           
					-----------------------------                           
					fst: G + A[R1] = g                      snd: G + A[R2]
					-------------------------------------------------------
					goal: G + A[R1*R2]
				*)
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cml_conj_n1 {U}{g-mki(R1,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cml_conj_n2 {U}{g-mki(R1,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cml_conj_n1 {U}{g-mki(R2,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_ar, pf)
				in 
					cml_conj_n2 {U}{g-mki(R2,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cml_conj_p {U}{g-mki(R1,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cml_conj_p {U}{g-mki(R2,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cml_axi {U}{g1}{gi1}{p1} init1, cml_axi {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{gi1}{p1}{R1}{A} init1
				then cml_axi {U}{g1-mki(R1,A)+mki(R1*R2,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{gi2}{p2}{R2}{A} init2 
				then cml_axi {U}{g2-mki(R2,A)+mki(R1*R2,A)}{gi2}{p2} init2
				else
					(*
						init1: CML_INIT (U,gi1,A)         init2: CML_INIT (U,gi2,A)
						--------------------------        ---------------------------
						fst: G + A[R1] = g1(gi1(A[R1]))   snd: G + A[R2] = g2(gi2(A[R2]))
						-----------------------------------------------------------------------------------------
						goal: G + A[R1*R2]

						G + A[R1] = g1' + gi1 (A[R1])
						G + A[R2] = g2' + gi2 (A[R2])
					*)
					let 
						prval _ = lemma_init_form {U}{gi1}{p1}{R1}{A} init1
						prval _ = lemma_init_form {U}{gi2}{p2}{R2}{A} init2
						prval init1 = lemma_init_remove {U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{gi2}{p2}{R2}{A} init2 
						prval _ = lemma_init_seqs {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)

						(* init = U-R1 + U-R2, missing R1*R2 right now *)
						prval init = lemma_init_merge {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)

						(* prove R1*R2 + U-R1 + U-R2 = U, all disjoint *)
						prval _ = lemma_set_com_demorgan {U,U-R1,U-R2} ()
						(* prove A[R1*R2] is not in gi1-A[R1] or gi2-A[R2] *)
						prval _ = lemma_init_role_neg {(U-R1)+(U-R2)}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A}{R1*R2}{A} (init)

						(* add back A[R1*R2] *)
						prval init = cml_init_more {(U-R1)+(U-R2)}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A}{R1*R2} init
					in 
						cml_axi {U}{G+mki(R1*R2,A)}{(gi1-mki(R1,A))+(gi2-mki(R2,A))+mki(R1*R2,A)}{A} init
					end 
		else
			case+ (fst, snd) of 
			| (cml_axi {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{gi1}{p1}{R1}{A} init in cml_axi {U}{g1-mki(R1,A)+mki(R1*R2,A)}{gi1}{p1} init end
			| (_, cml_axi {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{gi2}{p2}{R2}{A} init in cml_axi {U}{g2-mki(R2,A)+mki(R1*R2,A)}{gi2}{p2} init end

			| (cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cml_conj_n1 {U}{g-mki(R1,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cml_conj_n2 {U}{g-mki(R1,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cml_conj_n1 {U}{g-mki(R2,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					cml_conj_n2 {U}{g-mki(R2,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R1,A)} () =>   
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cml_conj_p {U}{g-mki(R1,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R2,A)} () =>   
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cml_conj_p {U}{g-mki(R2,A)+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cml_conj_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, cml_conj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
													   pf21: G + conj(rr,a,b)[R2] + a[R2] 
					pf1: G + conj(rr,a,b)[R1] + a[R1]  pf22: G + conj(rr,a,b)[R2] + b[R2]                        
					---------------------------------  ---------------------------------                         
					fst: G + conj(rr,a,b)[R1] = g1     snd:  G + conj(rr,a,b)[R2] = g2
					--------------------------------------------------------------------
					goal: G + A[R1*R2]

					A is principal in both
				*)
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + a1[R2], pf21) = G + a[R2] + A[R1*R2] *)
					prval fst_aR2 = lemma_wk {U}{g1}{R2}{a} fst 
					prval [i:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conj(rr,a,b)}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] + A[R1*R2] *)
					prval snd_aR1 = lemma_wk {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conj(rr,a,b)}{m1,N} (pf1, snd_aR1)

					(* cut (G_aR1, G_aR2) = G + a[R1*R2] + A[R1*R2] *)
					prval [k:int] pf = ih {U}{G+mki(R1*R2,A)}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				in 
					cml_conj_n1 {U}{G+mki(R1*R2,A)}{R1*R2}{rr}{a,b}{k} pf 
				end 

			| (cml_conj_n2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, cml_conj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conj(rr,a,b)}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conj(rr,a,b)}{n1,N} (pf1, snd_bR1)
					
					prval [k:int] pf = ih {U}{G+mki(R1*R2,A)}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				in 
					cml_conj_n2 {U}{G+mki(R1*R2,A)}{R1*R2}{rr}{a,b}{k} pf
				end 

			| (cml_conj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cml_conj_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
					pf11: G + conj(rr,a,b)[R1] + a[R1] 								    
					pf12: G + conj(rr,a,b)[R1] + b[R1]   pf2: G + conj(rr,a,b)[R2] + a[R2]                          
					----------------------------------   ---------------------------------                          
					fst:  G + conj(rr,a,b)[R1] = g1      snd: G + conj(rr,a,b)[R2] = g2     
					--------------------------------------------------------------------
					goal: G + A[R1*R2]

					A is principal in both
				*)
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + a[R1], pf11) = G + a[R1] + A[R1*R2] *)
					prval snd_aR1 = lemma_wk {U}{g2}{R1}{a} snd 
					prval [i:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conj(rr,a,b)}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] + A[R1*R2] *)
					prval fst_aR2 = lemma_wk {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conj(rr,a,b)}{M,m2} (fst_aR2, pf2)
				
					prval [k:int] pf = ih {U}{G+mki(R1*R2,A)}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				in 
					cml_conj_n1 {U}{G+mki(R1*R2,A)}{R1*R2}{rr}{a,b}{k} pf 
				end 

			| (cml_conj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cml_conj_n2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conj(rr,a,b)}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conj(rr,a,b)}{M,n2} (fst_bR2, pf2)
					
					prval [k:int] pf = ih {U}{G+mki(R1*R2,A)}{R1,R2}{b}{i,j} (G_bR1, G_bR2)
				in 
					cml_conj_n2 {U}{G+mki(R1*R2,A)}{R1*R2}{rr}{a,b}{k} pf
				end 

			
			| (_, _) =/=>> 
				let 
					extern praxi bottom (): [false] unit_p
					prval _ = $solver_assert bottom
				in 
					()
				end

in 
	ih {U}{G}{R1,R2}{A}{M,N} (fst, snd)
end 



primplement lemma_2cut {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|disjunion(U,U-R1,U-R2)} {A:form} {M,N:nat} .<size(A),M+N>. 
		(fst: CML (U, M, nil |- G + mki(R1,A)), snd: CML (U, N, nil |- G + mki(R2,A))): [I:nat] CML (U, I, nil |- G) = 

		sif not (is_atom A) 
		then 
			case+ (fst, snd) of 
			| (cml_axi {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{gi1}{p1}{R1}{A} init in cml_axi {U}{g1-mki(R1,A)}{gi1}{p1} init end
			| (_, cml_axi {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{gi2}{p2}{R2}{A} init in cml_axi {U}{g2-mki(R2,A)}{gi2}{p2} init end

			| (cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cml_conj_n1 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cml_conj_n2 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cml_conj_n1 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					cml_conj_n2 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R1,A)} () =>   
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cml_conj_p {U}{g-mki(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,conj(rr,a,b))}{mki(R2,A)} () =>   
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cml_conj_p {U}{g-mki(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cml_conj_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, cml_conj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
													   pf21: G + conj(rr,a,b)[R2] + a[R2] 
					pf1: G + conj(rr,a,b)[R1] + a[R1]  pf22: G + conj(rr,a,b)[R2] + b[R2]                        
					---------------------------------  ---------------------------------                         
					fst: G + conj(rr,a,b)[R1] = g1     snd:  G + conj(rr,a,b)[R2] = g2
					--------------------------------------------------------------------
					goal: G

					A is principal in both
				*)
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + a1[R2], pf21) = G + a1[R2] *)
					prval fst_aR2 = lemma_wk {U}{g1}{R2}{a} fst 
					prval [i:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conj(rr,a,b)}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] *)
					prval snd_aR1 = lemma_wk {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conj(rr,a,b)}{m1,N} (pf1, snd_aR1)
				in 
					ih {U}{G}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				end 

			| (cml_conj_n2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, cml_conj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conj(rr,a,b)}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conj(rr,a,b)}{n1,N} (pf1, snd_bR1)
				in 
					ih {U}{G}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				end 

			| (cml_conj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cml_conj_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
					pf11: G + conj(rr,a,b)[R1] + a[R1] 								    
					pf12: G + conj(rr,a,b)[R1] + b[R1]   pf2: G + conj(rr,a,b)[R2] + a[R2]                          
					----------------------------------   ---------------------------------                          
					fst:  G + conj(rr,a,b)[R1] = g1      snd: G + conj(rr,a,b)[R2] = g2     
					--------------------------------------------------------------------
					goal: G

					A is principal in both
				*)
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + a[R1], pf11) = G + a[R1] *)
					prval snd_aR1 = lemma_wk {U}{g2}{R1}{a} snd 
					prval [i:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conj(rr,a,b)}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] *)
					prval fst_aR2 = lemma_wk {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conj(rr,a,b)}{M,m2} (fst_aR2, pf2)
				in 
					ih {U}{G}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				end 

			| (cml_conj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cml_conj_n2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conj(rr,a,b)}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conj(rr,a,b)}{M,n2} (fst_bR2, pf2)
				in 
					ih {U}{G}{R1,R2}{b}{i,j} (G_bR1, G_bR2)
				end 

			
			| (_, _) =/=>> 
				let 
					extern praxi bottom (): [false] unit_p
					prval _ = $solver_assert bottom
				in 
					()
				end

//			| (cml_conj_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} _, cml_conj_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} _) when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =/=>> ()
//			| (cml_conj_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} _, cml_conj_n2 {U}{g2}{r2}{rr2}{a2,b2}{m2} _) when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =/=>> ()
//			| (cml_conj_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} _, cml_conj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} _) when ~(is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} ()) =/=>> ()

//			| (cml_conj_n2 {U}{g1}{r1}{rr1}{a1,b1}{m1} _, cml_conj_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} _) when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =/=>> ()
//			| (cml_conj_n2 {U}{g1}{r1}{rr1}{a1,b1}{m1} _, cml_conj_n2 {U}{g2}{r2}{rr2}{a2,b2}{m2} _) when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =/=>> ()
//			| (cml_conj_n2 {U}{g1}{r1}{rr1}{a1,b1}{n1} _, cml_conj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} _) when ~(is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} ()) =/=>> ()

//			| (cml_conj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} _, cml_conj_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} _) when ~(is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} ()) =/=>> ()
//			| (cml_conj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} _, cml_conj_n2 {U}{g2}{r2}{rr2}{a2,b2}{n2} _) when ~(is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} ()) =/=>> ()
//			| (cml_conj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} _, cml_conj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} _) when is_principal {mki(r1,conj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conj(rr2,a2,b2))}{mki(R2,A)} () =/=>> ()

		else 
			case+ (fst, snd) of 
			| (cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				(*
					pf: g(conj(rr,a,b)[r]) + a[r]                           
					-------------------------------------                           
					fst: G + A[R1] = g                      snd: G + A[R2]
					-------------------------------------------------------
					goal: G
				*)
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cml_conj_n1 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cml_conj_n2 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cml_conj_n1 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cml_conj_n2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_ar, pf)
				in 
					cml_conj_n2 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cml_conj_p {U}{g-mki(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cml_conj_p {U}{g-mki(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cml_axi {U}{g1}{gi1}{p1} init1, cml_axi {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{gi1}{p1}{R1}{A} init1
				then cml_axi {U}{g1-mki(R1,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{gi2}{p2}{R2}{A} init2 
				then cml_axi {U}{g2-mki(R2,A)}{gi2}{p2} init2
				else
					(*
						init1: CML_INIT (U,gi1,A)                   init2: CML_INIT (U,gi2,A)
						--------------------------                  ---------------------------
						fst: G + A[R1] = g1(gi1(A[R1]))   snd: G + A[R2] = g2(gi2(A[R2]))
						-----------------------------------------------------------------------------------------
						goal: G

						G + A[R1] = g1' + gi1 (A[R1])
						G + A[R2] = g2' + gi2 (A[R2])
					*)
					let 
						prval _ = lemma_init_form {U}{gi1}{p1}{R1}{A} init1
						prval _ = lemma_init_form {U}{gi2}{p2}{R2}{A} init2
						prval init1 = lemma_init_remove {U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{gi2}{p2}{R2}{A} init2 
						prval _ = lemma_init_seqs {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)
						prval init = lemma_init_merge {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)
					in 
						cml_axi {U}{G}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A} init
					end 

in 
//	sif mem(G,mki(R1,A))
//	then lemma_ctr {U}{G+mki(R1,A)}{R1}{A}{M} fst 
//	else sif mem(G,mki(R2,A))
//	then lemma_ctr {U}{G+mki(R2,A)}{R2}{A}{N} snd 
//	else ih {U}{G}{R1,R2}{A}{M,N} (fst, snd)
	ih {U}{G}{R1,R2}{A}{M,N} (fst, snd)

end 



primplement lemma_full {U}{G}{A} () = let 
	prfun ih {U:roles} {G:seqs} {A:form} .<size(A)>. (): [m:nat] CML (U, m, nil |- G + mki(U,A)) =
		scase A of 
		| atom () => 
			let 
				prval pf = cml_init_more {emp}{nil}{A}{U} (cml_init_zero {A} ())
				prval pf = cml_axi {U}{G+mki(U,A)}{mki(U,A)+nil}{A} (pf)
			in 
				#[0|pf]
			end 
		| conj (r, p, q) => 
			let 
				(* assume that r always belongs to U *)
				extern praxi _asrt {U:roles} {r:role} (): [mem(U,mk(r))] unit_p
				prval _ = _asrt {U}{r} ()

				prval [i:int] pfp = ih {U}{G}{p} ()
				prval [j:int] pfq = ih {U}{G}{q} ()

				prval pfp = lemma_wk {U}{G+mki(U,p)}{U}{conj(r,p,q)}{i} pfp 
				prval pfq = lemma_wk {U}{G+mki(U,q)}{U}{conj(r,p,q)}{j} pfq

				prval pf = cml_conj_p {U}{G+mki(U,conj(r,p,q))}{U}{r}{p,q}{i,j} (pfp, pfq)
			in 
				#[i+j+1|pf]
			end
in 
	ih {U}{G}{A} ()
end 


primplement lemma_empty {U}{G}{A}{M} (pf) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {A:form} {M:nat} .<size(A),M>. (pf: CML (U, M, nil |- G + mki(emp,A))): [i:nat|i <= M] CML (U, i, nil |- G) = 
		case+ pf of 
		| cml_axi {U}{g}{gi}{p} init =>
			sif mem (g-gi, mki(emp,A))
			then cml_axi {U}{g-mki(emp,A)}{gi}{p} init
			else cml_axi {U}{g-mki(emp,A)}{gi-mki(emp,A)}{p} (lemma_init_remove {U}{gi}{p}{emp}{A} init)

		| cml_conj_n1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			(*
				pf0: g(conj(rr,a,b)[r]) + a[r]
				-----------------------------
				pf: g = G + A[]
				----------------
				goal: G
			*)
			if ~is_principal {mki(r,conj(rr,a,b))}{mki(emp,A)} ()
			then 
				let prval [i:int] pf0 = ih {U}{G+mki(r,a)}{A}{m} pf0 
				in cml_conj_n1 {U}{g-mki(emp,A)}{r}{rr}{a,b}{i} pf0 end
			else
				let 
					prval [i:int] pf0 = ih {U}{G+mki(r,a)}{A}{m} pf0
					prval [i:int] pf0 = ih {U}{G}{a}{i} pf0 
				in 
					pf0
				end

		| cml_conj_n2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			if ~is_principal {mki(r,conj(rr,a,b))}{mki(emp,A)} ()
			then 
				let prval [i:int] pf0 = ih {U}{G+mki(r,b)}{A}{m} pf0 
				in cml_conj_n2 {U}{g-mki(emp,A)}{r}{rr}{a,b}{i} pf0 end
			else
				let 
					prval [i:int] pf0 = ih {U}{G+mki(r,b)}{A}{m} pf0
					prval [i:int] pf0 = ih {U}{G}{b}{i} pf0 
				in 
					pf0
				end

		| cml_conj_p {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
			let 
				prval [i:int] pf0 = ih {U}{g+mki(r,a)-mki(emp,A)}{A} pf0
				prval [j:int] pf1 = ih {U}{g+mki(r,b)-mki(emp,A)}{A} pf1
			in 
				cml_conj_p {U}{g-mki(emp,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
			end

in 
	ih {U}{G}{A}{M} pf 
end 

primplement lemma_id {U}{G}{R1,R2}{A} () = lemma_split {U}{G}{R1,R2}{A} (lemma_full {U}{G}{A} ())




