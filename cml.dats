
staload "./cml.sats"
infix |- 



//extern praxi lemma_test {1==2} (): unit_p

prval _ = $solver_assert lemma_bag_car_nat
prval _ = $solver_assert lemma_bag_size_nat
prval _ = $solver_assert lemma_bag_size_empty
//prval _ = $solver_assert lemma_bag_size_add
//prval _ = $solver_assert lemma_bag_size_cup

prval _ = $solver_assert lemma_set_size_nat
prval _ = $solver_assert lemma_set_size_empty
//prval _ = $solver_assert lemma_set_size_add



//prval _ = $solver_assert lemma_bag_sub_emp
//prval _ = $solver_assert lemma_bag_sub_self
//prval _ = $solver_assert lemma_bag_sub_sub
//prval _ = $solver_assert lemma_bag_sub_cap
//prval _ = $solver_assert lemma_bag_sub_cup2
//prval _ = $solver_assert lemma_bag_sub_cap2


//prval _ = $solver_assert lemma_set_sub_emp
//prval _ = $solver_assert lemma_set_sub_self
//prval _ = $solver_assert lemma_set_sub_sub
//prval _ = $solver_assert lemma_set_sub_cap
//prval _ = $solver_assert lemma_set_sub_cup
//prval _ = $solver_assert lemma_set_sub_cap2
//prval _ = $solver_assert lemma_set_sub_cup2

//prval _ = $solver_assert lemma_set_com_law
//prval _ = $solver_assert lemma_set_com_sub
//prval _ = $solver_assert lemma_set_com_emp
//prval _ = $solver_assert lemma_set_com_uni
//prval _ = $solver_assert lemma_set_com_inv

//prval _ = $solver_assert lemma_set_com_demorgan


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




//primplement lemma_wk {U}{G}{R}{A}{M} (pf) = let 
//	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} .<M>. (pf: CML (U, M, nil |- G)): CML (U, M, nil |- G + mki(R,A)) = 
//		case+ pf of 
//		| cml_axi {U}{g}{gi}{p} init => cml_axi {U}{g+mki(R,A)}{gi}{p} init 

//in 
//		ih {U}{G}{R}{A}{M} pf
//end 



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

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} {M,N:nat} .<size(A),M+N>. 
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







////
//extern praxi lemma_split_ctr {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {R0:roles|sub(R,R0)&&mem(G,mki(R0,A))} {m:nat} (CML (U, m, nil |- G + mki(R,A))): [i:int] CML (U, i, nil |- G + mki(R-R0,A))
//prval _ = $solver_assert lemma_split_ctr


//extern praxi lemma_init_nil {G:seqs} {R:roles} {p:form|mem(G,mki(emp,p))&&size(p)==1} (CML_INIT (G, R, p)): CML_INIT (G - mki(emp,p), R, p)
//extern praxi lemma_init_only {G:seqs} {R,R1:roles|sub(R,R1)} {p,p1:form|not(p1==p)&&size(p)==1} (CML_INIT (G, R, p)): [not(mem(G, mki(R1,p1)))] unit_p
//extern praxi lemma_init_is {G:seqs} {R,R1:roles|sub(R,R1)} {p,p1:form|mem(G,mki(R1,p1))&&size(p)==1} (CML_INIT (G, R, p)): [p==p1] unit_p
//extern praxi lemma_init_nonoverlap {G:seqs} {R:roles} {p:form|size(p)==1} {R1,R2:roles|sub(R,R1) && sub(R,R2) && not(R1*R2==emp) && mem(G,mki(R1,p))} (CML_INIT (G, R, p)): [not(mem(G,mki(R2,p)))] unit_p
//extern praxi lemma_init_split {G:seqs} {R:roles} {p:form|size(p)==1} {R0,R1,R2:roles|sub(R,R0)&&fulljoin(R0,R1,R2)&&mem(G,mki(R0,p))} (CML_INIT (G, R, p)): CML_INIT (G-mki(R0,p)+mki(R1,p)+mki(R2,p), R, p)
//extern praxi lemma_init_join  {G:seqs} {R:roles} {p:form|size(p)==1} {R0,R1,R2:roles|sub(R,R0)&&fulljoin(R0,R1,R2)&&mem(G,mki(R1,p))&&mem(G,mki(R2,p))} (CML_INIT (G, R, p)): CML_INIT (G+mki(R0,p)-mki(R1,p)-mki(R2,p), R, p)
//extern praxi lemma_init_del {G:seqs} {R:roles} {p:form|size(p)==1} {R0:roles|sub(R,R0)&&mem(G,mki(R0,p))} (CML_INIT (G, R, p)): CML_INIT (G-mki(R0,p), R-R0, p)
//extern praxi lemma_init_replace {G:seqs} {R:roles} {p:form|size(p)==1} {G0:seqs} (CML_INIT (G, R, p)): CML_INIT (G0, R, p)
//extern praxi lemma_init_splitall {G:seqs} {R:roles} {p:form|size(p)==1} {R0:roles|sub(R,R0)&&mem(G,mki(R-R0,p))} (CML_INIT (G, R, p)): [G0:seqs|]



//primplement lemma_init_nil {G} {R} {A} (pf) = let 
//	prfun ih {G:seqs} {R:roles} {A:form|mem(G, mki (emp, A))} .<size(G)>. (pf: CML_INIT (G, R, A)): CML_INIT (G - mki (emp, A), R, A) =
//		case+ pf of 
//		| cml_init_zero () =/=> ()
//		| cml_init_more {G1}{R1}{A}{R2} (pf1) =>>
//			sif R2 == emp 
//			then pf1 
//			else cml_init_more {G1-mki(emp,A)}{R1}{A}{R2} (ih {G1}{R1}{A} pf1)
//in 
//	ih {G}{R}{A} pf 
//end 

(*
primplement lemma_full {U} {G} {A} () = let 
	prfun ih {U:roles} {G:seqs} {A:form} .<size(A)>. (): [m:nat] CML (U, m, nil |- G + mki(U,A)) =
		scase A of 
		| atom () => 
			let 
				prval pf = cml_init_more {nil}{emp}{A}{U} (cml_init_zero {A} ())
				prval pf = cml_axi {U}{G,mki(U,A)+nil}{A} (pf)
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
				prval pf = cml_conj_p {U}{G}{r}{U}{p,q}{i,j} (pfp, pfq)
			in 
				#[i+j+1|pf]
			end
in 
	ih {U}{G}{A} ()
end 

primplement lemma_empty {U} {G} {A} {m} (pf) = let 
	prfun ih {U:roles} {G:seqs} {A:form} {m:nat} .<m>. (pf: CML (U, m, nil |- G + mki(emp,A))): [i:nat|i <= m] CML (U, i, nil |- G) = 
		case+ pf of 
		| cml_axi {U}{G1,G2}{A1} pf1 =>
			(*
			pf1: CML_INIT (G2, U, A1)
			------------------------
			pf: G + A(emp) = G1 + G2(A1's)
			-----------------------
			goal: G
			*)
			sif A == A1
			then sif mem(G1, mki(emp,A))
				then cml_axi {U}{G1-mki(emp,A),G2}{A} pf1 
				else cml_axi {U}{G1,G2-mki(emp,A)}{A} (lemma_init_nil {G2}{U}{A} pf1)
			else let 
					prval _ = lemma_init_only {G2}{U,emp}{A1,A} pf1 
				in cml_axi {U}{G1-mki(emp,A),G2}{A1} pf1 end

		| cml_conj_n1 {U}{G1}{r}{R}{A1,B1}{m1} pf1 =>>
			(*
			pf1: G1 + A1 ? B1 + A1
			------------------------
			pf: G1 + A1 ? B1 = G + A(emp)
			----------------
			goal: G
			*)

			sif mem(G1, mki(emp,A)) 
			then let 
					(* G1 + A1?B1 + A1 => (G1-Aemp) + A1?B1 + A1 *)
					prval [i:int] pf1 = ih {U}{G1+mki(R,conj(r,A1,B1))+mki(R,A1)-mki(emp,A)}{A}{m1} pf1 
				in 
					(* (G1-Aemp) + A1?B1 *)
					cml_conj_n1 {U}{G1-mki(emp,A)}{r}{R}{A1,B1}{i} pf1 
				end
			else let 
					(* G1 + A1?B1emp + A1emp => G1 + A1emp *)
					prval [i:int] pf1 = ih {U}{G1+mki(emp,A1)}{conj(r,A1,B1)}{m1} pf1
					(* G1 + A1emp => G1 *)
					prval [i:int] pf1 = ih {U}{G1}{A1}{i} pf1 
				in 
					pf1
				end

		| cml_conj_n2 {U}{G1}{r}{R}{A1,B1}{m1} pf1 =>>
			(*
			pf1: G1 + A1 ? B1 + B1
			------------------------
			pf: G1 + A1 ? B1 = G + A(emp)
			----------------
			goal: G
			*)

			sif mem(G1, mki(emp,A)) 
			then let 
					prval [i:int] pf1 = ih {U}{G1+mki(R,conj(r,A1,B1))+mki(R,B1)-mki(emp,A)}{A}{m1} pf1 
				in 
					cml_conj_n2 {U}{G1-mki(emp,A)}{r}{R}{A1,B1}{i} pf1 
				end
			else let 
					prval [i:int] pf1 = ih {U}{G1+mki(emp,B1)}{conj(r,A1,B1)}{m1} pf1
					prval [i:int] pf1 = ih {U}{G1}{B1}{i} pf1 
				in 
					pf1
				end

		| cml_conj_p {U}{G1}{r}{R}{A1,B1}{m1,n1} (pf1, pf2) =>> 
			(*
			pf1: G1 + A1?B1 + A1   
			pf2: G1 + A1?B1 + B1
			------------------------
			pf: G1 + A1?B1 = G + A(emp)
			----------------
			goal: G
			*)

			(* since r \in R, A(emp) can't be A1?B1 *)
			let 
				prval [i:int] pf1 = ih {U}{G1+mki(R,conj(r,A1,B1))+mki(R,A1)-mki(emp,A)}{A} pf1
				prval [j:int] pf2 = ih {U}{G1+mki(R,conj(r,A1,B1))+mki(R,B1)-mki(emp,A)}{A} pf2
			in 
				cml_conj_p {U}{G1-mki(emp,A)}{r}{R}{A1,B1}{i,j} (pf1, pf2)
			end

in 
	ih {U}{G}{A}{m} pf 
end 


primplement lemma_wk {U} {G} {R} {A} {m} (pf) = let 
	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {m:nat} .<m>. (pf: CML (U, m, nil |- G)): CML (U, m, nil |- G + mki(R,A)) = 
		case+ pf of 
		| cml_axi {U}{G1,G2}{A1} pf1 => cml_axi {U}{G1+mki(R,A),G2}{A1} pf1 
		| cml_conj_n1 {U}{G1}{r}{R1}{A1,B1}{m1} pf1 => 
			cml_conj_n1 {U}{G1+mki(R,A)}{r}{R1}{A1,B1}{m1} (
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,A1)}{R}{A}{m1} pf1)
		| cml_conj_n2 {U}{G1}{r}{R1}{A1,B1}{m1} pf1 => 
			cml_conj_n2 {U}{G1+mki(R,A)}{r}{R1}{A1,B1}{m1} (
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,B1)}{R}{A}{m1} pf1)
		| cml_conj_p {U}{G1}{r}{R1}{A1,B1}{m1,n1} (pf1, pf2) => 
			cml_conj_p {U}{G1+mki(R,A)}{r}{R1}{A1,B1}{m1,n1} (
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,A1)}{R}{A} pf1, 
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,B1)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{m} pf 
end 

primplement lemma_ctr {U} {G} {R} {A} {m} (pf) = let 
	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {m:nat} .<m>. (pf: CML (U, m, nil |- G + mki(R,A) + mki(R,A))): CML (U, m, nil |- G + mki(R,A)) = 
		case+ pf of 
		| cml_axi {U}{G1,G2}{A1} pf1 => 
			sif mem(G1,mki(R,A))
			then cml_axi {U}{G1-mki(R,A),G2}{A1} pf1
			else 
				let 
					prval _ = lemma_init_is {G2}{U,R}{A1,A} pf1
				in 
					sif not (R == emp)
					then let prval _ = lemma_init_nonoverlap {G2}{U}{A1}{R,R} pf1 in false_elim () (*impossible*) end 
					else cml_axi {U}{G1,G2-mki(R,A)}{A} (lemma_init_nil {G2}{U}{A} pf1)
				end 

		| cml_conj_n1 {U}{G1}{r}{R1}{A1,B1}{m1} pf1 => 
			cml_conj_n1 {U}{G1-mki(R,A)}{r}{R1}{A1,B1}{m1} (
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,A1)-mki(R,A)-mki(R,A)}{R}{A}{m1} pf1)
		| cml_conj_n2 {U}{G1}{r}{R1}{A1,B1}{m1} pf1 => 
			cml_conj_n2 {U}{G1-mki(R,A)}{r}{R1}{A1,B1}{m1} (
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,B1)-mki(R,A)-mki(R,A)}{R}{A}{m1} pf1)
		| cml_conj_p {U}{G1}{r}{R1}{A1,B1}{m1,n1} (pf1, pf2) => 
			cml_conj_p {U}{G1-mki(R,A)}{r}{R1}{A1,B1}{m1,n1} (
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,A1)-mki(R,A)-mki(R,A)}{R}{A} pf1, 
				ih {U}{G1+mki(R1,conj(r,A1,B1))+mki(R1,B1)-mki(R,A)-mki(R,A)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{m} pf 
end 






primplement lemma_split {U} {G} {R1,R2} {A} {m} (pf) = let
 	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&(R1*R2==emp)} {A:form} {m:nat} .<size(A),m>.
 		(pf: CML (U, m, nil |- G + mki(R1+R2,A))): [i:nat] CML (U, i, nil |- G + mki(R1,A) + mki(R2,A)) = 

 		case+ pf of 
 		| cml_axi {U}{G1,G2}{p} pf0 => 
 			(*
				pf0: INIT (G2, U, p)
				--------------------
				pf: G1 + G2 = G + A(R1+R2)
				-------------------------
				goal: G + A(R1) + A(R2)
 			*)
 			sif mem (G1, mki(R1+R2, A))
 			then 
 				let 
 					prval _ = lemma_bag_add_elt {G1+G2,G} {mki(R1+R2,A)} ()
 				in 
 					cml_axi {U}{G1+mki(R1,A)+mki(R2,A)-mki(R1+R2,A),G2}{p} pf0 
 				end
 			else 
 				(*
					A == p
 				*)
 				let 
 					prval _ = lemma_init_is {G2}{U,R1+R2}{p,A} pf0 
 					prval pf0 = lemma_init_split {G2}{U}{p}{R1+R2,R1,R2} pf0
 				in 
 					cml_axi {U}{G1,G2-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{A} pf0
 				end
 		| cml_conj_n1 {U}{G0}{r0}{R0}{A0,B0}{m0} pf0 =>>
 			(*
				pf0: G0 + A0 r B0 [R0] + A0[R0]
				------------------------------
				pf: G0 + A0 r B0 [R0] = G + A[R1+R2]
				-----------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			sif mem (G0, mki(R1+R2,A))
 			then 
 				let 
 					prval [i:int] pf0 = ih {U}{G0+mki(R0,conj(r0,A0,B0))+mki(R0,A0)-mki(R1+R2,A)}{R1,R2}{A}{m0} pf0
 				in 
 					cml_conj_n1 {U}{G0+mki(R1,A)+mki(R2,A)-mki(R1+R2,A)}{r0}{R0}{A0,B0}{i} pf0
 				end
 			else 
 				(*
 					pf0: G + A0 r B0 [R1+R2] + A0[R1+R2]
 					------------------------------
 					pf:  G + A0 r B0 [R1+R2] 
 					-----------------------------------
 					goal: G + A0 r B0 [R1] + A0 r B0 [R2]
 				*)
 				let 
 					(* G + A0rB0 [R1] + A0rB0 [R2] + A0[R1] + A0[R2] *)
 					prval [i:int] pf0 = ih {U}{G+mki(R1+R2,A0)}{R1,R2}{A}{m0} pf0
 					prval [i:int] pf0 = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{A0}{i} pf0

 					prval pf = cml_conj_n1 {U}{G+mki(R1,A)+mki(R1,A0)}{r0}{R2}{A0,B0}{i} pf0
 					prval pf = cml_conj_n1 {U}{G+mki(R2,A)}{r0}{R1}{A0,B0}{i+1} pf 
 				in 
 					pf
 				end
 		 | cml_conj_n2 {U}{G0}{r0}{R0}{A0,B0}{m0} pf0 =>>
 			(*
				pf0: G0 + A0 r B0 [R0] + B0[R0]
				------------------------------
				pf: G0 + A0 r B0 [R0] = G + A[R1+R2]
				-----------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			sif mem (G0, mki(R1+R2,A))
 			then 
 				let 
 					prval [i:int] pf0 = ih {U}{G0+mki(R0,conj(r0,A0,B0))+mki(R0,B0)-mki(R1+R2,A)}{R1,R2}{A}{m0} pf0
 				in 
 					cml_conj_n2 {U}{G0+mki(R1,A)+mki(R2,A)-mki(R1+R2,A)}{r0}{R0}{A0,B0}{i} pf0
 				end
 			else 
 				(*
 					pf0: G + A0 r B0 [R1+R2] + B0[R1+R2]
 					------------------------------
 					pf:  G + A0 r B0 [R1+R2] 
 					-----------------------------------
 					goal: G + A0 r B0 [R1] + A0 r B0 [R2]
 				*)
 				let 
 					(* G + A0rB0 [R1] + A0rB0 [R2] + B0[R1+R2] *)
 					prval [i:int] pf0 = ih {U}{G+mki(R1+R2,B0)}{R1,R2}{A}{m0} pf0
 					(* G + A0rB0 [R1] + A0rB0 [R2] + B0[R1] + B0[R2] *)
 					prval [i:int] pf0 = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{B0}{i} pf0

 					prval pf = cml_conj_n2 {U}{G+mki(R1,A)+mki(R1,B0)}{r0}{R2}{A0,B0}{i} pf0
 					prval pf = cml_conj_n2 {U}{G+mki(R2,A)}{r0}{R1}{A0,B0}{i+1} pf 
 				in 
 					pf
 				end
 		| cml_conj_p {U}{G0}{r0}{R0}{A0,B0}{m0,n0} (pf0, pf1) =>>
 			(*
				pf0: G0 + A0rB0[R0] + A0[R0]
				pf1: G0 + A0rB0[R0] + B0[R0]
				-----------------------------
				pf:  G0 + A0rB0[R0] = G + A[R1+R2]
 			*)
 			sif mem (G0, mki(R1+R2,A))
 			then 
 				let 
 				 	prval [i:int] pf0 = ih {U}{G0+mki(R0,conj(r0,A0,B0))+mki(R0,A0)-mki(R1+R2,A)}{R1,R2}{A}{m0} pf0
 					prval [j:int] pf1 = ih {U}{G0+mki(R0,conj(r0,A0,B0))+mki(R0,B0)-mki(R1+R2,A)}{R1,R2}{A}{n0} pf1
 				in 
 					cml_conj_p {U}{G0+mki(R1,A)+mki(R2,A)-mki(R1+R2,A)}{r0}{R0}{A0,B0}{i,j} (pf0, pf1)
 				end
 			else 
 				(*
				pf0: G + A0rB0[R1+R2] + A0[R1+R2]
				pf1: G + A0rB0[R1+R2] + B0[R1+R2]
				-----------------------------
				pf:  G + A0rB0[R1+R2]
 				*)
 				let 
 					(* G + A0B0[R1] + A0B0[R2] + A0[R1] + A0[R2] *)
 					prval [i:int] pf0 = ih {U}{G+mki(R1+R2,A0)}{R1,R2}{A}{m0} pf0
 					prval [i:int] pf0 = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{A0}{i} pf0

 					(* G + A0B0[R1] + A0B0[R2] + B0[R1] + B0[R2] *)
 					prval [j:int] pf1 = ih {U}{G+mki(R1+R2,B0)}{R1,R2}{A}{n0} pf1
 					prval [j:int] pf1 = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{B0}{j} pf1
 				in 
 					sif mem(R1,mk(r0))
 					then  
 						let 
		 					(* G + A0B0[R1] + A0B0[R2] + A0[R1] *)
		 					prval pf0 = cml_conj_n1 {U}{G+mki(R1,A)+mki(R1,A0)}{r0}{R2}{A0,B0}{i} pf0
		 					(* G + A0B0[R1] + A0B0[R2] + B0[R1] *)
		 					prval pf1 = cml_conj_n2 {U}{G+mki(R1,A)+mki(R1,B0)}{r0}{R2}{A0,B0}{j} pf1
		 				in 
		 					cml_conj_p {U}{G+mki(R2,A)}{r0}{R1}{A0,B0}{i+1,j+1} (pf0, pf1)
		 				end 
		 			else 
		 				let 
		 					(* G + A0B0[R1] + A0B0[R2] + A0[R2] *)
		 					prval pf0 = cml_conj_n1 {U}{G+mki(R2,A)+mki(R2,A0)}{r0}{R1}{A0,B0}{i} pf0
		 					(* G + A0B0[R1] + A0B0[R2] + B0[R2] *)
		 					prval pf1 = cml_conj_n2 {U}{G+mki(R2,A)+mki(R2,B0)}{r0}{R1}{A0,B0}{j} pf1
		 				in 
		 					cml_conj_p {U}{G+mki(R1,A)}{r0}{R2}{A0,B0}{i+1,j+1} (pf0, pf1)
		 				end 
		 		end

in 
	ih {U}{G}{R1,R2}{A}{m} pf 
end 


*)


primplement lemma_2cut {U} {G} {R1,R2} {A} {m,n} (fst, snd) = let 
(*
 	prfun lemma {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {R0:roles|sub(R,R0)&&mem(G,mki(R0,A))} {m:nat} .<m>. 
 		(pf: CML (U, m, nil |- G + mki(R,A))): [i:int] CML (U, i, nil |- G + mki(R-R0,A)) = let 
 			prval [i:int] pf = lemma_split {U}{G}{R-R0,R0}{A}{m} pf 
 		in 
 			lemma_ctr {U}{G+mki(R-R0,A)-mki(R0,A)}{R0}{A}{i} pf 
 		end 

	extern praxi lemma_set {g,g1:set|sub(g,g1)} {s:set|sub(g1,s)} (): [(g-g1)==(g-s)-(g1-s)] unit_p
	prval _ = $solver_assert lemma_set 

	prfun aux {U:roles} {G,Gi:seqs} {R,Ri:roles|sub(U,Ri)&&sub(Ri,R)} {p:form|size(p)==1&&mem(Gi,mki(Ri-R,p))} {m:nat} .<size(R)>. 
		(init: CML_INIT (Gi, Ri, p), pf: CML (U, m, nil |- G + Gi + mki(R,p))): CML (U, m, nil |- G + Gi) = 
		case+ init of 
		| cml_init_zero {p} () => pf 
		| cml_init_more {Gii}{Rii}{p}{r} init => 
			sif sub (R, r)
			then 
				let 
					prval _ = lemma_set {Ri,R}{r} ()
				in 
					aux {U}{G,Gii}{R-r,Rii}{p}{m} (init, lemma {U}{G+Gi}{R}{p}{r} pf)
				end
			else aux {U}{G,Gii}{R,Rii}{p}{m} (init, pf)
*)

	extern praxi lemma {U:roles} {G,Gi:seqs} {R,Ri:roles|sub(U,Ri)&&sub(Ri,R)} {p:form|size(p)==1&&mem(Gi,mki(Ri-R,p))} {m:nat} 
		(init: CML_INIT (Gi, Ri, p), pf: CML (U, m, nil |- G + Gi + mki(R,p))): CML (U, m, nil |- G + Gi)


	prfun ih {U:roles} {G:seqs} {R1,R2:roles|fulljoin(U,R1,R2)} {A:form} {m,n:nat} .<size(A),m,n>.
		(fst: CML (U, m, nil |- G + mki(R1,A)), snd: CML (U, n, nil |- G + mki(R2,A))): [i:nat] CML (U, i, nil |- G) = 

		case- (fst, snd) of 
		| (cml_axi {U}{G0,Gi0}{p} pf0, _) =>
			(*
				pf0: CML_INIT (Gi0, U, p)
				------------------------
				fst: G + A(R) = G0 + Gi0(p's)   snd: G + A(U-R)
				-----------------------------------------------
				goal: G
			*)
			sif mem (G0, mki (R1, A)) 
			then cml_axi {U}{G0-mki(R1,A),Gi0}{p} pf0 (* not principal in fst *)
			else (* principal in fst *)

				(* A(R) is in Gi0, so A == p *)
				let 
					prval _ = lemma_init_is {Gi0}{U,R1}{p,A} pf0 	
				in case+ snd of 
					| cml_axi {U}{G1,Gi1}{p} pf1 => 
						sif mem (G1, mki (R2, A))
						then cml_axi {U}{G1-mki(R2,A),Gi1}{p} pf1 (* not principal in snd *)
						else 
							(*
								G + p[R]   = G0 + Gi0 = G0 + ps[U-R] + p[R]   
								G + p[U-R] = G1 + Gi1 = G1 + ps[R]   + p[U-R] 
								sub (G, ps[U-R])
								sub (G, ps[R])

								G = G' + ps[R] + ps[U-R]
								G' = G0 - (Gi1 - p[U-R]) = G1 - (Gi0 - p[R])
							*)
							let 
								prval _ = lemma_init_is {Gi1}{U,R2}{p,A} pf1 	

//								extern praxi lemma_bag1 {ga1,gb1,ga2,gb2:bag|ga1+ga2==gb1+gb2&&(ga2*gb2==nil)} (): [sub(ga1,gb2)&&sub(gb1,ga2)] unit_p
								extern praxi lemma_bag2 {g,g1,g2:bag} {e:belt|g+e==g1+g2} (): [g==g1+g2-e] unit_p
//								extern praxi lemma_bag3 {g,g1,g2:bag} {e:belt|g+e==g1+g2} (): [(mem(g1,e)&&sub(g,g2)&&sub(g,g1-e))||(mem(g2,e)&&sub(g,g1)&&sub(g,g2-e))] unit_p
//								prval _ = $solver_assert lemma_bag1
								prval _ = $solver_assert lemma_bag2
//								prval _ = $solver_assert lemma_bag3

								extern praxi lemma_bag4 {g1,g2,g3:bag} (): [(g1+g2)+g3==g1+(g2+g3)] unit_p
								extern praxi lemma_bag5 {g1,g2:bag} (): [g1+g2==g2+g1] unit_p
								extern praxi lemma_bag6 {g1,g2,g3:bag|sub(g1,g2)} (): [g1-g2+g3==g1+g3-g2] unit_p

								prval _ = $solver_assert lemma_bag4
								prval _ = $solver_assert lemma_bag5
								prval _ = $solver_assert lemma_bag6

//								prval _ = $solver_assert lemma_bag_eq_eq	

//								prval _ = lemma_bag2 {G,G1,Gi1}{mki(U-R,p)} ()
//								prval _ = lemma_bag2 {G,G0,Gi0}{mki(R,p)} ()
//								prval _ = lemma_bag3 {G,G1,Gi1}{mki(U-R,p)} ()
//								prval _ = lemma_bag3 {G,G0,Gi0}{mki(R,p)} ()

//								prval _ = lemma_bag1 {G0,G1,Gi0-mki(R,p),Gi1-mki(U-R,p)} ()


								extern praxi _asrt 
									{U,R1,R2:roles|fulljoin(U,R1,R2)} {G,G0,Gi0,G1,Gi1:seqs} {p:form|(size(p)==1)&&(G+mki(R1,p)==G0+Gi0)&&(G+mki(R2,p)==G1+Gi1)} 
									(): [sub(G1,Gi0-mki(R1,p))&&sub(G0,Gi1-mki(R2,p))] unit_p

								prval _ = _asrt {U,R1,R2} {G,G0,Gi0,G1,Gi1} {p} ()

								prval pfi = lemma_init_replace {Gi0}{U}{p}{(Gi0-mki(R1,p))+(Gi1-mki(R2,p))} pf0

							in 
								cml_axi {U}{G1-(Gi0-mki(R1,p)), (Gi0-mki(R1,p)) + (Gi1-mki(R2,p))}{p} pfi 
							end 


					(* A == p, so couln't be a principal formula *)
					| cml_conj_n1 {U}{G1}{r1}{R1}{A1,B1}{m1} pf1 =>> cml_conj_n1 {U}{G1-mki(R2,A)}{r1}{R1}{A1,B1}{m1} pf1
					| cml_conj_n2 {U}{G1}{r1}{R1}{A1,B1}{m1} pf1 =>> cml_conj_n2 {U}{G1-mki(R2,A)}{r1}{R1}{A1,B1}{m1} pf1
					| cml_conj_p  {U}{G1}{r1}{R1}{A1,B1}{m1,n1} (pf10, pf11) =>> cml_conj_p {U}{G1-mki(R2,A)}{r1}{R1}{A1,B1}{m1,n1} (pf10, pf11)

					//lemma {U}{G1,Gi-mki(R,p)}{U-R,U}{p}{n} (lemma_init_del {Gi}{U}{p}{R} pf0, snd)
				end 

		| (cml_conj_n1 {U}{G0}{r0}{R0}{A0,B0}{m0} pf0, _) =>>
			(*
				pf0: G0 + A0r0B0[R0] + A0[R0]
				----------------------------------------------------
				fst: G0 + A0r0B0[R0] = G + A[R1]     snd: G + A[R2]
				-----------------------------------------------------
				goal: G
			*)

			sif mem (G0, mki (R1, A))
			then cml_conj_n1 {U}{G0-mki(R1,A)}{r0}{R0}{A0,B0}{m0} pf0 
			else 
				(*
					A = A0r0B0
					R0 = R1
					G0 = G

					pf0: G + A0r0B0[R1] + A0[R1]
					----------------------------------------------------
					fst: G + A0r0B0[R1]          snd: G + A0r0B0[R2]
					-----------------------------------------------------
					goal: G
				*)

in 
	ih {U}{G}{R1,R2}{A}{m,n} (fst, snd)
end




////
primplement lemma_3cut {U} {G} {R1,R2,R3} {A} {m,n,l} (fst, snd, thd) = let 
	prfun ih {U:roles} {G:seqs} {R1,R2,R3:roles|fulljoin(U,R1,R2,R3)} {A:form} {m,n,l:nat} 
		(fst: CML (U, m, nil |- G + mki(R1,A)), snd: CML (U, n, nil |- G + mki(R2,A)), thd: CML (U, l, nil |- G + mki(R3,A))): [i:nat] CML (U, i, nil |- G) = 

		case+ (fst, snd) of 
		| 


////
primplement lemma_35 {U} {G} {R} {A} () = 
	cml_axi {U}{G,nil+mki(R,A)+mki(U-R,A)}{A} (
		cml_init_more {mki(R,A)+nil}{R}{A}{U-R} (
			cml_init_more {nil}{emp}{A}{R} (
				cml_ini
	)



primplement lemma_36 {U} {G} {R} {A} {m,n} (fst, snd) = let 
	prval [i:int] pf = lemma_37 {U}{G}{R,U-R}{A}{m,n} (fst, snd)
	prval [i:int] pf = lemma_32 {U}{G}{A}{i} pf 
in 
	pf 
end 


primplement lemma_39 {U} {G} {R1,R2,R3} {A} {m,n,l} (fst, snd, thd) = 

//primplement lemma_38 {U} {G} {R1,R2} {A} {m} (pf) = 

//primplement lemma_39 {U} {G} {R1,R2} {A} {m,n,l} (fst, snd, thd) = let 
//	(* A(R1*R2) *)
//	prval [i:int] pf = lemma_37 {U}{G}{R1,R2}{A}{m,n} (fst, snd)
//in 
//	lemma_36 {U}{G}{R1*R2}{A}{i,l} (pf, thd)
//end
	



