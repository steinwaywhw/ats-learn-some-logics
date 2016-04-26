staload "./clml.sats"
infix |- 

//extern praxi lemma_consistency_test {1==2} (): unit_p

prval _ = $solver_assert lemma_bag_car_nat
prval _ = $solver_assert lemma_bag_size_nat
prval _ = $solver_assert lemma_bag_size_empty

prval _ = $solver_assert lemma_set_size_nat
prval _ = $solver_assert lemma_set_size_empty

prval _ = $solver_assert lemma_mk_iform_inj
prval _ = $solver_assert lemma_mk_iform_bij
prval _ = $solver_assert lemma_mk_role_inj
prval _ = $solver_assert lemma_mk_role_bij

prval _ = $solver_assert lemma_form_size_nat
prval _ = $solver_assert lemma_form_size_atom
prval _ = $solver_assert lemma_form_size_mconj
prval _ = $solver_assert lemma_form_size_aconj


primplement lemma_init_member {U}{G}{p}{R}{A} (init) = 
	case+ init of 
	| clml_init_zero {p} => false 
	| clml_init_more {r}{g}{p}{r0} init => 
		sif mki(r0,p) == mki(R,A)
		then true
		else lemma_init_member {r}{g}{p}{R}{A} init

primplement lemma_init_remove {U}{G}{p}{R}{A} (init) = let 
	prval _ = lemma_init_form {U}{G}{p}{R}{A} init 
in 
	case+ init of 
	| clml_init_zero {p} =/=> ()
	| clml_init_more {r}{g}{p}{r0} pf => 
		sif R == r0 
		then pf 
		else let 
			prval _ = lemma_init_role {U}{G}{p}{R,r0} init
		in 
			clml_init_more {r-R}{g-mki(R,A)}{p}{r0} (lemma_init_remove {r}{g}{p}{R}{A} pf)
		end 
end

primplement lemma_init_merge {U1,U2}{G1,G2}{p} (fst, snd) = 
	case+ fst of 
	| clml_init_zero {p} => snd 
	| clml_init_more {r}{g}{p}{r0} fst => clml_init_more {r+U2}{g+G2}{p}{r0} (lemma_init_merge {r,U2}{g,G2}{p} (fst, snd))


primplement lemma_3cut {U}{G1,G2,G3}{R1,R2,R3}{A}{M,N,L} (fst, snd, trd) = 
	(*
		G1 + A[R1]
		G2 + A[R2]
		G3 + A[R3]
	*)
	let 
		prval [i:int] split = lemma_split {U}{G3}{U-R1,U-R2}{A}{L} trd 
		prval [i:int] cut = lemma_2cut {U}{G2,G3+mki(U-R1,A)}{R2,U-R2}{A}{N,i} (snd, split)
	in 
		lemma_2cut {U}{G1,G2+G3}{R1,U-R1}{A}{M,i} (fst, cut)
	end


primplement lemma_split {U}{G}{R1,R2}{A}{M} (proof) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(R1,R2)} {A:form} {M:nat} .<size(A),M>.
		(proof: CLML (U, M, nil |- G + mki(R1+R2,A))): [I:nat] CLML (U, I, nil |- G + mki(R1,A) + mki(R2,A)) = 

		case+ proof of 
		| clml_axi {U}{g}{gi}{p} init => 
			if ~lemma_init_member {U}{gi}{p}{R1+R2}{A} init 
			then clml_axi {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{gi}{p} init 
			else 
				let 	
					prval _ = lemma_init_form {U}{gi}{p}{R1+R2}{A} init 
					prval init = lemma_init_remove {U}{gi}{p}{R1+R2}{A} init 

					prval _ = lemma_init_role_neg {U-(R1+R2)}{gi-mki(R1+R2,A)}{p}{R1}{A} init
 					prval init = clml_init_more {U-(R1+R2)}{gi-mki(R1+R2,A)}{p}{R1} init

 					prval _ = lemma_init_role_neg {U-R2}{gi-mki(R1+R2,A)+mki(R1,A)}{p}{R2}{A} init 
 					prval init = clml_init_more {U-R2}{gi-mki(R1+R2,A)+mki(R1,A)}{p}{R2} init
 				in 
 					clml_axi {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{gi-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{A} init
 				end

 		| clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf => 
 			if ~is_principal {mki(r,mconj(rr,a,b))}{mki(R1+R2,A)} ()
 			then 
 				let prval [i:int] split = ih {U}{g+mki(r,a)+mki(r,b)-mki(R1+R2,A)}{R1,R2}{A}{m} pf 
 				in clml_mconj_n {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i} split end 
 			else 
 				(*
 					                          
 					pf: G + a[R1+R2] + b[R1+R2] 
 					------------------------- 
 					proof: G + A[R1+R2] 		  
 					--------------------------
 					goal: G + A[R1] + A[R2]
 				*)
 				let 
 					prval [i:int] split = ih {U}{G+mki(R1+R2,b)}{R1,R2}{a} pf 
 					prval [i:int] split = ih {U}{G+mki(R1,a)+mki(R2,a)}{R1,R2}{b} split 
 					prval goal = clml_mconj_n {U}{G+mki(R2,a)+mki(R2,b)}{R1}{rr}{a,b}{i} split 
 					prval goal = clml_mconj_n {U}{G+mki(R1,A)}{R2}{rr}{a,b}{i+1} goal 
 				in 
 					goal
 				end

 		| clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
 			if ~is_principal {mki(r,mconj(rr,a,b))}{mki(R1+R2,A)} ()
 			then 
 				sif mem (g1, mki(R1+R2,A))
 				then 
 					let prval [i:int] split = ih {U}{g1+mki(r,a)-mki(R1+R2,A)}{R1,R2}{A}{m} pf1
 					in clml_mconj_p {U}{g1-mki(R1+R2,A)+mki(R1,A)+mki(R2,A),g2}{r}{rr}{a,b}{i,n} (split, pf2) end 
 				else 
 					let prval [i:int] split = ih {U}{g2+mki(r,b)-mki(R1+R2,A)}{R1,R2}{A}{n} pf2
 					in clml_mconj_p {U}{g1,g2-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{m,i} (pf1, split) end 
 			else 
 				(*
 					                          
 					pf1: g1 + a[R1+R2] 
 					pf2: g2 + b[R1+R2] 
 					------------------------- 
 					proof: G + A[R1+R2] 		  
 					--------------------------
 					goal: G + A[R1] + A[R2]
 				*)
 				let 
 					(* g1 + a[R1] + a[R2] *)
 					prval [i:int] split_a = ih {U}{g1}{R1,R2}{a}{m} pf1
 					(* g2 + b[R1] + b[R2] *)
 					prval [j:int] split_b = ih {U}{g2}{R1,R2}{b}{n} pf2
 				in 
 					sif mem(R1,mk(rr))
 					then 
 						let prval conj = clml_mconj_p {U}{g1+mki(R2,a),g2+mki(R2,b)}{R1}{rr}{a,b}{i,j} (split_a, split_b)
 						in clml_mconj_n {U}{g1+g2+mki(R1,A)}{R2}{rr}{a,b}{i+j+1} conj end 
 					else 
 						let prval conj = clml_mconj_p {U}{g1+mki(R1,a),g2+mki(R1,b)}{R2}{rr}{a,b}{i,j} (split_a, split_b)
 						in clml_mconj_n {U}{g1+g2+mki(R2,A)}{R1}{rr}{a,b}{i+j+1} conj end 
 				end

 		| clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf =>
 			(*
 				pf: g + a[R1+R2] 
 				------------------------- 
 				proof: G + A[R1+R2] 		  
 				--------------------------
 				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1+R2,A)} () 
 			then 
 				let prval [i:int] split = ih {U}{g+mki(r,a)-mki(R1+R2,A)}{R1,R2}{A}{m} pf 
 				in clml_aconj_n1 {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i} split end 
 			else 
 				let 
 					prval [i:int] split = ih {U}{g}{R1,R2}{a}{m} pf 
 					prval goal = clml_aconj_n1 {U}{g+mki(R2,a)}{R1}{rr}{a,b}{i} split 
 					prval goal = clml_aconj_n1 {U}{g+mki(R1,A)}{R2}{rr}{a,b}{i+1} goal
 				in 
 					goal
 				end 

 		| clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf => 
 			if ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1+R2,A)} () 
 			then 
 				let prval [i:int] split = ih {U}{g+mki(r,b)-mki(R1+R2,A)}{R1,R2}{A}{n} pf 
 				in clml_aconj_n2 {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i} split end 
 			else 
 				let 
 					prval [i:int] split = ih {U}{g}{R1,R2}{b}{n} pf 
 					prval goal = clml_aconj_n2 {U}{g+mki(R2,b)}{R1}{rr}{a,b}{i} split 
 					prval goal = clml_aconj_n2 {U}{g+mki(R1,A)}{R2}{rr}{a,b}{i+1} goal
 				in 
 					goal
 				end 

 		| clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
 			(*
 				pf1: g + a[R1+R2] 
 				pf2: g + b[R1+R2]
 				------------------------- 
 				proof: G + A[R1+R2] 		  
 				--------------------------
 				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1+R2,A)} ()
 			then 
 				let 
 					prval [i:int] split_pf1 = ih {U}{g+mki(r,a)-mki(R1+R2,A)}{R1,R2}{A}{m} pf1 
 					prval [j:int] split_pf2 = ih {U}{g+mki(r,b)-mki(R1+R2,A)}{R1,R2}{A}{n} pf2 
 				in 
 					clml_aconj_p {U}{g-mki(R1+R2,A)+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i,j} (split_pf1, split_pf2)
 				end 
 			else 
 				let 
 					(* g + a[R1] + a[R2] *)
 					prval [i:int] split_a = ih {U}{g}{R1,R2}{a}{m} pf1 
 					(* g + b[R1] + b[R2] *)
 					prval [j:int] split_b = ih {U}{g}{R1,R2}{b}{n} pf2 
 				in 
 					sif mem (R1, mk(rr))
 					then 
 						let 
 							prval pf1 = clml_aconj_n1 {U}{g+mki(R1,a)}{R2}{rr}{a,b}{i} split_a 
 							prval pf2 = clml_aconj_n2 {U}{g+mki(R1,b)}{R2}{rr}{a,b}{j} split_b
 						in 
 							clml_aconj_p {U}{g+mki(R2,A)}{R1}{rr}{a,b}{i+1,j+1} (pf1, pf2)
 						end 
 					else 
 						let 
 							prval pf1 = clml_aconj_n1 {U}{g+mki(R2,a)}{R1}{rr}{a,b}{i} split_a 
 							prval pf2 = clml_aconj_n2 {U}{g+mki(R2,b)}{R1}{rr}{a,b}{j} split_b
 						in 
 							clml_aconj_p {U}{g+mki(R1,A)}{R2}{rr}{a,b}{i+1,j+1} (pf1, pf2)
 						end 
 				end
in 
	ih {U}{G}{R1,R2}{A}{M} proof 
end 


primplement lemma_2cut_spill {U}{G1,G2}{R1,R2}{A}{M,N} (fst, snd) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G1,G2:seqs} {R1,R2:roles|sub(U,R1)&&sub(U,R2)&&disj(U-R1,U-R2)} {A:form} {M,N:nat} .<size(A),M+N>.
		(fst: CLML (U, M, nil |- G1 + mki(R1,A)), snd: CLML (U, N, nil |- G2 + mki(R2,A))): [I:nat] CLML (U, I, nil |- G1 + G2 + mki(R1*R2,A)) = 

		sif is_atom A
		then 
			case+ (fst, snd) of 
			| (clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let prval [i:int] cut = ih {U}{g-mki(R1,A)+mki(r,a)+mki(r,b),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_mconj_n {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end

			| (clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				sif mem (g1, mki(R1,A))
				then 
					let prval [i:int] cut = ih {U}{g1+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					in clml_mconj_p {U}{g1-mki(R1,A)+G2+mki(R1*R2,A),g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{g2+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
					in clml_mconj_p {U}{g1,g2-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				let prval [i:int] cut = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_aconj_n1 {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end

			| (clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let prval [i:int] cut = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf, snd)
				in clml_aconj_n2 {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end 

			| (clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval [i:int] cut1 = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					prval [j:int] cut2 = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
				in 
					clml_aconj_p {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			| (_, clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval [i:int] cut = ih {U}{G1,g-mki(R2,A)+mki(r,a)+mki(r,b)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					clml_mconj_n {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut
				end  

			| (_, clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				sif mem (g1, mki(R2,A))
				then 
					let prval [i:int] cut = ih {U}{G1,g1+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					in clml_mconj_p {U}{g1-mki(R2,A)+G1+mki(R1*R2,A),g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{G1,g2+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
					in clml_mconj_p {U}{g1,g2-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (_, clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in clml_aconj_n1 {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end

			| (_, clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf)
				in clml_aconj_n2 {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end 

			| (_, clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval [i:int] cut1 = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					prval [j:int] cut2 = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
				in 
					clml_aconj_p {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			| (clml_axi {U}{g1}{gi1}{p1} init1, clml_axi {U}{g2}{gi2}{p2} init2) => 
				if ~lemma_init_member {U}{gi1}{p1}{R1}{A} init1 
				then clml_axi {U}{g1-mki(R1,A)+G2+mki(R1*R2,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{gi2}{p2}{R2}{A} init2 
				then clml_axi {U}{g2-mki(R2,A)+G1+mki(R1*R2,A)}{gi2}{p2} init2 
				else 
					(*
						init1: gi1                 init2: gi2
						----------                 -------------
						fst: g1' + gi1' + A[R1]    snd: g2' + gi2' + A[R2]
						--------------------------------------------
						goal: G1 + G2 + A[R1*R2]
					*)
					let 
						prval _ = lemma_init_form {U}{gi1}{p1}{R1}{A} init1 
						prval _ = lemma_init_form {U}{gi2}{p2}{R2}{A} init2

						prval init1 = lemma_init_remove {U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{gi2}{p2}{R2}{A} init2
						prval _ = lemma_init_seqs {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)
						prval init = lemma_init_merge {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)

						prval _ = lemma_set_com_demorgan {U,U-R1,U-R2} ()
						prval _ = lemma_init_role_neg {(U-R1)+(U-R2)}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A}{R1*R2}{A} init

						prval init = clml_init_more {(U-R1)+(U-R2)}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A}{R1*R2} init
					in 
						clml_axi {U}{G1+G2+mki(R1*R2,A)}{(gi1-mki(R1,A))+(gi2-mki(R2,A))+mki(R1*R2,A)}{A} init
					end 

		else 
			case+ (fst, snd) of 

			(* axiom case *)
			| (clml_axi {U}{g}{gi}{p} init, _) => 
				let prval _ = lemma_init_form_neg {U}{gi}{p}{R1}{A} init in clml_axi {U}{G1+G2+mki(R1*R2,A)}{gi}{p} init end 
			| (_, clml_axi {U}{g}{gi}{p} init) => 
				let prval _ = lemma_init_form_neg {U}{gi}{p}{R2}{A} init in clml_axi {U}{G1+G2+mki(R1*R2,A)}{gi}{p} init end 

			(* not principal in either *)
			| (clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R1,A)} () =>
				let prval [i:int] cut = ih {U}{g-mki(R1,A)+mki(r,a)+mki(r,b),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_mconj_n {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end

			| (clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R1,A)} () => 
				sif mem (g1, mki(R1,A))
				then 
					let prval [i:int] cut = ih {U}{g1+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					in clml_mconj_p {U}{g1-mki(R1,A)+G2+mki(R1*R2,A),g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{g2+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
					in clml_mconj_p {U}{g1,g2-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1,A)} ()=> 
				let prval [i:int] cut = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_aconj_n1 {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end

			| (clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1,A)} () => 
				let prval [i:int] cut = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf, snd)
				in clml_aconj_n2 {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end 

			| (clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval [i:int] cut1 = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					prval [j:int] cut2 = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
				in 
					clml_aconj_p {U}{g-mki(R1,A)+G2+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			| (_, clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R2,A)} () =>
				let prval [i:int] cut = ih {U}{G1,g-mki(R2,A)+mki(r,a)+mki(r,b)}{R1,R2}{A}{M,m} (fst, pf)
				in clml_mconj_n {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end

			| (_, clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R2,A)} () => 
				sif mem (g1, mki(R2,A))
				then 
					let prval [i:int] cut = ih {U}{G1,g1+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					in clml_mconj_p {U}{g1-mki(R2,A)+G1+mki(R1*R2,A),g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{G1,g2+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
					in clml_mconj_p {U}{g1,g2-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (_, clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R2,A)} () => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in clml_aconj_n1 {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end

			| (_, clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R2,A)} () => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf)
				in clml_aconj_n2 {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i} cut end 

			| (_, clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R2,A)} () => 
				let 
					prval [i:int] cut1 = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					prval [j:int] cut2 = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
				in 
					clml_aconj_p {U}{g-mki(R2,A)+G1+mki(R1*R2,A)}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			(* principal in both *)
			| (clml_mconj_n {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, clml_mconj_p {U}{g21,g22}{r2}{rr2}{a2,b2}{m2,n2} (pf21,pf22))
				when is_principal {mki(r1,mconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,mconj(rr2,a2,b2))}{mki(R2,A)} () => 
				(*
					                            pf21: g21 + a2[R2]
					pf1: G1 + a1[R1] + b1[R1]   pf22: g22 + b2[R2]
					-------------------------   -------------------
					fst: G1 + A[R1] 		    snd:  G2 + A[R2]
					----------------------------------------------
					goal: G1 + G2 + A[R1*R2]
				*)
				let 
					prval [i:int] cut = ih {U}{g1+mki(r1,b1),g21}{R1,R2}{a1}{m1,m2} (pf1, pf21)
					prval [i:int] cut = ih {U}{g1+g21+mki(R1*R2,a1),g22}{R1,R2}{b1}{i,n2} (cut, pf22)
				in  
					clml_mconj_n {U}{G1+G2}{R1*R2}{rr1}{a1,b1}{i} cut 
				end

			| (clml_aconj_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, clml_aconj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22))
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				(*
					                       pf21: G2 + a2[R2]
					pf1: G1 + a1[R1]       pf22: G2 + b2[R2]
					----------------       -------------------
					fst: G1 + A[R1]        snd:  G2 + A[R2]
					----------------------------------------------
					goal: G1 + G2 + A[R1*R2]
				*)
				let prval [i:int] cut = ih {U}{G1,G2}{R1,R2}{a1}{m1,m2} (pf1, pf21)
				in clml_aconj_n1 {U}{G1+G2}{R1*R2}{rr1}{a1,b1}{i} cut end 

			| (clml_aconj_n2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, clml_aconj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22))
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				let prval [i:int] cut = ih {U}{G1,G2}{R1,R2}{b1}{n1,n2} (pf1, pf22)
				in clml_aconj_n2 {U}{G1+G2}{R1*R2}{rr1}{a1,b1}{i} cut end 

			| (clml_mconj_p {U}{g11,g12}{r1}{rr1}{a1,b1}{m1,n1} (pf11,pf12), clml_mconj_n {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2)
				when is_principal {mki(r1,mconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,mconj(rr2,a2,b2))}{mki(R2,A)} () => 
				let 
					prval [i:int] cut = ih {U}{g11,g2+mki(r2,b1)}{R1,R2}{a1}{m1,m2} (pf11, pf2)
					prval [i:int] cut = ih {U}{g12,g2+g11+mki(R1*R2,a1)}{R1,R2}{b1}{n1,i} (pf12, cut)
				in 
					clml_mconj_n {U}{G1+G2}{R1*R2}{rr1}{a1,b1}{i} cut 
				end

			| (clml_aconj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), clml_aconj_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2)
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				let prval [i:int] cut = ih {U}{G1,G2}{R1,R2}{a1}{m1,m2} (pf11, pf2)
				in clml_aconj_n1 {U}{G1+G2}{R1*R2}{rr2}{a2,b2}{i} cut end

			| (clml_aconj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), clml_aconj_n2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2)
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				let prval [i:int] cut = ih {U}{G1,G2}{R1,R2}{b1}{n1,n2} (pf12, pf2)
				in clml_aconj_n2 {U}{G1+G2}{R1*R2}{rr2}{a2,b2}{i} cut end

			| (_, _) =/=>> 
				let 
					extern praxi bottom (): [false] unit_p
					prval _ = $solver_assert bottom
				in 
					()
				end 

in 
	ih {U}{G1,G2}{R1,R2}{A}{M,N} (fst, snd)
end 

primplement lemma_2cut {U}{G1,G2}{R1,R2}{A}{M,N} (fst, snd) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G1,G2:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,U-R1,U-R2)} {A:form} {M,N:nat} .<size(A),M+N>.
		(fst: CLML (U, M, nil |- G1 + mki(R1,A)), snd: CLML (U, N, nil |- G2 + mki(R2,A))): [I:nat] CLML (U, I, nil |- G1 + G2) =

		sif is_atom A
		then 
			case+ (fst, snd) of 
			| (clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				(*
					pf: g + a[r] + b[r]
					-------------------------
					fst: g + mconj(rr,a,b)[r]  snd: G2 + A[R2]
					------------------------------------------
					goal: G1 + G2
				*)
				let prval [i:int] cut = ih {U}{g-mki(R1,A)+mki(r,a)+mki(r,b),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_mconj_n {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i} cut end

			| (clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				(*
					pf1: g1 + a[r]
					pf2: g2 + b[r]
					-------------------------------
					fst: g1 + g2 + mconj(rr,a,b)[r]   snd: G2 + A[R2]
					--------------------------------------------------
					goal: G1 + G2
				*)
				sif mem (g1, mki(R1,A))
				then 
					let prval [i:int] cut = ih {U}{g1+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					in clml_mconj_p {U}{g1-mki(R1,A)+G2,g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{g2+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
					in clml_mconj_p {U}{g1,g2-mki(R1,A)+G2}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				(* 
					pf: g + a[r]
					------------------
					fst: g + aconj(rr,a,b)[r]  snd: G2 + A[R2]
					-------------------------------------------
					goal: G1 + G2
				*)
				let prval [i:int] cut = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_aconj_n1 {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i} cut end

			| (clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let prval [i:int] cut = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf, snd)
				in clml_aconj_n2 {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i} cut end 

			| (clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				(*
					pf1: g + a[r]
					pf2: g + b[r]
					-------------------------------
					fst: g + aconj(rr,a,b)[r]   snd: G2 + A[R2]
					--------------------------------------------------
					goal: G1 + G2
				*)
				let 
					prval [i:int] cut1 = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					prval [j:int] cut2 = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
				in 
					clml_aconj_p {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			| (_, clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval [i:int] cut = ih {U}{G1,g-mki(R2,A)+mki(r,a)+mki(r,b)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					clml_mconj_n {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i} cut
				end  

			| (_, clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				sif mem (g1, mki(R2,A))
				then 
					let prval [i:int] cut = ih {U}{G1,g1+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					in clml_mconj_p {U}{g1-mki(R2,A)+G1,g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{G1,g2+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
					in clml_mconj_p {U}{g1,g2-mki(R2,A)+G1}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (_, clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in clml_aconj_n1 {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i} cut end

			| (_, clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf)
				in clml_aconj_n2 {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i} cut end 

			| (_, clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval [i:int] cut1 = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					prval [j:int] cut2 = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
				in 
					clml_aconj_p {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			| (clml_axi {U}{g1}{gi1}{p1} init1, clml_axi {U}{g2}{gi2}{p2} init2) => 
				(*
					init1: gi1                 init2: gi2
					----------                 -------------
					fst: g1(gi1) = G1 + A[R1]  snd: g2(gi2) = G2 + A[R2]
					--------------------------------------------
					goal: G1 + G2
				*)
				if ~lemma_init_member {U}{gi1}{p1}{R1}{A} init1 
				then clml_axi {U}{g1-mki(R1,A)+G2}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{gi2}{p2}{R2}{A} init2 
				then clml_axi {U}{g2-mki(R2,A)+G1}{gi2}{p2} init2 
				else 
					(*
						init1: gi1                 init2: gi2
						----------                 -------------
						fst: g1' + gi1' + A[R1]    snd: g2' + gi2' + A[R2]
						--------------------------------------------
						goal: G1 + G2
					*)
					let 
						prval _ = lemma_init_form {U}{gi1}{p1}{R1}{A} init1 
						prval _ = lemma_init_form {U}{gi2}{p2}{R2}{A} init2

						prval init1 = lemma_init_remove {U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{gi2}{p2}{R2}{A} init2
						prval _ = lemma_init_seqs {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)
						prval init = lemma_init_merge {U-R1,U-R2}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)
					in 
						clml_axi {U}{G1+G2}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A} init
					end 

		else 
			case+ (fst, snd) of 

			(* axiom case *)
			| (clml_axi {U}{g}{gi}{p} init, _) => 
				let prval _ = lemma_init_form_neg {U}{gi}{p}{R1}{A} init in clml_axi {U}{G1+G2}{gi}{p} init end 
			| (_, clml_axi {U}{g}{gi}{p} init) => 
				let prval _ = lemma_init_form_neg {U}{gi}{p}{R2}{A} init in clml_axi {U}{G1+G2}{gi}{p} init end 

			(* not principal in either *)
			| (clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R1,A)} () =>
				let prval [i:int] cut = ih {U}{g-mki(R1,A)+mki(r,a)+mki(r,b),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_mconj_n {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i} cut end

			| (clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R1,A)} () => 
				sif mem (g1, mki(R1,A))
				then 
					let prval [i:int] cut = ih {U}{g1+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					in clml_mconj_p {U}{g1-mki(R1,A)+G2,g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{g2+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
					in clml_mconj_p {U}{g1,g2-mki(R1,A)+G2}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1,A)} ()=> 
				let prval [i:int] cut = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf, snd)
				in clml_aconj_n1 {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i} cut end

			| (clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1,A)} () => 
				let prval [i:int] cut = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf, snd)
				in clml_aconj_n2 {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i} cut end 

			| (clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval [i:int] cut1 = ih {U}{g+mki(r,a)-mki(R1,A),G2}{R1,R2}{A}{m,N} (pf1, snd)
					prval [j:int] cut2 = ih {U}{g+mki(r,b)-mki(R1,A),G2}{R1,R2}{A}{n,N} (pf2, snd)
				in 
					clml_aconj_p {U}{g-mki(R1,A)+G2}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			| (_, clml_mconj_n {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R2,A)} () =>
				let 
					prval [i:int] cut = ih {U}{G1,g-mki(R2,A)+mki(r,a)+mki(r,b)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					clml_mconj_n {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i} cut
				end  

			| (_, clml_mconj_p {U}{g1,g2}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,mconj(rr,a,b))}{mki(R2,A)} () => 
				sif mem (g1, mki(R2,A))
				then 
					let prval [i:int] cut = ih {U}{G1,g1+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					in clml_mconj_p {U}{g1-mki(R2,A)+G1,g2}{r}{rr}{a,b}{i,n} (cut, pf2) end
				else 
					let prval [i:int] cut = ih {U}{G1,g2+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
					in clml_mconj_p {U}{g1,g2-mki(R2,A)+G1}{r}{rr}{a,b}{m,i} (pf1, cut) end

			| (_, clml_aconj_n1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R2,A)} () => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in clml_aconj_n1 {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i} cut end

			| (_, clml_aconj_n2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R2,A)} () => 
				let prval [i:int] cut = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf)
				in clml_aconj_n2 {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i} cut end 

			| (_, clml_aconj_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,aconj(rr,a,b))}{mki(R2,A)} () => 
				let 
					prval [i:int] cut1 = ih {U}{G1,g+mki(r,a)-mki(R2,A)}{R1,R2}{A}{M,m} (fst, pf1)
					prval [j:int] cut2 = ih {U}{G1,g+mki(r,b)-mki(R2,A)}{R1,R2}{A}{M,n} (fst, pf2)
				in 
					clml_aconj_p {U}{g-mki(R2,A)+G1}{r}{rr}{a,b}{i,j} (cut1, cut2)
				end 

			(* principal in both *)
			| (clml_mconj_n {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, clml_mconj_p {U}{g21,g22}{r2}{rr2}{a2,b2}{m2,n2} (pf21,pf22))
				when is_principal {mki(r1,mconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,mconj(rr2,a2,b2))}{mki(R2,A)} () => 
				(*
					                            pf21: g21 + a2[R2]
					pf1: G1 + a1[R1] + b1[R1]   pf22: g22 + b2[R2]
					-------------------------   -------------------
					fst: G1 + A[R1] 		    snd:  G2 + A[R2]
					----------------------------------------------
					goal: G1 + G2
				*)
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1 

					prval [i:int] cut = ih {U}{g1+mki(r1,b),g21}{R1,R2}{a}{m1,m2} (pf1, pf21)
				in 
					ih {U}{g1+g21,g22}{R1,R2}{b}{i,n2} (cut, pf22)
				end

			| (clml_aconj_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, clml_aconj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22))
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				(*
					                       pf21: G2 + a2[R2]
					pf1: G1 + a1[R1]       pf22: G2 + b2[R2]
					----------------       -------------------
					fst: G1 + A[R1]        snd:  G2 + A[R2]
					----------------------------------------------
					goal: G1 + G2
				*)
				ih {U}{G1,G2}{R1,R2}{a1}{m1,m2} (pf1, pf21)

			| (clml_aconj_n2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, clml_aconj_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22))
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				ih {U}{G1,G2}{R1,R2}{b1}{n1,n2} (pf1, pf22)

			| (clml_mconj_p {U}{g11,g12}{r1}{rr1}{a1,b1}{m1,n1} (pf11,pf12), clml_mconj_n {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2)
				when is_principal {mki(r1,mconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,mconj(rr2,a2,b2))}{mki(R2,A)} () => 
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1 

					prval [i:int] cut = ih {U}{g11,g2+mki(r2,b)}{R1,R2}{a}{m1,m2} (pf11, pf2)
				in 
					ih {U}{g12,g2+g11}{R1,R2}{b}{n1,i} (pf12, cut)
				end

			| (clml_aconj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), clml_aconj_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2)
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				ih {U}{G1,G2}{R1,R2}{a1}{m1,m2} (pf11, pf2)

			| (clml_aconj_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), clml_aconj_n2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2)
				when is_principal {mki(r1,aconj(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,aconj(rr2,a2,b2))}{mki(R2,A)} () => 
				ih {U}{G1,G2}{R1,R2}{b1}{n1,n2} (pf12, pf2)

			| (_, _) =/=>> 
				let 
					extern praxi bottom (): [false] unit_p
					prval _ = $solver_assert bottom
				in 
					()
				end 

in 
	ih {U}{G1,G2}{R1,R2}{A}{M,N} (fst, snd)
end 

