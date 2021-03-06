staload "cml_disj.sats"

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
prval _ = $solver_assert lemma_form_size_conn



primplement lemma_init_member {U}{U0}{G}{p}{R}{A} (init) = 
	case+ init of 
	| cmld_init_zero {U}{p} () => false 
	| cmld_init_more {U}{r}{g}{p}{r0} init => 
		sif mki(r0,p) == mki(R,A)
		then true 
		else lemma_init_member {U}{r}{g}{p}{R}{A} init


primplement lemma_init_remove {U}{U0}{G}{p}{R}{A} (init) = let 
	prval _ = lemma_init_form {U}{U0}{G}{p}{R}{A} init
in
	case+ init of 
	| cmld_init_zero {U}{p} () =/=> ()
	| cmld_init_more {U}{r}{g}{p}{r0} pf => 
		sif r0 == R 
		then pf 
		else let 
			prval _ = lemma_init_role {U}{U0}{G}{p}{R,r0} init 
		in 
			cmld_init_more {U}{r-(U-R)}{g-mki(R,A)}{p}{r0} (lemma_init_remove {U}{r}{g}{p}{R}{A} pf)
		end
end

primplement lemma_init_merge {U}{U1,U2}{G1,G2}{p} (fst, snd) = 
	case+ fst of 
	| cmld_init_zero {U}{p} () => snd 
	| cmld_init_more {U}{r}{g}{p}{r0} fst => cmld_init_more {U}{r+U2}{g+G2}{p}{r0} (lemma_init_merge {U}{r,U2}{g,G2}{p} (fst, snd))



primplement lemma_3cut {U}{G}{R1,R2,R3}{A}{M,N,L} (fst, snd, trd) = let 
	prval [i:int] pf = lemma_2cut_spill {U}{G}{R1,R2}{A}{M,N} (fst, snd)
in 
	lemma_2cut {U}{G}{R1+R2,R3}{A}{i,L} (pf, trd)
end


primplement lemma_empty {U}{G}{A} () = let 
	prfun ih {U:roles} {G:seqs} {A:form} .<size(A)>. (): [m:nat] CMLD (U, m, nil |- G + mki(emp,A)) =
		scase A of 
		| atom () => 
			let 
				prval pf = cmld_init_more {U}{emp}{nil}{A}{emp} (cmld_init_zero {U}{A} ())
				prval pf = cmld_axi {U}{G+mki(emp,A)}{mki(emp,A)+nil}{A} (pf)
			in 
				#[0|pf]
			end 
		| conn (r, p, q) => 
			let 
				(* assume that r always doesn't belongs to U *)
				extern praxi _asrt {U:roles} {r:role} (): [mem(U,mk(r))] unit_p
				prval _ = _asrt {U}{r} ()

				prval [i:int] pfp = ih {U}{G}{p} ()
				prval [j:int] pfq = ih {U}{G}{q} ()

				prval pfp = lemma_wk {U}{G+mki(emp,p)}{emp}{conn(r,p,q)}{i} pfp 
				prval pfq = lemma_wk {U}{G+mki(emp,q)}{emp}{conn(r,p,q)}{j} pfq

				prval pf = cmld_conn_n {U}{G+mki(emp,conn(r,p,q))}{emp}{r}{p,q}{i,j} (pfp, pfq)
			in 
				#[i+j+1|pf]
			end
in 
	ih {U}{G}{A} ()
end 


primplement lemma_full {U}{G}{A}{M} (pf) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {A:form} {M:nat} .<size(A),M>. (pf: CMLD (U, M, nil |- G + mki(U,A))): [i:nat|i <= M] CMLD (U, i, nil |- G) = 
		case+ pf of 
		| cmld_axi {U}{g}{gi}{p} init =>
			sif mem (g-gi, mki(U,A))
			then cmld_axi {U}{g-mki(U,A)}{gi}{p} init
			else cmld_axi {U}{g-mki(U,A)}{gi-mki(U,A)}{p} (lemma_init_remove {U}{U}{gi}{p}{U}{A} init)

		| cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			(*
				pf0: g(conn(rr,a,b)[r]) + a[r]
				-----------------------------
				pf: g = G + A[]
				----------------
				goal: G
			*)
			if ~is_principal {mki(r,conn(rr,a,b))}{mki(U,A)} ()
			then 
				let prval [i:int] pf0 = ih {U}{G+mki(r,a)}{A}{m} pf0 
				in cmld_conn_p1 {U}{g-mki(U,A)}{r}{rr}{a,b}{i} pf0 end
			else
				let 
					prval [i:int] pf0 = ih {U}{G+mki(r,a)}{A}{m} pf0
					prval [i:int] pf0 = ih {U}{G}{a}{i} pf0 
				in 
					pf0
				end

		| cmld_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			if ~is_principal {mki(r,conn(rr,a,b))}{mki(U,A)} ()
			then 
				let prval [i:int] pf0 = ih {U}{G+mki(r,b)}{A}{m} pf0 
				in cmld_conn_p2 {U}{g-mki(U,A)}{r}{rr}{a,b}{i} pf0 end
			else
				let 
					prval [i:int] pf0 = ih {U}{G+mki(r,b)}{A}{m} pf0
					prval [i:int] pf0 = ih {U}{G}{b}{i} pf0 
				in 
					pf0
				end

		| cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
			let 
				prval [i:int] pf0 = ih {U}{g+mki(r,a)-mki(U,A)}{A} pf0
				prval [j:int] pf1 = ih {U}{g+mki(r,b)-mki(U,A)}{A} pf1
			in 
				cmld_conn_n {U}{g-mki(U,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
			end

in 
	ih {U}{G}{A}{M} pf 
end 

primplement lemma_id {U}{G}{R1,R2}{A} () = lemma_split {U}{G}{R1,R2}{A} (lemma_empty {U}{G}{A} ())


primplement lemma_2cut_spill {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 
	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(R1,R2)} {A:form} {M,N:nat} .<size(A),M+N>.
		(fst: CMLD (U, M, nil |- G + mki(R1,A)), snd: CMLD (U, N, nil |- G + mki(R2,A))): [I:nat] CMLD (U, I, nil |- G + mki(R1+R2,A)) = 

		sif is_atom A 
		then 
			case+ (fst, snd) of 
			| (cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				(*
					pf: g(conn(rr,a,b)[r]) + a[r]                           
					-----------------------------                           
					fst: G + A[R1] = g                      snd: G + A[R2]
					-------------------------------------------------------
					goal: G + A[R1*R2]
				*)
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cmld_conn_p1 {U}{g-mki(R1,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cmld_conn_p2 {U}{g-mki(R1,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cmld_conn_p1 {U}{g-mki(R2,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_ar, pf)
				in 
					cmld_conn_p2 {U}{g-mki(R2,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cmld_conn_n {U}{g-mki(R1,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cmld_conn_n {U}{g-mki(R2,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cmld_axi {U}{g1}{gi1}{p1} init1, cmld_axi {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{U}{gi1}{p1}{R1}{A} init1
				then cmld_axi {U}{g1-mki(R1,A)+mki(R1+R2,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{U}{gi2}{p2}{R2}{A} init2 
				then cmld_axi {U}{g2-mki(R2,A)+mki(R1+R2,A)}{gi2}{p2} init2
				else
					(*
						init1: CML_INIT (U,gi1,A)         init2: CML_INIT (U,gi2,A)
						--------------------------        ---------------------------
						fst: G + A[R1] = g1(gi1(A[R1]))   snd: G + A[R2] = g2(gi2(A[R2]))
						-----------------------------------------------------------------------------------------
						goal: G + A[R1+R2]

						G + A[R1] = g1' + gi1 (A[R1])
						G + A[R2] = g2' + gi2 (A[R2])
					*)
					let 
						prval _ = lemma_init_form {U}{U}{gi1}{p1}{R1}{A} init1
						prval _ = lemma_init_form {U}{U}{gi2}{p2}{R2}{A} init2
						prval init1 = lemma_init_remove {U}{U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{U}{gi2}{p2}{R2}{A} init2 
						prval _ = lemma_init_seqs {U}{U-(U-R1),U-(U-R2)}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)

						(* init = U-R1 + U-R2, missing R1+R2 right now *)
						prval init = lemma_init_merge {U}{U-(U-R1),U-(U-R2)}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)

						(* prove R1+R2 + U-R1 + U-R2 = U, all disjoint *)
						prval _ = lemma_set_com_demorgan {U,U-(U-R1),U-(U-R2)} ()
						(* prove A[R1+R2] is not in gi1-A[R1] or gi2-A[R2] *)
						prval _ = lemma_init_role_neg {U}{(U-(U-R1))+(U-(U-R2))}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A}{R1+R2}{A} (init)

						(* add back A[R1+R2] *)
						prval init = cmld_init_more {U}{(U-(U-R1))+(U-(U-R2))}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A}{R1+R2} init
					in 
						cmld_axi {U}{G+mki(R1+R2,A)}{(gi1-mki(R1,A))+(gi2-mki(R2,A))+mki(R1+R2,A)}{A} init
					end 
		else
			case+ (fst, snd) of 
			| (cmld_axi {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{U}{gi1}{p1}{R1}{A} init in cmld_axi {U}{g1-mki(R1,A)+mki(R1+R2,A)}{gi1}{p1} init end
			| (_, cmld_axi {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{U}{gi2}{p2}{R2}{A} init in cmld_axi {U}{g2-mki(R2,A)+mki(R1+R2,A)}{gi2}{p2} init end

			| (cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cmld_conn_p1 {U}{g-mki(R1,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cmld_conn_p2 {U}{g-mki(R1,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cmld_conn_p1 {U}{g-mki(R2,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					cmld_conn_p2 {U}{g-mki(R2,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R1,A)} () =>   
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cmld_conn_n {U}{g-mki(R1,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R2,A)} () =>   
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cmld_conn_n {U}{g-mki(R2,A)+mki(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cmld_conn_p1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, cmld_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
													   pf21: G + conn(rr,a,b)[R2] + a[R2] 
					pf1: G + conn(rr,a,b)[R1] + a[R1]  pf22: G + conn(rr,a,b)[R2] + b[R2]                        
					---------------------------------  ---------------------------------                         
					fst: G + conn(rr,a,b)[R1] = g1     snd:  G + conn(rr,a,b)[R2] = g2
					--------------------------------------------------------------------
					goal: G + A[R1+R2]

					A is principal in both
				*)
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + a1[R2], pf21) = G + a[R2] + A[R1+R2] *)
					prval fst_aR2 = lemma_wk {U}{g1}{R2}{a} fst 
					prval [i:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conn(rr,a,b)}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] + A[R1+R2] *)
					prval snd_aR1 = lemma_wk {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conn(rr,a,b)}{m1,N} (pf1, snd_aR1)

					(* cut (G_aR1, G_aR2) = G + a[R1+R2] + A[R1+R2] *)
					prval [k:int] pf = ih {U}{G+mki(R1+R2,A)}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				in 
					cmld_conn_p1 {U}{G+mki(R1+R2,A)}{R1+R2}{rr}{a,b}{k} pf 
				end 

			| (cmld_conn_p2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, cmld_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conn(rr,a,b)}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conn(rr,a,b)}{n1,N} (pf1, snd_bR1)
					
					prval [k:int] pf = ih {U}{G+mki(R1+R2,A)}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				in 
					cmld_conn_p2 {U}{G+mki(R1+R2,A)}{R1+R2}{rr}{a,b}{k} pf
				end 

			| (cmld_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cmld_conn_p1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
					pf11: G + conn(rr,a,b)[R1] + a[R1] 								    
					pf12: G + conn(rr,a,b)[R1] + b[R1]   pf2: G + conn(rr,a,b)[R2] + a[R2]                          
					----------------------------------   ---------------------------------                          
					fst:  G + conn(rr,a,b)[R1] = g1      snd: G + conn(rr,a,b)[R2] = g2     
					--------------------------------------------------------------------
					goal: G + A[R1+R2]

					A is principal in both
				*)
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + a[R1], pf11) = G + a[R1] + A[R1+R2] *)
					prval snd_aR1 = lemma_wk {U}{g2}{R1}{a} snd 
					prval [i:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conn(rr,a,b)}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] + A[R1+R2] *)
					prval fst_aR2 = lemma_wk {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conn(rr,a,b)}{M,m2} (fst_aR2, pf2)
				
					prval [k:int] pf = ih {U}{G+mki(R1+R2,A)}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				in 
					cmld_conn_p1 {U}{G+mki(R1+R2,A)}{R1+R2}{rr}{a,b}{k} pf 
				end 

			| (cmld_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cmld_conn_p2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conn(rr,a,b)}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conn(rr,a,b)}{M,n2} (fst_bR2, pf2)
					
					prval [k:int] pf = ih {U}{G+mki(R1+R2,A)}{R1,R2}{b}{i,j} (G_bR1, G_bR2)
				in 
					cmld_conn_p2 {U}{G+mki(R1+R2,A)}{R1+R2}{rr}{a,b}{k} pf
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

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,R1,R2)} {A:form} {M,N:nat} .<size(A),M+N>. 
		(fst: CMLD (U, M, nil |- G + mki(R1,A)), snd: CMLD (U, N, nil |- G + mki(R2,A))): [I:nat] CMLD (U, I, nil |- G) = 

		sif not (is_atom A) 
		then 
			case+ (fst, snd) of 
			| (cmld_axi {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{U}{gi1}{p1}{R1}{A} init in cmld_axi {U}{g1-mki(R1,A)}{gi1}{p1} init end
			| (_, cmld_axi {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{U}{gi2}{p2}{R2}{A} init in cmld_axi {U}{g2-mki(R2,A)}{gi2}{p2} init end

			| (cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cmld_conn_p1 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R1,A)} () => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cmld_conn_p2 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cmld_conn_p1 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R2,A)} () =>  
				let 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					cmld_conn_p2 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R1,A)} () =>   
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cmld_conn_n {U}{g-mki(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mki(r,conn(rr,a,b))}{mki(R2,A)} () =>   
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cmld_conn_n {U}{g-mki(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cmld_conn_p1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, cmld_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
													   pf21: G + conn(rr,a,b)[R2] + a[R2] 
					pf1: G + conn(rr,a,b)[R1] + a[R1]  pf22: G + conn(rr,a,b)[R2] + b[R2]                        
					---------------------------------  ---------------------------------                         
					fst: G + conn(rr,a,b)[R1] = g1     snd:  G + conn(rr,a,b)[R2] = g2
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
					prval [i:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conn(rr,a,b)}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] *)
					prval snd_aR1 = lemma_wk {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conn(rr,a,b)}{m1,N} (pf1, snd_aR1)
				in 
					ih {U}{G}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				end 

			| (cmld_conn_p2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, cmld_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conn(rr,a,b)}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conn(rr,a,b)}{n1,N} (pf1, snd_bR1)
				in 
					ih {U}{G}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				end 

			| (cmld_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cmld_conn_p1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				(*
					pf11: G + conn(rr,a,b)[R1] + a[R1] 								    
					pf12: G + conn(rr,a,b)[R1] + b[R1]   pf2: G + conn(rr,a,b)[R2] + a[R2]                          
					----------------------------------   ---------------------------------                          
					fst:  G + conn(rr,a,b)[R1] = g1      snd: G + conn(rr,a,b)[R2] = g2     
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
					prval [i:int] G_aR1 = ih {U}{G+mki(R1,a)}{R1,R2}{conn(rr,a,b)}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] *)
					prval fst_aR2 = lemma_wk {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mki(R2,a)}{R1,R2}{conn(rr,a,b)}{M,m2} (fst_aR2, pf2)
				in 
					ih {U}{G}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				end 

			| (cmld_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), cmld_conn_p2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mki(r1,conn(rr1,a1,b1))}{mki(R1,A)} () * is_principal {mki(r2,conn(rr2,a2,b2))}{mki(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mki(R1,b)}{R1,R2}{conn(rr,a,b)}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mki(R2,b)}{R1,R2}{conn(rr,a,b)}{M,n2} (fst_bR2, pf2)
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

		else 
			case+ (fst, snd) of 
			| (cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				(*
					pf: g(conn(rr,a,b)[r]) + a[r]                           
					-------------------------------------                           
					fst: G + A[R1] = g                      snd: G + A[R2]
					-------------------------------------------------------
					goal: G
				*)
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					cmld_conn_p1 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					cmld_conn_p2 {U}{g-mki(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					cmld_conn_p1 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, cmld_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_ar, pf)
				in 
					cmld_conn_p2 {U}{g-mki(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval snd_ar = lemma_wk {U}{G+mki(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk {U}{G+mki(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					cmld_conn_n {U}{g-mki(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval fst_ar = lemma_wk {U}{G+mki(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk {U}{G+mki(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mki(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mki(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					cmld_conn_n {U}{g-mki(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (cmld_axi {U}{g1}{gi1}{p1} init1, cmld_axi {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{U}{gi1}{p1}{R1}{A} init1
				then cmld_axi {U}{g1-mki(R1,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{U}{gi2}{p2}{R2}{A} init2 
				then cmld_axi {U}{g2-mki(R2,A)}{gi2}{p2} init2
				else
					(*
						init1: CMLd_INIT (U,gi1,A)                   init2: CMLd_INIT (U,gi2,A)
						--------------------------                  ---------------------------
						fst: G + A[R1] = g1(gi1(A[R1]))   snd: G + A[R2] = g2(gi2(A[R2]))
						-----------------------------------------------------------------------------------------
						goal: G

						G + A[R1] = g1' + gi1 (A[R1])
						G + A[R2] = g2' + gi2 (A[R2])
					*)
					let 
						prval _ = lemma_init_form {U}{U}{gi1}{p1}{R1}{A} init1
						prval _ = lemma_init_form {U}{U}{gi2}{p2}{R2}{A} init2
						prval init1 = lemma_init_remove {U}{U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{U}{gi2}{p2}{R2}{A} init2 
						prval _ = lemma_init_seqs {U}{U-(U-R1),U-(U-R2)}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)
						prval init = lemma_init_merge {U}{U-(U-R1),U-(U-R2)}{gi1-mki(R1,A),gi2-mki(R2,A)}{A} (init1, init2)
					in 
						cmld_axi {U}{G}{(gi1-mki(R1,A))+(gi2-mki(R2,A))}{A} init
					end 

in 
	ih {U}{G}{R1,R2}{A}{M,N} (fst, snd)
end 




primplement lemma_wk {U}{G}{R}{A}{M} (pf) = let 
	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} .<M>. (pf: CMLD (U, M, nil |- G)): CMLD (U, M, nil |- G + mki(R,A)) = 
		case+ pf of 
		| cmld_axi {U}{g}{gi}{p} pf => cmld_axi {U}{g+mki(R,A)}{gi}{p} pf 
		| cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf => 
			cmld_conn_p1 {U}{g+mki(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mki(r,a)}{R}{A}{m} pf)
		| cmld_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf => 
			cmld_conn_p2 {U}{g+mki(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mki(r,b)}{R}{A}{m} pf)
		| cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			cmld_conn_n {U}{g+mki(R,A)}{r}{rr}{a,b}{m,n} (
				ih {U}{g+mki(r,a)}{R}{A} pf1, 
				ih {U}{g+mki(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 


primplement lemma_ctr {U}{G}{R}{A}{M} (pf) = let 

	prfun lemma_init_car {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mki(R,A))&&not(R==U)} .<size(G)>. 
		(init: CMLD_INIT (U,U0,G,p)): [car(G,mki(R,A))==1] unit_p = 
		case+ init of 
		| cmld_init_zero {U}{p} =/=> ()
		| cmld_init_more {U}{u}{g}{p}{r} (init) => 
			sif not (R == r)
			then let prval _ = lemma_bag_size_add {g}{mki(r,p)} () in lemma_init_car {U}{u}{g}{p}{R}{A} init end
			else lemma_init_role_neg {U}{u}{g}{p}{R}{A} init

	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mki(R,A))>1} .<M>. 
		(pf: CMLD (U, M, nil |- G)): CMLD (U, M, nil |- G - mki(R,A)) = 

		case+ pf of 
		| cmld_axi {U}{g}{gi}{p} init => 
			sif mem (g-gi, mki(R,A))
			then cmld_axi {U}{g-mki(R,A)}{gi}{p} init
			else 
				let 
					prval _ = lemma_init_member {U}{U}{gi}{p}{R}{A} init 
					prval _ = lemma_init_form {U}{U}{gi}{p}{R}{A} init
				in 
					sif not (R == U)
					then let prval _ = lemma_init_car {U}{U}{gi}{p}{R}{A} init in false_elim () end
					else cmld_axi {U}{g-mki(R,A)}{gi-mki(R,A)}{p} (lemma_init_remove {U}{U}{gi}{p}{R}{A} init)
				end 
		| cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf => 
			cmld_conn_p1 {U}{g-mki(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mki(r,a)}{R}{A}{m} pf)
		| cmld_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf => 
			cmld_conn_p2 {U}{g-mki(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mki(r,b)}{R}{A}{m} pf)
		| cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			cmld_conn_n {U}{g-mki(R,A)}{r}{rr}{a,b}{m,n} (ih {U}{g+mki(r,a)}{R}{A} pf1, ih {U}{g+mki(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 


primplement lemma_split {U}{G}{R1,R2}{A}{M} (pf) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(U-R1,U-R2)} {A:form} {M:nat} .<size(A),M>. 
		(pf: CMLD (U, M, nil |- G + mki(R1*R2,A))): [I:nat] CMLD (U, I, nil |- G + mki(R1,A) + mki(R2,A)) = 

		case+ pf of 
 		| cmld_axi {U}{g}{gi}{p} init => 
 			(*
				init: init (U,U,gi,p)
				----------------------
				pf: G + A[R1*R2] = g(gi)
				------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~lemma_init_member {U}{U}{gi}{p}{R1*R2}{A} init
 			then cmld_axi {U}{g-mki(R1*R2,A)+mki(R1,A)+mki(R2,A)}{gi}{p} init
 			else 
 				let 
 					prval _ = lemma_init_form {U}{U}{gi}{p}{R1*R2}{A} init 
 					prval init = lemma_init_remove {U}{U}{gi}{p}{R1*R2}{A} init

 					prval _ = lemma_init_role_neg {U}{U-(U-(R1*R2))}{gi-mki(R1*R2,A)}{p}{R1}{A} init
 					prval init = cmld_init_more {U}{U-(U-(R1*R2))}{gi-mki(R1*R2,A)}{p}{R1} init

 					prval _ = lemma_init_role_neg {U}{U-(U-(R1*R2))+(U-R1)}{gi-mki(R1*R2,A)+mki(R1,A)}{p}{R2}{A} init 
 					prval init = cmld_init_more {U}{U-(U-(R1*R2))+(U-R1)}{gi-mki(R1*R2,A)+mki(R1,A)}{p}{R2} init
 				in 
 					cmld_axi {U}{g-mki(R1*R2,A)+mki(R1,A)+mki(R2,A)}{gi-mki(R1*R2,A)+mki(R1,A)+mki(R2,A)}{A} init
 				end

 		| cmld_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + a[r]
				------------------------------
				pf: g(conn(rr,a,b)[r]) = G + A[R1*R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,conn(rr,a,b))}{mki(R1*R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mki(r,a)}{R1,R2}{A}{m} pf0
 				in cmld_conn_p1 {U}{G+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					(* split conn(rr,a,b)[r] first, for the sake of termination checks *)
 					prval [i:int] pf = ih {U}{G+mki(r,a)}{R1,R2}{A}{m} pf0
 					(* split a[r] *)
 					prval [i:int] pf = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{a}{i} pf

 					prval pf = cmld_conn_p1 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,a)}{R1}{rr}{a,b}{i} pf
 					prval pf = cmld_conn_p1 {U}{G+mki(R1,A)+mki(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

		| cmld_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + b[r]
				------------------------------
				pf: g(conn(rr,a,b)[r]) = G + A[R1*R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,conn(rr,a,b))}{mki(R1*R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mki(r,b)}{R1,R2}{A}{m} pf0
 				in cmld_conn_p2 {U}{G+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					prval [i:int] pf = ih {U}{G+mki(r,b)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf = ih {U}{G+mki(R1,A)+mki(R2,A)}{R1,R2}{b}{i} pf

 					prval pf = cmld_conn_p2 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,b)}{R1}{rr}{a,b}{i} pf
 					prval pf = cmld_conn_p2 {U}{G+mki(R1,A)+mki(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

 		| cmld_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + a[r]
				pf1: g(conn(rr,a,b)[r]) + b[r]
				------------------------------
				pf:  g(conn(rr,a,b)[r]) = G + A[R1*R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mki(r,conn(rr,a,b))}{mki(R1*R2,A)} ()
 			then 
 				let 
 				 	prval [i:int] pf0 = ih {U}{G+mki(r,a)}{R1,R2}{A}{m} pf0
 					prval [j:int] pf1 = ih {U}{G+mki(r,b)}{R1,R2}{A}{n} pf1
 				in 
 					cmld_conn_n {U}{G+mki(R1,A)+mki(R2,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
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
 					sif mem (R1, mk(rr))
 					then  
 						let 
		 					prval pf0 = cmld_conn_p1 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,a)}{R1}{rr}{a,b}{i} pf0
		 					prval pf1 = cmld_conn_p2 {U}{G+mki(R1,A)+mki(R2,A)+mki(R2,b)}{R1}{rr}{a,b}{j} pf1
		 				in 
		 					cmld_conn_n {U}{G+mki(R1,A)+mki(R2,A)}{R2}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 			else 
		 				let 
		 					prval pf0 = cmld_conn_p1 {U}{G+mki(R1,A)+mki(R2,A)+mki(R1,a)}{R2}{rr}{a,b}{i} pf0
		 					prval pf1 = cmld_conn_p2 {U}{G+mki(R1,A)+mki(R2,A)+mki(R1,b)}{R2}{rr}{a,b}{j} pf1
		 				in 
		 					cmld_conn_n {U}{G+mki(R1,A)+mki(R2,A)}{R1}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 		end
in 
	ih {U}{G}{R1,R2}{A}{M} pf 
end 