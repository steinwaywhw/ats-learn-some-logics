staload "dcml.sats"



infix |- 

extern praxi lemma_consistency_test {1==2} (): unit_p

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
prval _ = $solver_assert lemma_form_size_neg


primplement lemma_init_member_c {U}{U0}{G}{p}{R}{A} (init) = 
	case+ init of 
	| dcmlc_init_zero {U}{p} () => false 
	| dcmlc_init_more {U}{r}{g}{p}{r0} init => 
		sif mkic(r0,p) == mkic(R,A)
		then true 
		else lemma_init_member {U}{r}{g}{p}{R}{A} init

primplement lemma_init_member_d {U}{U0}{G}{p}{R}{A} (init) = 
	case+ init of 
	| dcmld_init_zero {U}{p} () => false 
	| dcmld_init_more {U}{r}{g}{p}{r0} init => 
		sif mkid(r0,p) == mkid(R,A)
		then true 
		else lemma_init_member {U}{r}{g}{p}{R}{A} init

primplement lemma_init_remove_c {U}{U0}{G}{p}{R}{A} (init) = let 
	prval _ = lemma_init_form {U}{U0}{G}{p}{R}{A} init
in
	case+ init of 
	| dcmlc_init_zero {U}{p} () =/=> ()
	| dcmlc_init_more {U}{r}{g}{p}{r0} pf => 
		sif r0 == R 
		then pf 
		else let 
			prval _ = lemma_init_role {U}{U0}{G}{p}{R,r0} init 
		in 
			dcmlc_init_more {U}{r-R}{g-mkic(R,A)}{p}{r0} (lemma_init_remove {U}{r}{g}{p}{R}{A} pf)
		end
end

primplement lemma_init_remove_d {U}{U0}{G}{p}{R}{A} (init) = let 
	prval _ = lemma_init_form {U}{U0}{G}{p}{R}{A} init
in
	case+ init of 
	| dcmld_init_zero {U}{p} () =/=> ()
	| dcmld_init_more {U}{r}{g}{p}{r0} pf => 
		sif r0 == R 
		then pf 
		else let 
			prval _ = lemma_init_role {U}{U0}{G}{p}{R,r0} init 
		in 
			dcmld_init_more {U}{r-(U-R)}{g-mkid(R,A)}{p}{r0} (lemma_init_remove {U}{r}{g}{p}{R}{A} pf)
		end
end

primplement lemma_init_merge_c {U}{U1,U2}{G1,G2}{p} (fst, snd) = 
	case+ fst of 
	| dcmlc_init_zero {U}{p} () => snd 
	| dcmlc_init_more {U}{r}{g}{p}{r0} fst => dcmlc_init_more {U}{r+U2}{g+G2}{p}{r0} (lemma_init_merge {U}{r,U2}{g,G2}{p} (fst, snd))

primplement lemma_init_merge_d {U}{U1,U2}{G1,G2}{p} (fst, snd) = 
	case+ fst of 
	| dcmld_init_zero {U}{p} () => snd 
	| dcmld_init_more {U}{r}{g}{p}{r0} fst => dcmld_init_more {U}{r+U2}{g+G2}{p}{r0} (lemma_init_merge {U}{r,U2}{g,G2}{p} (fst, snd))


primplement lemma_3cut_c {U}{G}{R1,R2,R3}{A}{M,N,L} (fst, snd, trd) = let 
	prval [i:int] pf = lemma_2cut_spill_c {U}{G}{R1,R2}{A}{M,N} (fst, snd)
in 
	lemma_2cut_c {U}{G}{R1*R2,R3}{A}{i,L} (pf, trd)
end

primplement lemma_3cut_d {U}{G}{R1,R2,R3}{A}{M,N,L} (fst, snd, trd) = let 
	prval [i:int] pf = lemma_2cut_spill_d {U}{G}{R1,R2}{A}{M,N} (fst, snd)
in 
	lemma_2cut_d {U}{G}{R1+R2,R3}{A}{i,L} (pf, trd)
end

primplement lemma_full_c {U}{G}{A} () = let 
	prfun ih {U:roles} {G:seqs} {A:form} .<size(A)>. (): [m:nat] DCML (U, m, nil |- G + mkic(U,A)) =
		scase A of 
		| atom () => 
			let 
				prval pf = dcmlc_init_more {U}{emp}{nil}{A}{U} (dcmlc_init_zero {U}{A} ())
				prval pf = dcml_axi_c {U}{G+mkic(U,A)}{mkic(U,A)+nil}{A} (pf)
			in 
				#[0|pf]
			end 
		| conn (r, p, q) => 
			let 
				(* assume that r always belongs to U *)
				extern praxi _asrt {U:roles} {r:role} (): [mem(U,mk(r))] unit_p
				prval _ = _asrt {U}{r} ()

				prval [i:int] pfp = ih {U}{G}{p} ()
				prval [j:int] pfq = ih {U}{G}{q} ()

				prval pfp = lemma_wk_c {U}{G+mkic(U,p)}{U}{conn(r,p,q)}{i} pfp 
				prval pfq = lemma_wk_c {U}{G+mkic(U,q)}{U}{conn(r,p,q)}{j} pfq

				prval pf = dcml_conn_p {U}{G+mkic(U,conn(r,p,q))}{U}{r}{p,q}{i,j} (pfp, pfq)
			in 
				#[i+j+1|pf]
			end
		| neg (p) => 
			let 
				(* here, size of A is strictly smaller *)
				prval [i:int] pf = lemma_empty_d {U}{G+mkic(U,A)}{p} () 
				prval pf = dcml_neg_c {U}{G+mkic(U,A)}{U}{p}{i} pf 
			in 
				#[i+1|pf]
			end
in 
	ih {U}{G}{A} ()
end 

primplement lemma_empty_d {U}{G}{A} () = let 
	prfun ih {U:roles} {G:seqs} {A:form} .<size(A)>. (): [m:nat] DCML (U, m, nil |- G + mkid(emp,A)) =
		scase A of 
		| atom () => 
			let 
				prval pf = dcmld_init_more {U}{emp}{nil}{A}{emp} (dcmld_init_zero {U}{A} ())
				prval pf = dcml_axi_d {U}{G+mkid(emp,A)}{mkid(emp,A)+nil}{A} (pf)
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

				prval pfp = lemma_wk_d {U}{G+mkid(emp,p)}{emp}{conn(r,p,q)}{i} pfp 
				prval pfq = lemma_wk_d {U}{G+mkid(emp,q)}{emp}{conn(r,p,q)}{j} pfq

				prval pf = dcml_conn_n {U}{G+mkid(emp,conn(r,p,q))}{emp}{r}{p,q}{i,j} (pfp, pfq)
			in 
				#[i+j+1|pf]
			end
		| neg (p) => 
			let 
				(* here, size of A is strictly smaller *)
				prval [i:int] pf = lemma_full_c {U}{G+mkid(emp,A)}{p} () 
				prval pf = dcml_neg_d {U}{G+mkid(emp,A)}{emp}{p}{i} pf 
			in 
				#[i+1|pf]
			end
in 
	ih {U}{G}{A} ()
end 


primplement lemma_empty_c {U}{G}{A}{M} (proof) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {A:form} {M:nat} .<size(A),M>. (proof: DCML (U, M, nil |- G + mkic(emp,A))): [i:nat|i <= M] DCML (U, i, nil |- G) = 
		case+ proof of 
		| dcml_axi_c {U}{g}{gi}{p} init =>
			sif mem (g-gi, mkic(emp,A))
			then dcml_axi_c {U}{g-mkic(emp,A)}{gi}{p} init
			else dcml_axi_c {U}{g-mkic(emp,A)}{gi-mkic(emp,A)}{p} (lemma_init_remove {U}{U}{gi}{p}{emp}{A} init)

		| dcml_axi_d {U}{g}{gi}{p} init => 
			sif mem (g-gi, mkic(emp,A))
			then dcml_axi_d {U}{g-mkic(emp,A)}{gi}{p} init
			else let prval _ = lemma_init_form_mix {U}{U}{gi}{p}{emp}{A} init in false_elim () end 

		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf =>
			if ~is_principal {mkic(r,conn(rr,a,b))}{mkic(emp,A)} ()
			then 
				let prval [i:int] pf = ih {U}{G+mkic(r,a)}{A}{m} pf 
				in dcml_conn_n1 {U}{g-mkic(emp,A)}{r}{rr}{a,b}{i} pf end
			else
				let 
					prval [i:int] pf = ih {U}{G+mkic(r,a)}{A}{m} pf
					prval [i:int] pf = ih {U}{G}{a}{i} pf 
				in 
					pf
				end

		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf => 
			let prval [i:int] pf = ih {U}{G+mkid(r,a)}{A}{m} pf 
			in dcml_conn_p1 {U}{g-mkic(emp,A)}{r}{rr}{a,b}{i} pf end

		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf =>
			if ~is_principal {mkic(r,conn(rr,a,b))}{mkic(emp,A)} ()
			then 
				let prval [i:int] pf = ih {U}{G+mkic(r,b)}{A}{m} pf 
				in dcml_conn_n2 {U}{g-mkic(emp,A)}{r}{rr}{a,b}{i} pf end
			else
				let 
					prval [i:int] pf = ih {U}{G+mkic(r,b)}{A}{m} pf
					prval [i:int] pf = ih {U}{G}{b}{i} pf 
				in 
					pf
				end

		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf =>
			let prval [i:int] pf = ih {U}{G+mkid(r,b)}{A}{m} pf 
			in dcml_conn_p2 {U}{g-mkic(emp,A)}{r}{rr}{a,b}{i} pf end

		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) =>
			let 
				prval [i:int] pf1 = ih {U}{g+mkic(r,a)-mkic(emp,A)}{A} pf1
				prval [j:int] pf2 = ih {U}{g+mkic(r,b)-mkic(emp,A)}{A} pf2
			in 
				dcml_conn_p {U}{g-mkic(emp,A)}{r}{rr}{a,b}{i,j} (pf1, pf2)
			end

		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) =>
			let 
				prval [i:int] pf1 = ih {U}{g+mkid(r,a)-mkic(emp,A)}{A} pf1
				prval [j:int] pf2 = ih {U}{g+mkid(r,b)-mkic(emp,A)}{A} pf2
			in 
				dcml_conn_n {U}{g-mkic(emp,A)}{r}{rr}{a,b}{i,j} (pf1, pf2)
			end

		| dcml_neg_c {U}{g}{r}{a}{m} pf => 
			if ~is_principal {mkic(r,neg(a))}{mkic(emp,A)} ()
			then 
				let prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(emp,A)}{A}{m} pf 
				in dcml_neg_c {U}{g-mkic(emp,A)}{r}{a}{i} pf end 
			else 
				(* here, the proof size is strictly smaller *)
				let prval [i:int] pf = ih {U}{g+mkid(U,a)-mkic(emp,A)}{A}{m} pf 
				in lemma_full_d {U}{g-mkic(emp,A)}{a}{i} pf end 

		| dcml_neg_d {U}{G}{r}{a}{m} pf => 
			let prval [i:int] pf = ih {U}{G+mkic(U-r,a)-mkic(emp,A)}{A}{m} pf 
			in dcml_neg_d {U}{G-mkic(emp,A)}{r}{a}{i} pf end 

in 
	ih {U}{G}{A}{M} proof 
end 

primplement lemma_full_d {U}{G}{A}{M} (proof) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {A:form} {M:nat} .<size(A),M>. (proof: DCML (U, M, nil |- G + mkid(U,A))): [i:nat|i <= M] DCML (U, i, nil |- G) = 
		case+ proof of 
		| dcml_axi_d {U}{g}{gi}{p} init =>
			sif mem (g-gi, mkid(U,A))
			then dcml_axi_d {U}{g-mkid(U,A)}{gi}{p} init
			else dcml_axi_d {U}{g-mkid(U,A)}{gi-mkid(U,A)}{p} (lemma_init_remove {U}{U}{gi}{p}{U}{A} init)

		| dcml_axi_c {U}{g}{gi}{p} init => 
			sif mem (g-gi, mkid(U,A))
			then dcml_axi_c {U}{g-mkid(U,A)}{gi}{p} init
			else let prval _ = lemma_init_form_mix {U}{U}{gi}{p}{U}{A} init in false_elim () end 

		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf =>
			if ~is_principal {mkid(r,conn(rr,a,b))}{mkid(U,A)} ()
			then 
				let prval [i:int] pf = ih {U}{G+mkid(r,a)}{A}{m} pf 
				in dcml_conn_p1 {U}{g-mkid(U,A)}{r}{rr}{a,b}{i} pf end
			else
				let 
					prval [i:int] pf = ih {U}{G+mkid(r,a)}{A}{m} pf
					prval [i:int] pf = ih {U}{G}{a}{i} pf 
				in 
					pf
				end

		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf => 
			let prval [i:int] pf = ih {U}{G+mkic(r,a)}{A}{m} pf 
			in dcml_conn_n1 {U}{g-mkid(U,A)}{r}{rr}{a,b}{i} pf end

		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf =>
			if ~is_principal {mkid(r,conn(rr,a,b))}{mkid(U,A)} ()
			then 
				let prval [i:int] pf = ih {U}{G+mkid(r,b)}{A}{m} pf 
				in dcml_conn_p2 {U}{g-mkid(U,A)}{r}{rr}{a,b}{i} pf end
			else
				let 
					prval [i:int] pf = ih {U}{G+mkid(r,b)}{A}{m} pf
					prval [i:int] pf = ih {U}{G}{b}{i} pf 
				in 
					pf
				end

		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf =>
			let prval [i:int] pf = ih {U}{G+mkic(r,b)}{A}{m} pf 
			in dcml_conn_n2 {U}{g-mkid(U,A)}{r}{rr}{a,b}{i} pf end

		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) =>
			let 
				prval [i:int] pf1 = ih {U}{g+mkid(r,a)-mkid(U,A)}{A} pf1
				prval [j:int] pf2 = ih {U}{g+mkid(r,b)-mkid(U,A)}{A} pf2
			in 
				dcml_conn_n {U}{g-mkid(U,A)}{r}{rr}{a,b}{i,j} (pf1, pf2)
			end

		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) =>
			let 
				prval [i:int] pf1 = ih {U}{g+mkic(r,a)-mkid(U,A)}{A} pf1
				prval [j:int] pf2 = ih {U}{g+mkic(r,b)-mkid(U,A)}{A} pf2
			in 
				dcml_conn_p {U}{g-mkid(U,A)}{r}{rr}{a,b}{i,j} (pf1, pf2)
			end

		| dcml_neg_d {U}{g}{r}{a}{m} pf => 
			if ~is_principal {mkid(r,neg(a))}{mkid(U,A)} ()
			then 
				let prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(U,A)}{A}{m} pf 
				in dcml_neg_d {U}{g-mkid(U,A)}{r}{a}{i} pf end 
			else 
				(* here, the proof size is strictly smaller *)
				let prval [i:int] pf = ih {U}{g+mkic(emp,a)-mkid(U,A)}{A}{m} pf 
				in lemma_empty_c {U}{g-mkid(U,A)}{a}{i} pf end 

		| dcml_neg_c {U}{G}{r}{a}{m} pf => 
			let prval [i:int] pf = ih {U}{G+mkid(U-r,a)-mkid(U,A)}{A}{m} pf 
			in dcml_neg_c {U}{G-mkid(U,A)}{r}{a}{i} pf end 

in 
	ih {U}{G}{A}{M} proof 
end 



primplement lemma_id_c {U}{G}{R1,R2}{A} () = lemma_split_c {U}{G}{R1,R2}{A} (lemma_full_c {U}{G}{A} ())

primplement lemma_id_d {U}{G}{R1,R2}{A} () = lemma_split_d {U}{G}{R1,R2}{A} (lemma_empty_d {U}{G}{A} ())






primplement lemma_2cut_d {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,R1,R2)} {A:form} {M,N:nat} .<size(A),M+N>. 
		(fst: DCML (U, M, nil |- G + mkid(R1,A)), snd: DCML (U, N, nil |- G + mkid(R2,A))): [I:nat] DCML (U, I, nil |- G) = 

		sif not (is_atom A) 
		then 
			case+ (fst, snd) of 
			(* axioms *)
			| (dcml_axi_d {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_d {U}{g1-mkid(R1,A)}{gi1}{p1} init end
			| (_, dcml_axi_d {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_d {U}{g2-mkid(R2,A)}{gi2}{p2} init end
			| (dcml_axi_c {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_c {U}{g1-mkid(R1,A)}{gi1}{p1} init end
			| (_, dcml_axi_c {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_c {U}{g2-mkid(R2,A)}{gi2}{p2} init end

			(* non-principal disj *)
			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) when ~is_principal {mkid(r,neg(a))}{mkid(R1,A)} () => 
				let 
					prval snd = lemma_wk_c {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in 
					dcml_neg_d {U}{g-mkid(R1,A)}{r}{a}{i} pf 
				end 

			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) when ~is_principal {mkid(r,neg(a))}{mkid(R2,A)} () => 
				let 
					prval fst = lemma_wk_c {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					dcml_neg_d {U}{g-mkid(R2,A)}{r}{a}{i} pf 
				end 

			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1,A)} () => 
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_p1 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1,A)} () => 
				let 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_p2 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R2,A)} () =>  
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_p1 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R2,A)} () =>  
				let 
					prval fst_br = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					dcml_conn_p2 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1,A)} () =>   
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_n {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R2,A)} () =>   
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_n {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			(* non-principal conj *)
			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_d {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in 
					dcml_neg_c {U}{g-mkid(R1,A)}{r}{a}{i} pf 
				end 

			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) => 
				let 
					prval fst = lemma_wk_d {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					dcml_neg_c {U}{g-mkid(R2,A)}{r}{a}{i} pf 
				end 

			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_n1 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_n2 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_n1 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					dcml_conn_n2 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_p {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_p {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			(* all-principal *)
			| (dcml_neg_d {U}{g1}{r1}{a1}{m1} pf1, dcml_neg_d {U}{g2}{r2}{a2}{m2} pf2) 
				when is_principal {mkid(r1,neg(a1))}{mkid(R1,A)} () * is_principal {mkid(r2,neg(a2))}{mkid(R2,A)} () => 
				(*
					pf1: g1 + mkic(U-r1,a1)  pf2: g2 + mkic(U-r2,a2)
					----------------------   ----------------------
					fst: g1(mkid(R1,A))      snd: g2(mkid(R2,A))
					-------------------------------------------
					goal
				*)
				let 
					stadef a = a1

					prval fst_wk = lemma_wk_c {U}{g1}{U-r2}{a} fst 
					prval [i:int] G_a2 = ih {U}{G+mkic(U-r2,a)}{R1,R2}{A}{M,m2} (fst_wk, pf2)

					prval snd_wk = lemma_wk_c {U}{g2}{U-r1}{a} snd 
					prval [j:int] G_a1 = ih {U}{G+mkic(U-r1,a)}{R1,R2}{A}{m1,N} (pf1, snd_wk)
				in 
					lemma_2cut_c {U}{G}{U-r2,U-r1}{a}{i,j} (G_a2, G_a1)
				end


			| (dcml_conn_p1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, dcml_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
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
					prval fst_aR2 = lemma_wk_d {U}{g1}{R2}{a} fst 
					prval [i:int] G_aR2 = ih {U}{G+mkid(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] *)
					prval snd_aR1 = lemma_wk_d {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mkid(R1,a)}{R1,R2}{A}{m1,N} (pf1, snd_aR1)
				in 
					ih {U}{G}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				end 

			| (dcml_conn_p2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, dcml_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_d {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mkid(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_d {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mkid(R1,b)}{R1,R2}{A}{n1,N} (pf1, snd_bR1)
				in 
					ih {U}{G}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				end 

			| (dcml_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_p1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
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
					prval snd_aR1 = lemma_wk_d {U}{g2}{R1}{a} snd 
					prval [i:int] G_aR1 = ih {U}{G+mkid(R1,a)}{R1,R2}{A}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] *)
					prval fst_aR2 = lemma_wk_d {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mkid(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf2)
				in 
					ih {U}{G}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				end 

			| (dcml_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_p2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_d {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mkid(R1,b)}{R1,R2}{A}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_d {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mkid(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf2)
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
			| (dcml_axi_c {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_c {U}{g1-mkid(R1,A)}{gi1}{p1} init end
			| (_, dcml_axi_c {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_c {U}{g2-mkid(R2,A)}{gi2}{p2} init end
			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_d {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_c {U}{g-mkid(R1,A)}{r}{a}{i} pf end
 			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) =>
				let 
					prval fst = lemma_wk_d {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_c {U}{g-mkid(R2,A)}{r}{a}{i} pf end
			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_n1 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_n2 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_n1 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf)
				in dcml_conn_n2 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_p {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_p {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end

			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_c {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_d {U}{g-mkid(R1,A)}{r}{a}{i} pf end

			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) => 
				let 
					prval fst = lemma_wk_c {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_d {U}{g-mkid(R2,A)}{r}{a}{i} pf end

			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_p1 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_p2 {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_p1 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_p2 {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_n {U}{g-mkid(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_n {U}{g-mkid(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (dcml_axi_d {U}{g1}{gi1}{p1} init1, dcml_axi_d {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{U}{gi1}{p1}{R1}{A} init1
				then dcml_axi_d {U}{g1-mkid(R1,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{U}{gi2}{p2}{R2}{A} init2 
				then dcml_axi_d {U}{g2-mkid(R2,A)}{gi2}{p2} init2
				else
					(*
						init1: dcml_INIT (U,gi1,A)                   init2: dcml_INIT (U,gi2,A)
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
						prval _ = lemma_init_seqs {U}{U-(U-R1),U-(U-R2)}{gi1-mkid(R1,A),gi2-mkid(R2,A)}{A} (init1, init2)
						prval init = lemma_init_merge {U}{U-(U-R1),U-(U-R2)}{gi1-mkid(R1,A),gi2-mkid(R2,A)}{A} (init1, init2)
					in 
						dcml_axi_d {U}{G}{(gi1-mkid(R1,A))+(gi2-mkid(R2,A))}{A} init
					end 

in 
	ih {U}{G}{R1,R2}{A}{M,N} (fst, snd)
end 

primplement lemma_2cut_c {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disjunion(U,U-R1,U-R2)} {A:form} {M,N:nat} .<size(A),M+N>. 
		(fst: DCML (U, M, nil |- G + mkic(R1,A)), snd: DCML (U, N, nil |- G + mkic(R2,A))): [I:nat] DCML (U, I, nil |- G) = 

		sif not (is_atom A) 
		then 
			case+ (fst, snd) of 
			(* axioms *)
			| (dcml_axi_c {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_c {U}{g1-mkic(R1,A)}{gi1}{p1} init end
			| (_, dcml_axi_c {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_c {U}{g2-mkic(R2,A)}{gi2}{p2} init end
			| (dcml_axi_d {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_d {U}{g1-mkic(R1,A)}{gi1}{p1} init end
			| (_, dcml_axi_d {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_d {U}{g2-mkic(R2,A)}{gi2}{p2} init end

			(* non-principal conj *)
			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) when ~is_principal {mkic(r,neg(a))}{mkic(R1,A)} () => 
				let 
					prval snd = lemma_wk_d {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in 
					dcml_neg_c {U}{g-mkic(R1,A)}{r}{a}{i} pf 
				end 

			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) when ~is_principal {mkic(r,neg(a))}{mkic(R2,A)} () => 
				let 
					prval fst = lemma_wk_d {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					dcml_neg_c {U}{g-mkic(R2,A)}{r}{a}{i} pf 
				end 

			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R1,A)} () => 
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_n1 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R1,A)} () => 
				let 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_n2 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R2,A)} () =>  
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_n1 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R2,A)} () =>  
				let 
					prval fst_br = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					dcml_conn_n2 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R1,A)} () =>   
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_p {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R2,A)} () =>   
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_p {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			(* non-principal disj *)
			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_c {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in 
					dcml_neg_d {U}{g-mkic(R1,A)}{r}{a}{i} pf 
				end 

			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) => 
				let 
					prval fst = lemma_wk_c {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					dcml_neg_d {U}{g-mkic(R2,A)}{r}{a}{i} pf 
				end 

			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_p1 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_p2 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_p1 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					dcml_conn_p2 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_n {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_n {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			(* all-principal *)
			| (dcml_neg_c {U}{g1}{r1}{a1}{m1} pf1, dcml_neg_c {U}{g2}{r2}{a2}{m2} pf2) 
				when is_principal {mkic(r1,neg(a1))}{mkic(R1,A)} () * is_principal {mkic(r2,neg(a2))}{mkic(R2,A)} () => 
				let 
					stadef a = a1

					prval fst_wk = lemma_wk_d {U}{g1}{U-r2}{a} fst 
					prval [i:int] G_a2 = ih {U}{G+mkid(U-r2,a)}{R1,R2}{A}{M,m2} (fst_wk, pf2)

					prval snd_wk = lemma_wk_d {U}{g2}{U-r1}{a} snd 
					prval [j:int] G_a1 = ih {U}{G+mkid(U-r1,a)}{R1,R2}{A}{m1,N} (pf1, snd_wk)
				in 
					lemma_2cut_d {U}{G}{U-r2,U-r1}{a}{i,j} (G_a2, G_a1)
				end


			| (dcml_conn_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, dcml_conn_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
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
					prval fst_aR2 = lemma_wk_c {U}{g1}{R2}{a} fst 
					prval [i:int] G_aR2 = ih {U}{G+mkic(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] *)
					prval snd_aR1 = lemma_wk_c {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mkic(R1,a)}{R1,R2}{A}{m1,N} (pf1, snd_aR1)
				in 
					ih {U}{G}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				end 

			| (dcml_conn_n2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, dcml_conn_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_c {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mkic(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_c {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mkic(R1,b)}{R1,R2}{A}{n1,N} (pf1, snd_bR1)
				in 
					ih {U}{G}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				end 

			| (dcml_conn_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
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
					prval snd_aR1 = lemma_wk_c {U}{g2}{R1}{a} snd 
					prval [i:int] G_aR1 = ih {U}{G+mkic(R1,a)}{R1,R2}{A}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] *)
					prval fst_aR2 = lemma_wk_c {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mkic(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf2)
				in 
					ih {U}{G}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				end 

			| (dcml_conn_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_n2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_c {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mkic(R1,b)}{R1,R2}{A}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_c {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mkic(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf2)
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
			| (dcml_axi_d {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_d {U}{g1-mkic(R1,A)}{gi1}{p1} init end
			| (_, dcml_axi_d {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_d {U}{g2-mkic(R2,A)}{gi2}{p2} init end
			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_c {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_d {U}{g-mkic(R1,A)}{r}{a}{i} pf end
			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) => 
				let 
					prval fst = lemma_wk_c {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_d {U}{g-mkic(R2,A)}{r}{a}{i} pf end
			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_p1 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_p2 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_p1 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf)
				in dcml_conn_p2 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_n {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_n {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end

			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) =>
				let 
					prval snd = lemma_wk_d {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_c {U}{g-mkic(R1,A)}{r}{a}{i} pf end
			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) =>
				let 
					prval fst = lemma_wk_d {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_c {U}{g-mkic(R2,A)}{r}{a}{i} pf end
			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_n1 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_n2 {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_n1 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf)
				in dcml_conn_n2 {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_p {U}{g-mkic(R1,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_p {U}{g-mkic(R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (dcml_axi_c {U}{g1}{gi1}{p1} init1, dcml_axi_c {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{U}{gi1}{p1}{R1}{A} init1
				then dcml_axi_c {U}{g1-mkic(R1,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{U}{gi2}{p2}{R2}{A} init2 
				then dcml_axi_c {U}{g2-mkic(R2,A)}{gi2}{p2} init2
				else
					let 
						prval _ = lemma_init_form {U}{U}{gi1}{p1}{R1}{A} init1
						prval _ = lemma_init_form {U}{U}{gi2}{p2}{R2}{A} init2
						prval init1 = lemma_init_remove {U}{U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{U}{gi2}{p2}{R2}{A} init2 
						prval _ = lemma_init_seqs {U}{U-R1,U-R2}{gi1-mkic(R1,A),gi2-mkic(R2,A)}{A} (init1, init2)
						prval init = lemma_init_merge {U}{U-R1,U-R2}{gi1-mkic(R1,A),gi2-mkic(R2,A)}{A} (init1, init2)
					in 
						dcml_axi_c {U}{G}{(gi1-mkic(R1,A))+(gi2-mkic(R2,A))}{A} init
					end 

in 
	ih {U}{G}{R1,R2}{A}{M,N} (fst, snd)
end 


primplement lemma_2cut_spill_d {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 
	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(R1,R2)} {A:form} {M,N:nat} .<size(A),M+N>.
		(fst: DCML (U, M, nil |- G + mkid(R1,A)), snd: DCML (U, N, nil |- G + mkid(R2,A))): [I:nat] DCML (U, I, nil |- G + mkid(R1+R2,A)) = 

		sif is_atom A 
		then 
			case+ (fst, snd) of 
			| (dcml_axi_c {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_c {U}{g1-mkid(R1,A)+mkid(R1+R2,A)}{gi1}{p1} init end
			| (_, dcml_axi_c {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_c {U}{g2-mkid(R2,A)+mkid(R1+R2,A)}{gi2}{p2} init end
			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_d {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_c {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{a}{i} pf end
 			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) =>
				let 
					prval fst = lemma_wk_d {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_c {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{a}{i} pf end
			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_n1 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_n2 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_n1 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf)
				in dcml_conn_n2 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_p {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_p {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end

			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_c {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_d {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{a}{i} pf end

			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) => 
				let 
					prval fst = lemma_wk_c {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_d {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{a}{i} pf end

			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_p1 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_p2 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_p1 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_p2 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_n {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_n {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (dcml_axi_d {U}{g1}{gi1}{p1} init1, dcml_axi_d {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{U}{gi1}{p1}{R1}{A} init1
				then dcml_axi_d {U}{g1-mkid(R1,A)+mkid(R1+R2,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{U}{gi2}{p2}{R2}{A} init2 
				then dcml_axi_d {U}{g2-mkid(R2,A)+mkid(R1+R2,A)}{gi2}{p2} init2
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
						prval _ = lemma_init_seqs {U}{U-(U-R1),U-(U-R2)}{gi1-mkid(R1,A),gi2-mkid(R2,A)}{A} (init1, init2)

						(* init = U-R1 + U-R2, missing R1+R2 right now *)
						prval init = lemma_init_merge {U}{U-(U-R1),U-(U-R2)}{gi1-mkid(R1,A),gi2-mkid(R2,A)}{A} (init1, init2)

						(* prove R1+R2 + U-R1 + U-R2 = U, all disjoint *)
						prval _ = lemma_set_com_demorgan {U,U-(U-R1),U-(U-R2)} ()
						(* prove A[R1+R2] is not in gi1-A[R1] or gi2-A[R2] *)
						prval _ = lemma_init_role_neg {U}{(U-(U-R1))+(U-(U-R2))}{(gi1-mkid(R1,A))+(gi2-mkid(R2,A))}{A}{R1+R2}{A} (init)

						(* add back A[R1+R2] *)
						prval init = dcmld_init_more {U}{(U-(U-R1))+(U-(U-R2))}{(gi1-mkid(R1,A))+(gi2-mkid(R2,A))}{A}{R1+R2} init
					in 
						dcml_axi_d {U}{G+mkid(R1+R2,A)}{(gi1-mkid(R1,A))+(gi2-mkid(R2,A))+mkid(R1+R2,A)}{A} init
					end 
		else
			case+ (fst, snd) of 
			(* axioms *)
			| (dcml_axi_d {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_d {U}{g1-mkid(R1,A)+mkid(R1+R2,A)}{gi1}{p1} init end
			| (_, dcml_axi_d {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_d {U}{g2-mkid(R2,A)+mkid(R1+R2,A)}{gi2}{p2} init end
			| (dcml_axi_c {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_c {U}{g1-mkid(R1,A)+mkid(R1+R2,A)}{gi1}{p1} init end
			| (_, dcml_axi_c {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_c {U}{g2-mkid(R2,A)+mkid(R1+R2,A)}{gi2}{p2} init end

			(* non-principal disj *)
			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) when ~is_principal {mkid(r,neg(a))}{mkid(R1,A)} () => 
				let 
					prval snd = lemma_wk_c {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in 
					dcml_neg_d {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{a}{i} pf 
				end 

			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) when ~is_principal {mkid(r,neg(a))}{mkid(R2,A)} () => 
				let 
					prval fst = lemma_wk_c {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					dcml_neg_d {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{a}{i} pf 
				end 

			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1,A)} () => 
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_p1 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1,A)} () => 
				let 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_p2 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R2,A)} () =>  
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_p1 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R2,A)} () =>  
				let 
					prval fst_br = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					dcml_conn_p2 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1,A)} () =>   
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_n {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R2,A)} () =>   
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_n {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			(* non-principal conj *)
			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_d {U}{G+mkid(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in 
					dcml_neg_c {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{a}{i} pf 
				end 

			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) => 
				let 
					prval fst = lemma_wk_d {U}{G+mkid(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkid(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in 
					dcml_neg_c {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{a}{i} pf 
				end 

			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in 
					dcml_conn_n1 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in 
					dcml_conn_n2 {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in 
					dcml_conn_n1 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_ar
				end 

			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf)
				in 
					dcml_conn_n2 {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i} G_br
				end 

			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkid(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkid(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in 
					dcml_conn_p {U}{g-mkid(R1,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkid(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkid(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in 
					dcml_conn_p {U}{g-mkid(R2,A)+mkid(R1+R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br)
				end 

			(* all-principal *)
			| (dcml_neg_d {U}{g1}{r1}{a1}{m1} pf1, dcml_neg_d {U}{g2}{r2}{a2}{m2} pf2) 
				when is_principal {mkid(r1,neg(a1))}{mkid(R1,A)} () * is_principal {mkid(r2,neg(a2))}{mkid(R2,A)} () => 
				(*
					pf1: g1 + mkic(U-r1,a1)  pf2: g2 + mkic(U-r2,a2)
					----------------------   ----------------------
					fst: g1(mkid(R1,A))      snd: g2(mkid(R2,A))
					-------------------------------------------
					goal
				*)
				let 
					stadef a = a1

					prval fst_wk = lemma_wk_c {U}{g1}{U-r2}{a} fst 
					prval [i:int] G_a2 = ih {U}{G+mkic(U-r2,a)}{R1,R2}{A}{M,m2} (fst_wk, pf2)

					prval snd_wk = lemma_wk_c {U}{g2}{U-r1}{a} snd 
					prval [j:int] G_a1 = ih {U}{G+mkic(U-r1,a)}{R1,R2}{A}{m1,N} (pf1, snd_wk)
					
					prval [i:int] pf = lemma_2cut_spill_c {U}{G+mkid(R1+R2,A)}{U-r2,U-r1}{a}{i,j} (G_a2, G_a1)
				in 
					dcml_neg_d {U}{G+mkid(R1+R2,A)}{R1+R2}{a}{i} pf
				end


			| (dcml_conn_p1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, dcml_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
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
					prval fst_aR2 = lemma_wk_d {U}{g1}{R2}{a} fst 
					prval [i:int] G_aR2 = ih {U}{G+mkid(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] *)
					prval snd_aR1 = lemma_wk_d {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mkid(R1,a)}{R1,R2}{A}{m1,N} (pf1, snd_aR1)

					prval [i:int] pf = ih {U}{G+mkid(R1+R2,A)}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				in 
					dcml_conn_p1 {U}{G+mkid(R1+R2,A)}{R1+R2}{rr}{a,b}{i} pf 
				end 

			| (dcml_conn_p2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, dcml_conn_n {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_d {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mkid(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_d {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mkid(R1,b)}{R1,R2}{A}{n1,N} (pf1, snd_bR1)

					prval [i:int] pf = ih {U}{G+mkid(R1+R2,A)}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				in 
					dcml_conn_p2 {U}{G+mkid(R1+R2,A)}{R1+R2}{rr}{a,b}{i} pf 
				end 

			| (dcml_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_p1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
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
					prval snd_aR1 = lemma_wk_d {U}{g2}{R1}{a} snd 
					prval [i:int] G_aR1 = ih {U}{G+mkid(R1,a)}{R1,R2}{A}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] *)
					prval fst_aR2 = lemma_wk_d {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mkid(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf2)
					
					prval [i:int] pf = ih {U}{G+mkid(R1+R2,A)}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				in 
					dcml_conn_p1 {U}{G+mkid(R1+R2,A)}{R1+R2}{rr}{a,b}{i} pf 
				end 

			| (dcml_conn_n {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_p2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mkid(r1,conn(rr1,a1,b1))}{mkid(R1,A)} () * is_principal {mkid(r2,conn(rr2,a2,b2))}{mkid(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_d {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mkid(R1,b)}{R1,R2}{A}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_d {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mkid(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf2)
					
					prval [i:int] pf = ih {U}{G+mkid(R1+R2,A)}{R1,R2}{b}{i,j} (G_bR1, G_bR2)
				in 
					dcml_conn_p2 {U}{G+mkid(R1+R2,A)}{R1+R2}{rr}{a,b}{i} pf 
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


primplement lemma_2cut_spill_c {U}{G}{R1,R2}{A}{M,N} (fst, snd) = let 
	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(U-R1,U-R2)} {A:form} {M,N:nat} .<size(A),M+N>.
		(fst: DCML (U, M, nil |- G + mkic(R1,A)), snd: DCML (U, N, nil |- G + mkic(R2,A))): [I:nat] DCML (U, I, nil |- G + mkic(R1*R2,A)) = 

		sif is_atom A 
		then 
			case+ (fst, snd) of 
			| (dcml_axi_d {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_d {U}{g1-mkic(R1,A)+mkic(R1*R2,A)}{gi1}{p1} init end
			| (_, dcml_axi_d {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_d {U}{g2-mkic(R2,A)+mkic(R1*R2,A)}{gi2}{p2} init end
			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_c {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_d {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
 			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) =>
				let 
					prval fst = lemma_wk_c {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_d {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_p1 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_p2 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_p1 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf)
				in dcml_conn_p2 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_n {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_n {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end

			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_d {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_c {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) => 
				let 
					prval fst = lemma_wk_d {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_c {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) => 
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_n1 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) => 
				let 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_n2 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) => 
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_n1 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) => 
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_n2 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) => 
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_p {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) => 
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_p {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end

			| (dcml_axi_c {U}{g1}{gi1}{p1} init1, dcml_axi_c {U}{g2}{gi2}{p2} init2) =>>

				if ~lemma_init_member {U}{U}{gi1}{p1}{R1}{A} init1
				then dcml_axi_c {U}{g1-mkic(R1,A)+mkic(R1*R2,A)}{gi1}{p1} init1 
				else if ~lemma_init_member {U}{U}{gi2}{p2}{R2}{A} init2 
				then dcml_axi_c {U}{g2-mkic(R2,A)+mkic(R1*R2,A)}{gi2}{p2} init2
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
						prval _ = lemma_init_form {U}{U}{gi1}{p1}{R1}{A} init1
						prval _ = lemma_init_form {U}{U}{gi2}{p2}{R2}{A} init2
						prval init1 = lemma_init_remove {U}{U}{gi1}{p1}{R1}{A} init1 
						prval init2 = lemma_init_remove {U}{U}{gi2}{p2}{R2}{A} init2 
						prval _ = lemma_init_seqs {U}{U-R1,U-R2}{gi1-mkic(R1,A),gi2-mkic(R2,A)}{A} (init1, init2)

						(* init = U-R1 + U-R2, missing R1*R2 right now *)
						prval init = lemma_init_merge {U}{U-R1,U-R2}{gi1-mkic(R1,A),gi2-mkic(R2,A)}{A} (init1, init2)

						(* prove R1*R2 + U-R1 + U-R2 = U, all disjoint *)
						prval _ = lemma_set_com_demorgan {U,U-R1,U-R2} ()
						(* prove A[R1*R2] is not in gi1-A[R1] or gi2-A[R2] *)
						prval _ = lemma_init_role_neg {U}{(U-R1)+(U-R2)}{(gi1-mkic(R1,A))+(gi2-mkic(R2,A))}{A}{R1*R2}{A} (init)

						(* add back A[R1*R2] *)
						prval init = dcmlc_init_more {U}{(U-R1)+(U-R2)}{(gi1-mkic(R1,A))+(gi2-mkic(R2,A))}{A}{R1*R2} init
					in 
						dcml_axi_c {U}{G+mkic(R1*R2,A)}{(gi1-mkic(R1,A))+(gi2-mkic(R2,A))+mkic(R1*R2,A)}{A} init
					end 
		else
			case+ (fst, snd) of 
			(* axioms *)
			| (dcml_axi_c {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_neg {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_c {U}{g1-mkic(R1,A)+mkic(R1*R2,A)}{gi1}{p1} init end
			| (_, dcml_axi_c {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_neg {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_c {U}{g2-mkic(R2,A)+mkic(R1*R2,A)}{gi2}{p2} init end
			| (dcml_axi_d {U}{g1}{gi1}{p1} init, _) => let prval _ = lemma_init_form_mix {U}{U}{gi1}{p1}{R1}{A} init in dcml_axi_d {U}{g1-mkic(R1,A)+mkic(R1*R2,A)}{gi1}{p1} init end
			| (_, dcml_axi_d {U}{g2}{gi2}{p2} init) => let prval _ = lemma_init_form_mix {U}{U}{gi2}{p2}{R2}{A} init in dcml_axi_d {U}{g2-mkic(R2,A)+mkic(R1*R2,A)}{gi2}{p2} init end
			| (dcml_neg_d {U}{g}{r}{a}{m} pf, _) => 
				let 
					prval snd = lemma_wk_c {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_d {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
 			| (_, dcml_neg_d {U}{g}{r}{a}{m} pf) =>
				let 
					prval fst = lemma_wk_c {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkic(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_d {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
			| (dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf, _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_p1 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf, _) =>
				let 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_p2 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_p1 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_p2 {U}{g}{r}{rr}{a,b}{n} pf) =>
				let 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf)
				in dcml_conn_p2 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) =>
				let 
					prval snd_ar = lemma_wk_d {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_d {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_n {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) =>
				let 
					prval fst_ar = lemma_wk_d {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_d {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkid(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkid(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_n {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end

			| (dcml_neg_c {U}{g}{r}{a}{m} pf, _) when ~is_principal {mkic(R1,A)}{mkic(r,neg(a))} () => 
				let 
					prval snd = lemma_wk_d {U}{G+mkic(R2,A)}{U-r}{a} snd 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R1,A)}{R1,R2}{A}{m,N} (pf, snd)
				in dcml_neg_c {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
			| (_, dcml_neg_c {U}{g}{r}{a}{m} pf) when ~is_principal {mkic(R2,A)}{mkic(r,neg(a))} ()=> 
				let 
					prval fst = lemma_wk_d {U}{G+mkic(R1,A)}{U-r}{a} fst 
					prval [i:int] pf = ih {U}{g+mkid(U-r,a)-mkic(R2,A)}{R1,R2}{A}{M,m} (fst, pf)
				in dcml_neg_c {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{a}{i} pf end
			| (dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf, _) when ~is_principal {mkic(R1,A)}{mkic(r,conn(rr,a,b))} () => 
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf, snd_ar)
				in dcml_conn_n1 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf, _) when ~is_principal {mkic(R1,A)}{mkic(r,conn(rr,a,b))} () => 
				let 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf, snd_br)
				in dcml_conn_n2 {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (_, dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf) when ~is_principal {mkic(R2,A)}{mkic(r,conn(rr,a,b))} () => 
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_n1 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_ar end
			| (_, dcml_conn_n2 {U}{g}{r}{rr}{a,b}{n} pf) when ~is_principal {mkic(R2,A)}{mkic(r,conn(rr,a,b))} () => 
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_ar, pf)
				in dcml_conn_n2 {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i} G_br end
			| (dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2), _) when ~is_principal {mkic(R1,A)}{mkic(r,conn(rr,a,b))} () => 
				let 
					prval snd_ar = lemma_wk_c {U}{G+mkic(R2,A)}{r}{a} snd 
					prval snd_br = lemma_wk_c {U}{G+mkic(R2,A)}{r}{b} snd 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (pf1, snd_ar)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (pf2, snd_br)
				in dcml_conn_p {U}{g-mkic(R1,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end
			| (_, dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2)) when ~is_principal {mkic(R2,A)}{mkic(r,conn(rr,a,b))} () => 
				let 
					prval fst_ar = lemma_wk_c {U}{G+mkic(R1,A)}{r}{a} fst 
					prval fst_br = lemma_wk_c {U}{G+mkic(R1,A)}{r}{b} fst 
					prval [i:int] G_ar = ih {U}{G+mkic(r,a)}{R1,R2}{A} (fst_ar, pf1)
					prval [j:int] G_br = ih {U}{G+mkic(r,b)}{R1,R2}{A} (fst_br, pf2)
				in dcml_conn_p {U}{g-mkic(R2,A)+mkic(R1*R2,A)}{r}{rr}{a,b}{i,j} (G_ar, G_br) end

			(* all-principal *)
			| (dcml_neg_c {U}{g1}{r1}{a1}{m1} pf1, dcml_neg_c {U}{g2}{r2}{a2}{m2} pf2) 
				when is_principal {mkic(r1,neg(a1))}{mkic(R1,A)} () * is_principal {mkic(r2,neg(a2))}{mkic(R2,A)} () => 
				(*
					pf1: g1 + mkid(U-r1,a1)  pf2: g2 + mkid(U-r2,a2)
					----------------------   ----------------------
					fst: g1(mkic(R1,A))      snd: g2(mkic(R2,A))
					-------------------------------------------
					goal
				*)
				let 
					stadef a = a1

					prval fst_wk = lemma_wk_d {U}{g1}{U-r2}{a} fst 
					prval [i:int] G_a2 = ih {U}{G+mkid(U-r2,a)}{R1,R2}{A}{M,m2} (fst_wk, pf2)

					prval snd_wk = lemma_wk_d {U}{g2}{U-r1}{a} snd 
					prval [j:int] G_a1 = ih {U}{G+mkid(U-r1,a)}{R1,R2}{A}{m1,N} (pf1, snd_wk)
					
					prval [i:int] pf = lemma_2cut_spill_d {U}{G+mkic(R1*R2,A)}{U-r2,U-r1}{a}{i,j} (G_a2, G_a1)
				in 
					dcml_neg_c {U}{G+mkic(R1*R2,A)}{R1*R2}{a}{i} pf
				end


			| (dcml_conn_n1 {U}{g1}{r1}{rr1}{a1,b1}{m1} pf1, dcml_conn_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
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
					prval fst_aR2 = lemma_wk_c {U}{g1}{R2}{a} fst 
					prval [i:int] G_aR2 = ih {U}{G+mkic(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf21)

					(* cut (snd + a[R1], pf1) = G + a[R1] *)
					prval snd_aR1 = lemma_wk_c {U}{g2}{R1}{a} snd 
					prval [j:int] G_aR1 = ih {U}{G+mkic(R1,a)}{R1,R2}{A}{m1,N} (pf1, snd_aR1)

					prval [i:int] pf = ih {U}{G+mkic(R1*R2,A)}{R1,R2}{a}{j,i} (G_aR1, G_aR2)
				in 
					dcml_conn_n1 {U}{G+mkic(R1*R2,A)}{R1*R2}{rr}{a,b}{i} pf 
				end 

			| (dcml_conn_n2 {U}{g1}{r1}{rr1}{a1,b1}{n1} pf1, dcml_conn_p {U}{g2}{r2}{rr2}{a2,b2}{m2,n2} (pf21, pf22)) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (fst + b[R2], pf22) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_c {U}{g1}{R2}{b} fst 
					prval [i:int] G_bR2 = ih {U}{G+mkic(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf22)

					(* cut (snd + b[R1], pf1) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_c {U}{g2}{R1}{b} snd 
					prval [j:int] G_bR1 = ih {U}{G+mkic(R1,b)}{R1,R2}{A}{n1,N} (pf1, snd_bR1)

					prval [i:int] pf = ih {U}{G+mkic(R1*R2,A)}{R1,R2}{b}{j,i} (G_bR1, G_bR2)
				in 
					dcml_conn_n2 {U}{G+mkic(R1*R2,A)}{R1*R2}{rr}{a,b}{i} pf 
				end 

			| (dcml_conn_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_n1 {U}{g2}{r2}{rr2}{a2,b2}{m2} pf2) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
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
					prval snd_aR1 = lemma_wk_c {U}{g2}{R1}{a} snd 
					prval [i:int] G_aR1 = ih {U}{G+mkic(R1,a)}{R1,R2}{A}{m1,N} (pf11, snd_aR1)

					(* cut (fst + a[R2], pf2) = G + a[R2] *)
					prval fst_aR2 = lemma_wk_c {U}{g1}{R2}{a} fst 
					prval [j:int] G_aR2 = ih {U}{G+mkic(R2,a)}{R1,R2}{A}{M,m2} (fst_aR2, pf2)
					
					prval [i:int] pf = ih {U}{G+mkic(R1*R2,A)}{R1,R2}{a}{i,j} (G_aR1, G_aR2)
				in 
					dcml_conn_n1 {U}{G+mkic(R1*R2,A)}{R1*R2}{rr}{a,b}{i} pf 
				end 

			| (dcml_conn_p {U}{g1}{r1}{rr1}{a1,b1}{m1,n1} (pf11, pf12), dcml_conn_n2 {U}{g2}{r2}{rr2}{a2,b2}{n2} pf2) 
				when is_principal {mkic(r1,conn(rr1,a1,b1))}{mkic(R1,A)} () * is_principal {mkic(r2,conn(rr2,a2,b2))}{mkic(R2,A)} () =>
				let 
					stadef a = a1
					stadef b = b1 
					stadef rr = rr1

					(* cut (snd + b[R1], pf11) = G + b[R1] *)
					prval snd_bR1 = lemma_wk_c {U}{g2}{R1}{b} snd 
					prval [i:int] G_bR1 = ih {U}{G+mkic(R1,b)}{R1,R2}{A}{n1,N} (pf12, snd_bR1)

					(* cut (fst + b[R2], pf2) = G + b[R2] *)
					prval fst_bR2 = lemma_wk_c {U}{g1}{R2}{b} fst 
					prval [j:int] G_bR2 = ih {U}{G+mkic(R2,b)}{R1,R2}{A}{M,n2} (fst_bR2, pf2)
					
					prval [i:int] pf = ih {U}{G+mkic(R1*R2,A)}{R1,R2}{b}{i,j} (G_bR1, G_bR2)
				in 
					dcml_conn_n2 {U}{G+mkic(R1*R2,A)}{R1*R2}{rr}{a,b}{i} pf 
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


primplement lemma_wk_c {U}{G}{R}{A}{M} (pf) = let 
	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} .<M>. (pf: DCML (U, M, nil |- G)): DCML (U, M, nil |- G + mkic(R,A)) = 
		case+ pf of 
		| dcml_axi_d {U}{g}{gi}{p} pf => dcml_axi_d {U}{g+mkic(R,A)}{gi}{p} pf 
		| dcml_neg_d {U}{g}{r}{a}{m} pf => dcml_neg_d {U}{g+mkic(R,A)}{r}{a}{m} (ih {U}{g+mkic(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p1 {U}{g+mkic(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkid(r,a)}{R}{A}{m} pf)
		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p2 {U}{g+mkic(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkid(r,b)}{R}{A}{m} pf)
		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_n {U}{g+mkic(R,A)}{r}{rr}{a,b}{m,n} (
				ih {U}{g+mkid(r,a)}{R}{A} pf1, 
				ih {U}{g+mkid(r,b)}{R}{A} pf2)

		| dcml_axi_c {U}{g}{gi}{p} pf => dcml_axi_c {U}{g+mkic(R,A)}{gi}{p} pf 
		| dcml_neg_c {U}{g}{r}{a}{m} pf => dcml_neg_c {U}{g+mkic(R,A)}{r}{a}{m} (ih {U}{g+mkid(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n1 {U}{g+mkic(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkic(r,a)}{R}{A}{m} pf)
		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n2 {U}{g+mkic(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkic(r,b)}{R}{A}{m} pf)
		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_p {U}{g+mkic(R,A)}{r}{rr}{a,b}{m,n} (
				ih {U}{g+mkic(r,a)}{R}{A} pf1, 
				ih {U}{g+mkic(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 

primplement lemma_wk_d {U}{G}{R}{A}{M} (pf) = let 
	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} .<M>. (pf: DCML (U, M, nil |- G)): DCML (U, M, nil |- G + mkid(R,A)) = 
		case+ pf of 
		| dcml_axi_d {U}{g}{gi}{p} pf => dcml_axi_d {U}{g+mkid(R,A)}{gi}{p} pf 
		| dcml_neg_d {U}{g}{r}{a}{m} pf => dcml_neg_d {U}{g+mkid(R,A)}{r}{a}{m} (ih {U}{g+mkic(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p1 {U}{g+mkid(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkid(r,a)}{R}{A}{m} pf)
		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p2 {U}{g+mkid(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkid(r,b)}{R}{A}{m} pf)
		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_n {U}{g+mkid(R,A)}{r}{rr}{a,b}{m,n} (
				ih {U}{g+mkid(r,a)}{R}{A} pf1, 
				ih {U}{g+mkid(r,b)}{R}{A} pf2)

		| dcml_axi_c {U}{g}{gi}{p} pf => dcml_axi_c {U}{g+mkid(R,A)}{gi}{p} pf 
		| dcml_neg_c {U}{g}{r}{a}{m} pf => dcml_neg_c {U}{g+mkid(R,A)}{r}{a}{m} (ih {U}{g+mkid(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n1 {U}{g+mkid(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkic(r,a)}{R}{A}{m} pf)
		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n2 {U}{g+mkid(R,A)}{r}{rr}{a,b}{m} (
				ih {U}{g+mkic(r,b)}{R}{A}{m} pf)
		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_p {U}{g+mkid(R,A)}{r}{rr}{a,b}{m,n} (
				ih {U}{g+mkic(r,a)}{R}{A} pf1, 
				ih {U}{g+mkic(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 


primplement lemma_ctr_c {U}{G}{R}{A}{M} (pf) = let 

	prfun lemma_init_car {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mkic(R,A))&&not(R==emp)} .<size(G)>. 
		(init: DCMLC_INIT (U,U0,G,p)): [car(G,mkic(R,A))==1] unit_p = 
		case+ init of 
		| dcmlc_init_zero {U}{p} =/=> ()
		| dcmlc_init_more {U}{u}{g}{p}{r} (init) => 
			sif not (R == r)
			then let prval _ = lemma_bag_size_add {g}{mkic(r,p)} () in lemma_init_car {U}{u}{g}{p}{R}{A} init end
			else lemma_init_role_neg {U}{u}{g}{p}{R}{A} init

	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mkic(R,A))>1} .<M>. 
		(pf: DCML (U, M, nil |- G)): DCML (U, M, nil |- G - mkic(R,A)) = 

		case+ pf of 
		| dcml_axi_d {U}{g}{gi}{p} init => 
			let prval _ = lemma_init_form_mix {U}{U}{gi}{p}{R}{A} init 
			in dcml_axi_d {U}{g-mkic(R,A)}{gi}{p} init end
		| dcml_axi_c {U}{g}{gi}{p} init => 
			sif mem (g-gi, mkic(R,A))
			then dcml_axi_c {U}{g-mkic(R,A)}{gi}{p} init
			else 
				let 
					prval _ = lemma_init_member {U}{U}{gi}{p}{R}{A} init 
					prval _ = lemma_init_form {U}{U}{gi}{p}{R}{A} init
				in 
					sif not (R == emp)
					then let prval _ = lemma_init_car {U}{U}{gi}{p}{R}{A} init in false_elim () end
					else dcml_axi_c {U}{g-mkic(R,A)}{gi-mkic(R,A)}{p} (lemma_init_remove {U}{U}{gi}{p}{R}{A} init)
				end 
		| dcml_neg_d {U}{g}{r}{a}{m} pf => 
			dcml_neg_d {U}{g-mkic(R,A)}{r}{a}{m} (ih {U}{g+mkic(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p1 {U}{g-mkic(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkid(r,a)}{R}{A}{m} pf)
		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p2 {U}{g-mkic(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkid(r,b)}{R}{A}{m} pf)
		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_n {U}{g-mkic(R,A)}{r}{rr}{a,b}{m,n} (ih {U}{g+mkid(r,a)}{R}{A} pf1, ih {U}{g+mkid(r,b)}{R}{A} pf2)

		| dcml_neg_c {U}{g}{r}{a}{m} pf => 
			dcml_neg_c {U}{g-mkic(R,A)}{r}{a}{m} (ih {U}{g+mkid(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n1 {U}{g-mkic(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkic(r,a)}{R}{A}{m} pf)
		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n2 {U}{g-mkic(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkic(r,b)}{R}{A}{m} pf)
		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_p {U}{g-mkic(R,A)}{r}{rr}{a,b}{m,n} (ih {U}{g+mkic(r,a)}{R}{A} pf1, ih {U}{g+mkic(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 

primplement lemma_ctr_d {U}{G}{R}{A}{M} (pf) = let 

	prfun lemma_init_car {U:roles} {U0:roles|sub(U,U0)} {G:seqs} {p:form} {R:roles} {A:form} {mem(G,mkid(R,A))&&not(R==U)} .<size(G)>. 
		(init: DCMLD_INIT (U,U0,G,p)): [car(G,mkid(R,A))==1] unit_p = 
		case+ init of 
		| dcmld_init_zero {U}{p} =/=> ()
		| dcmld_init_more {U}{u}{g}{p}{r} (init) => 
			sif not (R == r)
			then let prval _ = lemma_bag_size_add {g}{mkid(r,p)} () in lemma_init_car {U}{u}{g}{p}{R}{A} init end
			else lemma_init_role_neg {U}{u}{g}{p}{R}{A} init

	prfun ih {U:roles} {G:seqs} {R:roles|sub(U,R)} {A:form} {M:nat} {car(G,mkid(R,A))>1} .<M>. 
		(pf: DCML (U, M, nil |- G)): DCML (U, M, nil |- G - mkid(R,A)) = 

		case+ pf of 
		| dcml_axi_c {U}{g}{gi}{p} init => 
			let prval _ = lemma_init_form_mix {U}{U}{gi}{p}{R}{A} init 
			in dcml_axi_c {U}{g-mkid(R,A)}{gi}{p} init end
		| dcml_axi_d {U}{g}{gi}{p} init => 
			sif mem (g-gi, mkid(R,A))
			then dcml_axi_d {U}{g-mkid(R,A)}{gi}{p} init
			else 
				let 
					prval _ = lemma_init_member {U}{U}{gi}{p}{R}{A} init 
					prval _ = lemma_init_form {U}{U}{gi}{p}{R}{A} init
				in 
					sif not (R == U)
					then let prval _ = lemma_init_car {U}{U}{gi}{p}{R}{A} init in false_elim () end
					else dcml_axi_d {U}{g-mkid(R,A)}{gi-mkid(R,A)}{p} (lemma_init_remove {U}{U}{gi}{p}{R}{A} init)
				end 
		| dcml_neg_d {U}{g}{r}{a}{m} pf => 
			dcml_neg_d {U}{g-mkid(R,A)}{r}{a}{m} (ih {U}{g+mkic(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p1 {U}{g-mkid(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkid(r,a)}{R}{A}{m} pf)
		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_p2 {U}{g-mkid(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkid(r,b)}{R}{A}{m} pf)
		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_n {U}{g-mkid(R,A)}{r}{rr}{a,b}{m,n} (ih {U}{g+mkid(r,a)}{R}{A} pf1, ih {U}{g+mkid(r,b)}{R}{A} pf2)

		| dcml_neg_c {U}{g}{r}{a}{m} pf => 
			dcml_neg_c {U}{g-mkid(R,A)}{r}{a}{m} (ih {U}{g+mkid(U-r,a)}{R}{A}{m} pf)
		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n1 {U}{g-mkid(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkic(r,a)}{R}{A}{m} pf)
		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf => 
			dcml_conn_n2 {U}{g-mkid(R,A)}{r}{rr}{a,b}{m} (ih {U}{g+mkic(r,b)}{R}{A}{m} pf)
		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf1, pf2) => 
			dcml_conn_p {U}{g-mkid(R,A)}{r}{rr}{a,b}{m,n} (ih {U}{g+mkic(r,a)}{R}{A} pf1, ih {U}{g+mkic(r,b)}{R}{A} pf2)
in 
	ih {U}{G}{R}{A}{M} pf 
end 

primplement lemma_split_c {U}{G}{R1,R2}{A}{M} (pf) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(R1,R2)} {A:form} {M:nat} .<size(A),M>. 
		(pf: DCML (U, M, nil |- G + mkic(R1+R2,A))): [I:nat] DCML (U, I, nil |- G + mkic(R1,A) + mkic(R2,A)) = 

		case+ pf of 
 		| dcml_axi_c {U}{g}{gi}{p} init => 
 			(*
				init: init (U,U,gi,p)
				----------------------
				pf: G + A[R1+R2] = g(gi)
				------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~lemma_init_member {U}{U}{gi}{p}{R1+R2}{A} init
 			then dcml_axi_c {U}{g-mkic(R1+R2,A)+mkic(R1,A)+mkic(R2,A)}{gi}{p} init
 			else 
 				let 
 					prval _ = lemma_init_form {U}{U}{gi}{p}{R1+R2}{A} init 
 					prval init = lemma_init_remove {U}{U}{gi}{p}{R1+R2}{A} init

 					prval _ = lemma_init_role_neg {U}{U-(R1+R2)}{gi-mkic(R1+R2,A)}{p}{R1}{A} init
 					prval init = dcmlc_init_more {U}{U-(R1+R2)}{gi-mkic(R1+R2,A)}{p}{R1} init

 					prval _ = lemma_init_role_neg {U}{U-(R1+R2)+R1}{gi-mkic(R1+R2,A)+mkic(R1,A)}{p}{R2}{A} init 
 					prval init = dcmlc_init_more {U}{U-(R1+R2)+R1}{gi-mkic(R1+R2,A)+mkic(R1,A)}{p}{R2} init
 				in 
 					dcml_axi_c {U}{g-mkic(R1+R2,A)+mkic(R1,A)+mkic(R2,A)}{gi-mkic(R1+R2,A)+mkic(R1,A)+mkic(R2,A)}{A} init
 				end

 		| dcml_axi_d {U}{g}{gi}{p} init => 
 			let prval _ = lemma_init_form_mix {U}{U}{gi}{p}{R1+R2}{A} init 
 			in dcml_axi_d {U}{g-mkic(R1+R2,A)+mkic(R1,A)+mkic(R2,A)}{gi}{p} init end 
 			

 		| dcml_neg_c {U}{g}{r}{a}{m} pf0 => 
 			if ~is_principal {mkic(r,neg(a))}{mkic(R1+R2,A)} () 
 			then 
 				let prval [i:int] pf = ih {U}{G+mkid(U-r,a)}{R1,R2}{A}{m} pf0
 				in dcml_neg_c {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{a}{i} pf end 
 			else 
 				let 
 					prval [i:int] pf = ih {U}{G+mkid(U-r,a)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf = lemma_split_d {U}{G+mkic(R1,A)+mkic(R2,A)}{U-R1,U-R2}{a}{i} pf 

 					prval pf = dcml_neg_c {U}{G+mkic(R1,A)+mkic(R2,A)+mkid(U-R2,a)}{R1}{a}{i} pf 
 					prval pf = dcml_neg_c {U}{G+mkic(R1,A)+mkic(R2,A)}{R2}{a}{i+1} pf 
 				in 
 					pf 
 				end 

 		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + a[r]
				------------------------------
				pf: g(conn(rr,a,b)[r]) = G + A[R1+R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R1+R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mkic(r,a)}{R1,R2}{A}{m} pf0
 				in dcml_conn_n1 {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					(* split conn(rr,a,b)[r] first, for the sake of termination checks *)
 					prval [i:int] pf = ih {U}{G+mkic(r,a)}{R1,R2}{A}{m} pf0
 					(* split a[r] *)
 					prval [i:int] pf = ih {U}{G+mkic(R1,A)+mkic(R2,A)}{R1,R2}{a}{i} pf

 					prval pf = dcml_conn_n1 {U}{G+mkic(R1,A)+mkic(R2,A)+mkic(R2,a)}{R1}{rr}{a,b}{i} pf
 					prval pf = dcml_conn_n1 {U}{G+mkic(R1,A)+mkic(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + b[r]
				------------------------------
				pf: g(conn(rr,a,b)[r]) = G + A[R1+R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R1+R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mkic(r,b)}{R1,R2}{A}{m} pf0
 				in dcml_conn_n2 {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					prval [i:int] pf = ih {U}{G+mkic(r,b)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf = ih {U}{G+mkic(R1,A)+mkic(R2,A)}{R1,R2}{b}{i} pf

 					prval pf = dcml_conn_n2 {U}{G+mkic(R1,A)+mkic(R2,A)+mkic(R2,b)}{R1}{rr}{a,b}{i} pf
 					prval pf = dcml_conn_n2 {U}{G+mkic(R1,A)+mkic(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

 		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + a[r]
				pf1: g(conn(rr,a,b)[r]) + b[r]
				------------------------------
				pf:  g(conn(rr,a,b)[r]) = G + A[R1+R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mkic(r,conn(rr,a,b))}{mkic(R1+R2,A)} ()
 			then 
 				let 
 				 	prval [i:int] pf0 = ih {U}{G+mkic(r,a)}{R1,R2}{A}{m} pf0
 					prval [j:int] pf1 = ih {U}{G+mkic(r,b)}{R1,R2}{A}{n} pf1
 				in 
 					dcml_conn_p {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
 				end
 			else 
 				let 
 					(* G + A[R1] + A[R2] + a[R1] + a[R2] *)
 					prval [i:int] pf0 = ih {U}{G+mkic(r,a)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf0 = ih {U}{G+mkic(R1,A)+mkic(R2,A)}{R1,R2}{a}{i} pf0

 					(* G + A[R1] + A[R2] + b[R1] + b[R2] *)
 					prval [j:int] pf1 = ih {U}{G+mkic(r,b)}{R1,R2}{A}{n} pf1
 					prval [j:int] pf1 = ih {U}{G+mkic(R1,A)+mkic(R2,A)}{R1,R2}{b}{j} pf1
 				in 
 					sif mem (U-R1, mk(rr))
 					then  
 						let 
		 					prval pf0 = dcml_conn_n1 {U}{G+mkic(R1,A)+mkic(R2,A)+mkic(R2,a)}{R1}{rr}{a,b}{i} pf0
		 					prval pf1 = dcml_conn_n2 {U}{G+mkic(R1,A)+mkic(R2,A)+mkic(R2,b)}{R1}{rr}{a,b}{j} pf1
		 				in 
		 					dcml_conn_p {U}{G+mkic(R1,A)+mkic(R2,A)}{R2}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 			else 
		 				let 
		 					prval pf0 = dcml_conn_n1 {U}{G+mkic(R1,A)+mkic(R2,A)+mkic(R1,a)}{R2}{rr}{a,b}{i} pf0
		 					prval pf1 = dcml_conn_n2 {U}{G+mkic(R1,A)+mkic(R2,A)+mkic(R1,b)}{R2}{rr}{a,b}{j} pf1
		 				in 
		 					dcml_conn_p {U}{G+mkic(R1,A)+mkic(R2,A)}{R1}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 		end

		| dcml_neg_d {U}{g}{r}{a}{m} pf0 => 
			let prval [i:int] pf = ih {U}{G+mkic(U-r,a)}{R1,R2}{A}{m} pf0
			in dcml_neg_d {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{a}{i} pf end 

 		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			let prval [i:int] pf = ih {U}{G+mkid(r,a)}{R1,R2}{A}{m} pf0
			in dcml_conn_p1 {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{rr}{a,b}{i} pf end

		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			let prval [i:int] pf = ih {U}{G+mkid(r,b)}{R1,R2}{A}{m} pf0
			in dcml_conn_p2 {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{rr}{a,b}{i} pf end

 		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
			let 
			 	prval [i:int] pf0 = ih {U}{G+mkid(r,a)}{R1,R2}{A}{m} pf0
				prval [j:int] pf1 = ih {U}{G+mkid(r,b)}{R1,R2}{A}{n} pf1
			in 
				dcml_conn_n {U}{G+mkic(R1,A)+mkic(R2,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
			end
in 
	ih {U}{G}{R1,R2}{A}{M} pf 
end 

primplement lemma_split_d {U}{G}{R1,R2}{A}{M} (pf) = let 

	prfun is_principal {p:belt} {a:belt} .<>. (): bool (p==a) = sif p == a then true else false

	prfun ih {U:roles} {G:seqs} {R1,R2:roles|sub(U,R1,R2)&&disj(U-R1,U-R2)} {A:form} {M:nat} .<size(A),M>. 
		(pf: DCML (U, M, nil |- G + mkid(R1*R2,A))): [I:nat] DCML (U, I, nil |- G + mkid(R1,A) + mkid(R2,A)) = 

		case+ pf of 
 		| dcml_axi_d {U}{g}{gi}{p} init => 
 			(*
				init: init (U,U,gi,p)
				----------------------
				pf: G + A[R1*R2] = g(gi)
				------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~lemma_init_member {U}{U}{gi}{p}{R1*R2}{A} init
 			then dcml_axi_d {U}{g-mkid(R1*R2,A)+mkid(R1,A)+mkid(R2,A)}{gi}{p} init
 			else 
 				let 
 					prval _ = lemma_init_form {U}{U}{gi}{p}{R1*R2}{A} init 
 					prval init = lemma_init_remove {U}{U}{gi}{p}{R1*R2}{A} init

 					prval _ = lemma_init_role_neg {U}{U-(U-(R1*R2))}{gi-mkid(R1*R2,A)}{p}{R1}{A} init
 					prval init = dcmld_init_more {U}{U-(U-(R1*R2))}{gi-mkid(R1*R2,A)}{p}{R1} init

 					prval _ = lemma_init_role_neg {U}{U-(U-(R1*R2))+(U-R1)}{gi-mkid(R1*R2,A)+mkid(R1,A)}{p}{R2}{A} init 
 					prval init = dcmld_init_more {U}{U-(U-(R1*R2))+(U-R1)}{gi-mkid(R1*R2,A)+mkid(R1,A)}{p}{R2} init
 				in 
 					dcml_axi_d {U}{g-mkid(R1*R2,A)+mkid(R1,A)+mkid(R2,A)}{gi-mkid(R1*R2,A)+mkid(R1,A)+mkid(R2,A)}{A} init
 				end

 		| dcml_axi_c {U}{g}{gi}{p} init => 
 			let prval _ = lemma_init_form_mix {U}{U}{gi}{p}{R1*R2}{A} init 
 			in dcml_axi_c {U}{g-mkid(R1*R2,A)+mkid(R1,A)+mkid(R2,A)}{gi}{p} init end 
 			

 		| dcml_neg_d {U}{g}{r}{a}{m} pf0 => 
 			if ~is_principal {mkid(r,neg(a))}{mkid(R1*R2,A)} () 
 			then 
 				let prval [i:int] pf = ih {U}{G+mkic(U-r,a)}{R1,R2}{A}{m} pf0
 				in dcml_neg_d {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{a}{i} pf end 
 			else 
 				let 
 					prval [i:int] pf = ih {U}{G+mkic(U-r,a)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf = lemma_split_c {U}{G+mkid(R1,A)+mkid(R2,A)}{U-R1,U-R2}{a}{i} pf 

 					prval pf = dcml_neg_d {U}{G+mkid(R1,A)+mkid(R2,A)+mkic(U-R2,a)}{R1}{a}{i} pf 
 					prval pf = dcml_neg_d {U}{G+mkid(R1,A)+mkid(R2,A)}{R2}{a}{i+1} pf 
 				in 
 					pf 
 				end 

 		| dcml_conn_p1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + a[r]
				------------------------------
				pf: g(conn(rr,a,b)[r]) = G + A[R1*R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1*R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mkid(r,a)}{R1,R2}{A}{m} pf0
 				in dcml_conn_p1 {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					(* split conn(rr,a,b)[r] first, for the sake of termination checks *)
 					prval [i:int] pf = ih {U}{G+mkid(r,a)}{R1,R2}{A}{m} pf0
 					(* split a[r] *)
 					prval [i:int] pf = ih {U}{G+mkid(R1,A)+mkid(R2,A)}{R1,R2}{a}{i} pf

 					prval pf = dcml_conn_p1 {U}{G+mkid(R1,A)+mkid(R2,A)+mkid(R2,a)}{R1}{rr}{a,b}{i} pf
 					prval pf = dcml_conn_p1 {U}{G+mkid(R1,A)+mkid(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

		| dcml_conn_p2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + b[r]
				------------------------------
				pf: g(conn(rr,a,b)[r]) = G + A[R1*R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1*R2,A)} ()
 			then 
 				let prval [i:int] pf = ih {U}{G+mkid(r,b)}{R1,R2}{A}{m} pf0
 				in dcml_conn_p2 {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{rr}{a,b}{i} pf end
 			else 
 				let 
 					prval [i:int] pf = ih {U}{G+mkid(r,b)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf = ih {U}{G+mkid(R1,A)+mkid(R2,A)}{R1,R2}{b}{i} pf

 					prval pf = dcml_conn_p2 {U}{G+mkid(R1,A)+mkid(R2,A)+mkid(R2,b)}{R1}{rr}{a,b}{i} pf
 					prval pf = dcml_conn_p2 {U}{G+mkid(R1,A)+mkid(R2,A)}{R2}{rr}{a,b}{i+1} pf 
 				in 
 					pf
 				end

 		| dcml_conn_n {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
 			(*
				pf0: g(conn(rr,a,b)[r]) + a[r]
				pf1: g(conn(rr,a,b)[r]) + b[r]
				------------------------------
				pf:  g(conn(rr,a,b)[r]) = G + A[R1*R2]
				-------------------------------------
				goal: G + A[R1] + A[R2]
 			*)
 			if ~is_principal {mkid(r,conn(rr,a,b))}{mkid(R1*R2,A)} ()
 			then 
 				let 
 				 	prval [i:int] pf0 = ih {U}{G+mkid(r,a)}{R1,R2}{A}{m} pf0
 					prval [j:int] pf1 = ih {U}{G+mkid(r,b)}{R1,R2}{A}{n} pf1
 				in 
 					dcml_conn_n {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
 				end
 			else 
 				let 
 					(* G + A[R1] + A[R2] + a[R1] + a[R2] *)
 					prval [i:int] pf0 = ih {U}{G+mkid(r,a)}{R1,R2}{A}{m} pf0
 					prval [i:int] pf0 = ih {U}{G+mkid(R1,A)+mkid(R2,A)}{R1,R2}{a}{i} pf0

 					(* G + A[R1] + A[R2] + b[R1] + b[R2] *)
 					prval [j:int] pf1 = ih {U}{G+mkid(r,b)}{R1,R2}{A}{n} pf1
 					prval [j:int] pf1 = ih {U}{G+mkid(R1,A)+mkid(R2,A)}{R1,R2}{b}{j} pf1
 				in 
 					sif mem (R1, mk(rr))
 					then  
 						let 
		 					prval pf0 = dcml_conn_p1 {U}{G+mkid(R1,A)+mkid(R2,A)+mkid(R2,a)}{R1}{rr}{a,b}{i} pf0
		 					prval pf1 = dcml_conn_p2 {U}{G+mkid(R1,A)+mkid(R2,A)+mkid(R2,b)}{R1}{rr}{a,b}{j} pf1
		 				in 
		 					dcml_conn_n {U}{G+mkid(R1,A)+mkid(R2,A)}{R2}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 			else 
		 				let 
		 					prval pf0 = dcml_conn_p1 {U}{G+mkid(R1,A)+mkid(R2,A)+mkid(R1,a)}{R2}{rr}{a,b}{i} pf0
		 					prval pf1 = dcml_conn_p2 {U}{G+mkid(R1,A)+mkid(R2,A)+mkid(R1,b)}{R2}{rr}{a,b}{j} pf1
		 				in 
		 					dcml_conn_n {U}{G+mkid(R1,A)+mkid(R2,A)}{R1}{rr}{a,b}{i+1,j+1} (pf0, pf1)
		 				end 
		 		end

		 | dcml_neg_c {U}{g}{r}{a}{m} pf0 => 
			let prval [i:int] pf = ih {U}{G+mkid(U-r,a)}{R1,R2}{A}{m} pf0
			in dcml_neg_c {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{a}{i} pf end 

 		| dcml_conn_n1 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			let prval [i:int] pf = ih {U}{G+mkic(r,a)}{R1,R2}{A}{m} pf0
			in dcml_conn_n1 {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{rr}{a,b}{i} pf end

		| dcml_conn_n2 {U}{g}{r}{rr}{a,b}{m} pf0 =>
			let prval [i:int] pf = ih {U}{G+mkic(r,b)}{R1,R2}{A}{m} pf0
			in dcml_conn_n2 {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{rr}{a,b}{i} pf end

 		| dcml_conn_p {U}{g}{r}{rr}{a,b}{m,n} (pf0, pf1) =>
			let 
			 	prval [i:int] pf0 = ih {U}{G+mkic(r,a)}{R1,R2}{A}{m} pf0
				prval [j:int] pf1 = ih {U}{G+mkic(r,b)}{R1,R2}{A}{n} pf1
			in 
				dcml_conn_p {U}{G+mkid(R1,A)+mkid(R2,A)}{r}{rr}{a,b}{i,j} (pf0, pf1)
			end
in 
	ih {U}{G}{R1,R2}{A}{M} pf 
end 