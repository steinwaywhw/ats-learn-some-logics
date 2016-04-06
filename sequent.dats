
staload "sequent.sats"

infix |-

prval _ = ()

prval _ = $solver_assert lemma_size_nat
prval _ = $solver_assert lemma_size_empty
prval _ = $solver_assert lemma_size_add
prval _ = $solver_assert lemma_car_nat
prval _ = $solver_assert lemma_mk_inj
prval _ = $solver_assert lemma_mk_bij

prval _ = $solver_assert lemma_form_size_nat 
prval _ = $solver_assert lemma_form_size_atom
prval _ = $solver_assert lemma_form_size_conj
prval _ = $solver_assert lemma_form_size_disj
prval _ = $solver_assert lemma_form_size_impl

primplement lemma_g3_wk {g} {c} {wk} {n} (proof) = let 
	prfun ih {g:seqs} {c:form} {wk:form} {n:nat} .<n>. (proof: G3 (g |- mks c, n)): G3 (g+mk(wk) |- mks c, n) = 
		case+ proof of 
		| g3_axi {g}{a} ()                     => g3_axi {g+mk(wk)}{a} ()
		| g3_botl {g}{c} ()                    => g3_botl {g+mk(wk)}{c} ()
		| g3_conjr {g}{a,b}{m,n} (fst, snd)    => g3_conjr {g+mk(wk)}{a,b}{m,n} (ih {g}{a}{wk}{m} fst, ih {g}{b}{wk}{n} snd)
		| g3_conjl1 {g}{a,b}{c}{n} (proof)     => g3_conjl1 {g+mk(wk)}{a,b}{c}{n} (ih {g+mk(a)}{c}{wk}{n} proof)
		| g3_conjl2 {g}{a,b}{c}{n} (proof)     => g3_conjl2 {g+mk(wk)}{a,b}{c}{n} (ih {g+mk(b)}{c}{wk}{n} proof)
		| g3_disjr1 {g}{a,b}{n} (proof)        => g3_disjr1 {g+mk(wk)}{a,b}{n} (ih {g}{a}{wk}{n} proof)
		| g3_disjr2 {g}{a,b}{n} (proof)        => g3_disjr2 {g+mk(wk)}{a,b}{n} (ih {g}{b}{wk}{n} proof)
		| g3_disjl {g}{a,b}{c}{m,n} (fst, snd) => g3_disjl {g+mk(wk)}{a,b}{c}{m,n} (ih {g+mk(a)}{c}{wk}{m} fst, ih {g+mk(b)}{c}{wk}{n} snd)
		| g3_implr {g}{a,b}{n} (proof)         => g3_implr {g+mk(wk)}{a,b}{n} (ih {g+mk(a)}{b}{wk}{n} proof)
		| g3_impll {g}{a,b}{c}{m,n} (fst, snd) => g3_impll {g+mk(wk)}{a,b}{c}{m,n} (ih {g}{a}{wk}{m} fst, ih {g+mk(b)}{c}{wk}{n} snd)
in 
	ih {g}{c}{wk}{n} proof
end

primplement lemma_g3_ctr {g} {c} {ctr} {n} (proof) = let 
	prfun ih {g:seqs} {c:form} {ctr:form|car(g,mk(ctr))>1} {n:nat} .<n>. (proof: G3 (g |- mks c, n)): G3 (g-mk(ctr) |- mks c, n) = 
		case+ proof of
		| g3_axi {g}{a} ()                     => g3_axi {g-mk(ctr)}{a} ()
		| g3_botl {g}{c} ()                    => g3_botl {g-mk(ctr)}{c} ()
		| g3_conjr {g}{a,b}{m,n} (fst, snd)    => g3_conjr {g-mk(ctr)}{a,b}{m,n} (ih {g}{a}{ctr}{m} fst, ih {g}{b}{ctr}{n} snd)
		| g3_conjl1 {g}{a,b}{c}{n} (proof)     => g3_conjl1 {g-mk(ctr)}{a,b}{c}{n} (ih {g+mk(a)}{c}{ctr}{n} proof)
		| g3_conjl2 {g}{a,b}{c}{n} (proof)     => g3_conjl2 {g-mk(ctr)}{a,b}{c}{n} (ih {g+mk(b)}{c}{ctr}{n} proof)
		| g3_disjr1 {g}{a,b}{n} (proof)        => g3_disjr1 {g-mk(ctr)}{a,b}{n} (ih {g}{a}{ctr}{n} proof)
		| g3_disjr2 {g}{a,b}{n} (proof)        => g3_disjr2 {g-mk(ctr)}{a,b}{n} (ih {g}{b}{ctr}{n} proof)
		| g3_disjl {g}{a,b}{c}{m,n} (fst, snd) => g3_disjl {g-mk(ctr)}{a,b}{c}{m,n} (ih {g+mk(a)}{c}{ctr}{m} fst, ih {g+mk(b)}{c}{ctr}{n} snd)
		| g3_implr {g}{a,b}{n} (proof)         => g3_implr {g-mk(ctr)}{a,b}{n} (ih {g+mk(a)}{b}{ctr}{n} proof)
		| g3_impll {g}{a,b}{c}{m,n} (fst, snd) => g3_impll {g-mk(ctr)}{a,b}{c}{m,n} (ih {g}{a}{ctr}{m} fst, ih {g+mk(b)}{c}{ctr}{n} snd)
in 
	ih {g}{c}{ctr}{n} proof
end 

primplement g3_negr {g} {a} {n} (pf) = g3_implr {g}{a,bot}{n} pf 
primplement g3_negl {g} {a} {n} (pf) = let 
	(*
		pf: g' + a->bot |- a 
		------------------------
		goal: g' + a->bot |- bot
	*)

	(* pf0: g + bot |- anything *)
	prval pf0 = g3_botl {g+mk(bot)}{bot} ()
in 
	g3_impll {g}{a,bot}{bot}{n,0} (pf, pf0)
end

primplement lemma_g3_dp {a,b} {n} (proof) = 
	case+ proof of 
	| g3_disjr1 {g}{a,b}{n} (proof)   =>   #[a|proof]
	| g3_disjr2 {g}{a,b}{n} (proof)   =>   #[b|proof]
	| _ =/=>> ()



primplement lemma_g3_cut {g} {c} {cut} {m,n} (fst, snd) = let 

	prfun ih 
		{g:seqs} {c:form} {cut:form} {m,n:nat} 
		.<size(cut),m,n>. 
		(fst: G3 (g |- mks cut, m), snd: G3 (g+mk(cut) |- mks c, n))
		: [i:nat] G3 (g |- mks c, i) =

		case+ (fst, snd) of 
		(* 
			axiom and botl cases
		*)
		| (g3_axi {g}{cut} (), _) =>> 
			(*
				fst: g |- cut  snd: g + cut |- c
				----------------------------------------
				goal: g |- c

				apply contraction
			*)
			lemma_g3_ctr {g+mk(cut)}{c}{cut}{n} snd

		| (_, g3_axi {g1}{c} ()) =>>
			(*
				fst: g |- cut     snd: g + cut |- c
				-----------------------------------
				goal: g |- c
			*)
			sif cut == c
			then fst
			else 
				(*
					snd: (g' + c) + cut |- c
				*)
				g3_axi {g1-mk(cut)}{c} ()

		| (g3_botl {g}{cut} (), _) =>> 
			(*
				fst: g(g' + bot) |- cut
			*)
			g3_botl {g}{c} ()

		| (_, g3_botl {g1}{c} ()) =>>
			(*
				fst: g |- cut   snd: g + cut |- c
			*)
			sif mem(g, mk bot)
			then g3_botl {g}{c} ()
			else 
				(* 
					fst: g |- bot(cut)

					snd can't be a right rule
					and axiom/botl is already covered in previous cases

					then all of these should be covered in other snd = left cases
				*)
				(
				case+ fst of 
				| g3_conjl1 {g}{a0,b0}{cut}{n0} (pf0) => 
					(*
						pf0: g(g' + a \conj b) + a0 |- bot
						----------------------------------
						fst: g(g' + a \conj b) |- bot

						cut (pf0, snd) => g + a0 |- bot
						conjl1: g |- bot
					*)
					let 
						prval snda = lemma_g3_wk {g+mk(cut)}{c}{a0}{0} snd 
						prval [i:int] pf = ih {g+mk(a0)}{c}{cut}{n0,0} (pf0, snda)
					in 
						g3_conjl1 {g}{a0,b0}{c}{i} pf 
					end 

				| g3_conjl2 {g}{a0,b0}{cut}{n0} (pf0) => 
					(* same as conjl1 *)
					let 
						prval sndb = lemma_g3_wk {g+mk(cut)}{c}{b0}{0} snd 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,0} (pf0, sndb)
					in 
						g3_conjl2 {g}{a0,b0}{c}{i} pf 
					end 

				| g3_disjl {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) => 
					(*
						pf00: g + a0 |- cut 
						pf01: g + b0 |- cut             
						--------------------------------------------------------
						fst: g(g' + a0 \disj b0) |- cut  snd: g1(g + bot(cut)) |- c
					*)
					let 
						prval snda = lemma_g3_wk {g+mk(cut)}{c}{a0}{0} snd 
						prval sndb = lemma_g3_wk {g+mk(cut)}{c}{b0}{0} snd 

						(* to get g + a0 |- c *)
						prval [i:int] pf00 = ih {g+mk(a0)}{c}{cut}{m0,0} (pf00, snda)
						(* to get g + b0 |- c *)
						prval [j:int] pf01 = ih {g+mk(b0)}{c}{cut}{n0,0} (pf01, sndb)
					in 
						g3_disjl {g}{a0,b0}{c}{i,j} (pf00, pf01)
					end 

				| g3_impll {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) => 
					(*
						pf00: g |- a0
						pf01: g + b0 |- cut
						------------------------------------------------
						fst: g(g' + a0 -> b0) |- cut   snd: g + cut |- c
					*)	
					let 
						prval sndb = lemma_g3_wk {g+mk(cut)}{c}{b0}{0} snd
						(* to get g + b0 |- c *)
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,0} (pf01, sndb)
					in 
						g3_impll {g}{a0,b0}{c}{m0,i} (pf00, pf)
					end
				| _ =/=>> ()
				)

		(*
			when cut is not the principal formula of fst,
			fst must be a left rule
		*)
		
		| (g3_conjl1 {g}{a0,b0}{cut}{n0} (pf0), _) =>>
			(*
				pf0: g(g' + a0 \conj b0) + a0 |- cut
				------------------------------------
				fst: g(g' + a0 \conj b0) |- cut       snd: g(g' + a0 \conj b0) + cut |- c
				-------------------------------------------------------------------------
				goal: g |- c
			*)
			let 
				(* pf: g + a0 + cut |- c *)
				prval snda = lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd 

				(* pf: g + a0 |- c *)
				prval [i:int] pf = ih {g+mk(a0)}{c}{cut}{n0,n} (pf0, snda)
			in 
				g3_conjl1 {g}{a0,b0}{c}{i} pf 
			end 
		

		| (g3_conjl2 {g}{a0,b0}{cut}{n0} (pf0), _) =>>
			(* the same as g3_conjl1 *)
			let 
				(* pf: g + b0 + cut |- c *)
				prval sndb = lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd 

				(* pf: g + b0 |- c *)
				prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf0, sndb)
			in 
				g3_conjl2 {g}{a0,b0}{c}{i} pf 
			end 
		

		| (g3_disjl {g}{a0,b0}{cut}{m0,n0} (pf00, pf01), _) =>> 
			(*
				pf00: g + a0 |- cut    
				pf01: g + b0 |- cut
				--------------------------------------------------
				fst: g(g' + a0 \disj b0) |- cut  snd: g + cut |- c
			*)
			let 
				(* 
					pf1: g + a0 + cut |- c 
					pf2: g + b0 + cut |- c

					cut (pf1, snd)
					cut (pf2, snd)
				*)
				prval snda = lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd 
				prval sndb = lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd 
				prval [i:int] pf1 = ih {g+mk(a0)}{c}{cut}{m0,n} (pf00, snda)
				prval [j:int] pf2 = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, sndb)
			in 
				g3_disjl {g}{a0,b0}{c}{i,j} (pf1, pf2)
			end 

		
		| (g3_impll {g}{a0,b0}{cut}{m0,n0} (pf00, pf01), _) =>> 
			(*
				pf00: g(g' + a->b) |- a    
				pf01: g + b0 |- cut
				--------------------------------------
				fst: g |- cut        snd: g + cut |- c
			*)
			let 
				(* pf: g + b0 + cut |- c *)
				prval sndb = lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd 

				(* pf: g + b0 |- c *)
				prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, sndb)
			in 
				g3_impll {g}{a0,b0}{c}{m0,i} (pf00, pf)
			end

		(* 
			now, cut must be a principal formula of fst, 
			let us consider snd,
			if it is R rule, then cut must not be principal formula of snd
		*)

		| (_, g3_conjr {g1}{a1,b1}{m1,n1} (pf10, pf11)) =>>
			(*
				                pf10: g1 |- a1   
				                pf11: g1 |- b1
                                -------------------------------
				fst: g |- cut   snd: g1(g+cut) |- c(a1 \conj b1)
			*)
			let 
				(* pf1: g |- a1 *)
				prval [i:int] pf1 = ih {g}{a1}{cut}{m,m1} (fst, pf10)
				(* pf2: g |- b1 *)
				prval [j:int] pf2 = ih {g}{b1}{cut}{m,n1} (fst, pf11)
			in 
				g3_conjr {g}{a1,b1}{i,j} (pf1, pf2)
			end
		
		| (_, g3_disjr1 {g1}{a1,b1}{n1} pf1) =>> 
			(*
				                pf1: g1 |- a1
                                -------------------------------
				fst: g |- cut   snd: g1(g+cut) |- c(a1 \disj b1)
			*)
			let 
				prval [i:int] pf = ih {g}{a1}{cut}{m,n1} (fst, pf1)
			in 
				g3_disjr1 {g}{a1,b1}{i} pf 
			end 

		| (_, g3_disjr2 {g1}{a1,b1}{n1} pf1) =>> 
			(* same as g3_disjr1 *)
			let 
				prval [i:int] pf = ih {g}{b1}{cut}{m,n1} (fst, pf1)
			in 
				g3_disjr2 {g}{a1,b1}{i} pf 
			end 

		| (_, g3_implr {g1}{a1,b1}{n1} pf1) =>> 
			(*
				                pf1: g1 + a1 |- b1
                                -------------------------------
				fst: g |- cut   snd: g1(g+cut) |- c(a1 -> b1)
			*)
			let 
				(* pf: g + a1 |- cut *)
				prval fsta = lemma_g3_wk {g}{cut}{a1}{m} fst 
				prval [i:int] pf = ih {g+mk(a1)}{b1}{cut}{m,n1} (fsta, pf1)
			in 
				g3_implr {g}{a1,b1}{i} pf 
			end

		(*
			now, cut has to be a principal formula of fst, 
			which means fst has to be R rule

			since snd R rules are finished, now snd should be L rules

			* cut is principal in snd, then fst's shape is decidable
			* cut is not principal in snd
		*)

		| (_, g3_conjl1 {g1}{a1,b1}{c}{n1} pf1) =>> 
			sif not(cut==(a1 \conj b1))
			then (* cut is not principal in snd *)
				(*
					                pf1: g1(g' + cut + a1 \conj b1) + a1 |- c
	                                ------------------------------------------
					fst: g |- cut   snd: g1(g' + cut + a1 \conj b1) |- c
				*) 
				let  
					prval fsta = lemma_g3_wk {g}{cut}{a1}{m} fst 
					prval [i:int] pf = ih {g+mk(a1)}{c}{cut}{m,n1} (fsta, pf1)
				in 
					g3_conjl1 {g}{a1,b1}{c}{i} pf 
				end 
			else (* cut is principal in snd *)
				(*
					pf00: g |- a0, pf01: g |- b0         pf1: g + a1 \conj b1 + a1/b1 |- c
				    --------------------------------     --------------------------------------
				    fst: g |- a0 \conj b0 (cut)          snd: g + a1 \conj b1 |- c
				    --------------------------------------------------------------------
				    goal: g |- c
				*) 
				(
				case+ fst of 
				| g3_conjr {g}{a0,b0}{m0,n0} (pf00, _) => 
					let 
						(* pf: g + a1 |- cut *)
						prval fsta = lemma_g3_wk {g}{cut}{a1}{m} fst 
						(* pf: g + a1 |- c *)
						prval [i:int] pf = ih {g+mk(a1)}{c}{cut}{m,n1} (fsta, pf1)
					in 
						ih {g}{c}{a0}{m0,i} (pf00, pf)
					end 

				| g3_conjl1 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(a0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
					in 
						g3_conjl1 {g}{a0,b0}{c}{i} pf 
					end 

				| g3_conjl2 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_conjl2 {g}{a0,b0}{c}{i} pf 
					end 
				

				| g3_disjl {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf1 = ih {g+mk(a0)}{c}{cut}{m0,n} (pf00, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
						prval [j:int] pf2 = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_disjl {g}{a0,b0}{c}{i,j} (pf1, pf2)
					end 

				
				| g3_impll {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_impll {g}{a0,b0}{c}{m0,i} (pf00, pf)
					end

				| _ =/=>> ()
				)

		| (_, g3_conjl2 {g1}{a1,b1}{c}{n1} pf1) =>>
			(* same as g3_conjl2 *)
			sif not(cut==(a1 \conj b1))
			then 
				let  
					prval fstb = lemma_g3_wk {g}{cut}{b1}{m} fst 
					prval [i:int] pf = ih {g+mk(b1)}{c}{cut}{m,n1} (fstb, pf1)
				in 
					g3_conjl2 {g}{a1,b1}{c}{i} pf 
				end 
			else 
				(
				case+ fst of 
				| g3_conjr {g}{a0,b0}{m0,n0} (_, pf01) => 
					let 
						(* pf: g + a1 |- cut *)
						prval fstb = lemma_g3_wk {g}{cut}{b1}{m} fst 
						(* pf: g + a1 |- c *)
						prval [i:int] pf = ih {g+mk(b1)}{c}{cut}{m,n1} (fstb, pf1)
					in 
						ih {g}{c}{b0}{n0,i} (pf01, pf)
					end 
				| g3_conjl1 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(a0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
					in 
						g3_conjl1 {g}{a0,b0}{c}{i} pf 
					end 

				| g3_conjl2 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_conjl2 {g}{a0,b0}{c}{i} pf 
					end 
				

				| g3_disjl {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf1 = ih {g+mk(a0)}{c}{cut}{m0,n} (pf00, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
						prval [j:int] pf2 = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_disjl {g}{a0,b0}{c}{i,j} (pf1, pf2)
					end 

				
				| g3_impll {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_impll {g}{a0,b0}{c}{m0,i} (pf00, pf)
					end
	
				| _ =/=>> () 
				)

		| (_, g3_disjl {g1}{a1,b1}{c}{m1,n1} (pf10, pf11)) =>>
			sif not(cut==(a1 \disj b1))
			then (* cut is not principal in snd*)
				(*
					                pf10: g1(g' + cut + a1 \disj b1) + a1 |- c
					                pf11: g1(g' + cut + a1 \disj b1) + b1 |- c
	                                ------------------------------------------
					fst: g |- cut   snd: g1(g' + cut + a1 \disj b1) |- c
				*) 
				let 
					prval fsta = lemma_g3_wk {g}{cut}{a1}{m} fst 
					prval fstb = lemma_g3_wk {g}{cut}{b1}{m} fst 
					prval [i:int] pf1 = ih {g+mk(a1)}{c}{cut}{m,m1} (fsta, pf10)
					prval [j:int] pf2 = ih {g+mk(b1)}{c}{cut}{m,n1} (fstb, pf11)
				in 
					g3_disjl {g}{a1,b1}{c}{i,j} (pf1, pf2)
				end 
			else (* cut is principal in snd *)
				(*
					pf0: g |- a0/b0                pf10: g1(g + a1 \disj b1) + a1 |- c
                                                   pf11: g1(g + a1 \disj b1) + b1 |- c
					---------------------------    --------------------------------------
					fst: g |- a0 \disj b0 (cut)    snd: g + a1 \conj b1 |- c
					---------------------------------------------------------------------
					goal: g |- c
				*)
				(
				case+ fst of 
				| g3_disjr1 {g}{a0,b0}{n0} pf0 => 
					let 
						prval fsta = lemma_g3_wk {g}{cut}{a1}{m} fst 
						prval [i:int] pf = ih {g+mk(a1)}{c}{cut}{m,m1} (fsta, pf10)
					in 
						ih {g}{c}{a0}{n0,i} (pf0, pf)
					end 
				| g3_disjr2 {g}{a0,b0}{n0} pf0 => 
					let 
						prval fstb = lemma_g3_wk {g}{cut}{b1}{m} fst 
						prval [i:int] pf = ih {g+mk(b1)}{c}{cut}{m,n1} (fstb, pf11)
					in 
						ih {g}{c}{b0}{n0,i} (pf0, pf)
					end
				| g3_conjl1 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(a0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
					in 
						g3_conjl1 {g}{a0,b0}{c}{i} pf 
					end 

				| g3_conjl2 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_conjl2 {g}{a0,b0}{c}{i} pf 
					end 
				

				| g3_disjl {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf1 = ih {g+mk(a0)}{c}{cut}{m0,n} (pf00, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
						prval [j:int] pf2 = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_disjl {g}{a0,b0}{c}{i,j} (pf1, pf2)
					end 

				
				| g3_impll {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_impll {g}{a0,b0}{c}{m0,i} (pf00, pf)
					end
 
				| _ =/=>> ()
				)

		| (_, g3_impll {g1}{a1,b1}{c}{m1,n1} (pf10, pf11)) =>>
			sif not(cut==(a1 \impl b1))
			then (* cut is not principal in snd *)
				(*
					                pf10: g1(g' + cut + a1->b1) |- a1
					                pf11: g1(g' + cut + a1->b1) + b1 |- c
	                                ------------------------------------------
					fst: g |- cut   snd: g1(g' + cut + a1->b1) |- c
				*) 			
				let 
					(* pf1: g |- a1 *)
					prval [i:int] pf1 = ih {g}{a1}{cut}{m,m1} (fst, pf10)
					(* pf: g + b1 |- cut *)
					prval fstb = lemma_g3_wk {g}{cut}{b1}{m} fst 
					(* pf2: g + b1 |- c *)
					prval [j:int] pf2 = ih {g+mk(b1)}{c}{cut}{m,n1} (fstb, pf11)
				in 
					g3_impll {g}{a1,b1}{c}{i,j} (pf1, pf2)
				end 
			else (* cut is principal in snd *)
				(*
					                    pf10: g1(g + a1->b1) |- a1
					pf0: g + a0 |- b0   pf11: g1(g + a1->b1) + b1 |- c
	                -----------------   ------------------------------------------
					fst: g |- cut       snd: g1(g + a1->b1 (cut)) |- c
				*)
				( 			
				case+ fst of 
				| g3_implr {g}{a0,b0}{n0} (pf0) => 
					let 
						(* pf1: g |- a1 *)
						prval [i:int] pf1 = ih {g}{a1}{cut}{m,m1} (fst, pf10)
						(* pf1: g |- b1 *)
						prval [i:int] pf1 = ih {g}{b1}{a1}{i,n0} (pf1, pf0)

						(* pf: g + b1 |- cut *)
						prval fstb = lemma_g3_wk {g}{cut}{b1}{m} fst 
						(* pf2: g + b1 |- c *)
						prval [j:int] pf2 = ih {g+mk(b1)}{c}{cut}{m,n1} (fstb, pf11)
					in 
						ih {g}{c}{b1}{i,j} (pf1, pf2)
					end
				| g3_conjl1 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(a0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
					in 
						g3_conjl1 {g}{a0,b0}{c}{i} pf 
					end 

				| g3_conjl2 {g}{a0,b0}{cut}{n0} (pf0) =>>
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf0, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_conjl2 {g}{a0,b0}{c}{i} pf 
					end 
				

				| g3_disjl {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf1 = ih {g+mk(a0)}{c}{cut}{m0,n} (pf00, lemma_g3_wk {g+mk(cut)}{c}{a0}{n} snd)
						prval [j:int] pf2 = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_disjl {g}{a0,b0}{c}{i,j} (pf1, pf2)
					end 

				
				| g3_impll {g}{a0,b0}{cut}{m0,n0} (pf00, pf01) =>> 
					let 
						prval [i:int] pf = ih {g+mk(b0)}{c}{cut}{n0,n} (pf01, lemma_g3_wk {g+mk(cut)}{c}{b0}{n} snd)
					in 
						g3_impll {g}{a0,b0}{c}{m0,i} (pf00, pf)
					end

				| _ =/=>> ()
				)		
in 
	ih {g}{c}{cut}{m,n} (fst, snd)
end

		

// primplement lemma_g3_dp {a,b} {c} (proof) =
// 	sif c == a
// 	then case+ proof of g3_disjr1 {g}{a,b} (proof) => proof
// 	else case+ proof of g3_disjr2 {g}{a,b} (proof) => proof



//primplement lemma_lem {a} () = let 
//	prval pf = draxi {a} ()
//	prval pf = drnegr {nil, mks a} {a} pf 
//	prval pf = drdisjr2 {nil, mks a} {a, neg(a)} pf 
//	prval pf = drdisjr1 {nil, mks (a \disj neg(a))} {a, neg(a)} pf 
//	prval pf = drcr {nil, mk(a \disj neg(a))+mks(a \disj neg(a))} {a \disj neg(a)} pf 
//in 
//	lemma_com_disj {nil} {a, neg a} pf 
//end

