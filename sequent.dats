
staload "sequent.sats"

prval _ = $solver_assert lemma_size_nat
prval _ = $solver_assert lemma_size_empty
prval _ = $solver_assert lemma_size_add
prval _ = $solver_assert lemma_car_nat
prval _ = $solver_assert lemma_elt_eq


primplement g3_weakening {g} {d} {aa} (proof) = 
	case+ proof of 
	| g3_axi {g}{a} ()                => g3_axi {g+mk(aa)}{a} ()
	| g3_cut {g}{a}{c} (fst, snd)     => g3_cut {g+mk(aa)}{a}{c} (g3_weakening{g}{mks a}{aa} fst, g3_weakening{g+mk(a)}{mks c}{aa} snd)
	| g3_conjr {g}{a,b} (fst, snd)    => g3_conjr {g+mk(aa)}{a,b} (g3_weakening{g}{mks a}{aa} fst, g3_weakening{g}{mks b}{aa} snd)
	| g3_conjl1 {g}{a,b}{c} (proof)   => g3_conjl1 {g+mk(aa)}{a,b}{c} (g3_weakening{g+mk(a)}{mks c}{aa} proof)
	| g3_conjl2 {g}{a,b}{c} (proof)   => g3_conjl2 {g+mk(aa)}{a,b}{c} (g3_weakening{g+mk(b)}{mks c}{aa} proof)
	| g3_disjr1 {g}{a,b} (proof)      => g3_disjr1 {g+mk(aa)}{a,b} (g3_weakening{g}{mks a}{aa} proof)
	| g3_disjr2 {g}{a,b} (proof)      => g3_disjr2 {g+mk(aa)}{a,b} (g3_weakening{g}{mks b}{aa} proof)
	| g3_disjl {g}{a,b}{c} (fst, snd) => g3_disjl {g+mk(aa)}{a,b}{c} (g3_weakening{g+mk(a)}{mks c}{aa} fst, g3_weakening{g+mk(b)}{mks c}{aa} snd)
	| g3_implr {g}{a,b} (proof)       => g3_implr {g+mk(aa)}{a,b} (g3_weakening{g+mk(a)}{mks b}{aa} proof)
	| g3_impll {g}{a,b}{c} (fst, snd) => g3_impll {g+mk(aa)}{a,b}{c} (g3_weakening{g}{mks a}{aa} fst, g3_weakening{g+mk(b)}{mks c}{aa} snd)
	| g3_negr {g}{a} (proof)          => g3_negr {g+mk(aa)}{a} (g3_weakening{g+mk(a)}{nil}{aa} proof)
	| g3_negl {g}{a} (proof)          => g3_negl {g+mk(aa)}{a} (g3_weakening{g}{mks a}{aa} proof)

primplement g3_contraction {g} {d} {aa} (proof) = 
	case+ proof of 
	| g3_axi {g}{a} ()                => g3_axi {g-mk(aa)}{a} ()
	| g3_cut {g}{a}{c} (fst, snd)     => g3_cut {g-mk(aa)}{a}{c} (g3_contraction{g}{mks a}{aa} fst, g3_contraction{g+mk(a)}{mks c}{aa} snd)
	| g3_conjr {g}{a,b} (fst, snd)    => g3_conjr {g-mk(aa)}{a,b} (g3_contraction{g}{mks a}{aa} fst, g3_contraction{g}{mks b}{aa} snd)
	| g3_conjl1 {g}{a,b}{c} (proof)   => g3_conjl1 {g-mk(aa)}{a,b}{c} (g3_contraction{g+mk(a)}{mks c}{aa} proof)
	| g3_conjl2 {g}{a,b}{c} (proof)   => g3_conjl2 {g-mk(aa)}{a,b}{c} (g3_contraction{g+mk(b)}{mks c}{aa} proof)
	| g3_disjr1 {g}{a,b} (proof)      => g3_disjr1 {g-mk(aa)}{a,b} (g3_contraction{g}{mks a}{aa} proof)
	| g3_disjr2 {g}{a,b} (proof)      => g3_disjr2 {g-mk(aa)}{a,b} (g3_contraction{g}{mks b}{aa} proof)
	| g3_disjl {g}{a,b}{c} (fst, snd) => g3_disjl {g-mk(aa)}{a,b}{c} (g3_contraction{g+mk(a)}{mks c}{aa} fst, g3_contraction{g+mk(b)}{mks c}{aa} snd)
	| g3_implr {g}{a,b} (proof)       => g3_implr {g-mk(aa)}{a,b} (g3_contraction{g+mk(a)}{mks b}{aa} proof)
	| g3_impll {g}{a,b}{c} (fst, snd) => g3_impll {g-mk(aa)}{a,b}{c} (g3_contraction{g}{mks a}{aa} fst, g3_contraction{g+mk(b)}{mks c}{aa} snd)
	| g3_negr {g}{a} (proof)          => g3_negr {g-mk(aa)}{a} (g3_contraction{g+mk(a)}{nil}{aa} proof)
	| g3_negl {g}{a} (proof)          => g3_negl {g-mk(aa)}{a} (g3_contraction{g}{mks a}{aa} proof)

 primplement g3_disjunction {a,b} {c} (proof) = 
 	case+ proof of 
 	| g3_disjr1 {g}{a,b} (proof) => proof 
 	| g3_disjr2 {g}{a,b} (proof) => proof

//primplement lemma_lem {a} () = let 
//	prval pf = draxi {a} ()
//	prval pf = drnegr {nil, mks a} {a} pf 
//	prval pf = drdisjr2 {nil, mks a} {a, neg(a)} pf 
//	prval pf = drdisjr1 {nil, mks (a \disj neg(a))} {a, neg(a)} pf 
//	prval pf = drcr {nil, mk(a \disj neg(a))+mks(a \disj neg(a))} {a \disj neg(a)} pf 
//in 
//	lemma_com_disj {nil} {a, neg a} pf 
//end

