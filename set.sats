datasort SetElt = (* *)
sortdef selt = SetElt

datasort Set = (* *)
sortdef set = Set 

stacst set_emp: () -> set
stacst set_add: (set, selt) -> set
stacst set_del: (set, selt) -> set
stacst set_cap: (set, set) -> set 
stacst set_cup: (set, set) -> set
stacst set_dif: (set, set) -> set
stacst set_mem: (set, selt) -> bool
stacst set_sub: (set, set) -> bool
stacst set_eq: (set, set) -> bool
stacst set_size: (set) -> int (* not built-in *)

stadef snil = set_emp
stadef + (e:selt, s:set) = set_add (s, e)
stadef + = set_add
stadef - = set_del 
stadef + = set_cup
stadef - = set_dif
stadef * = set_cap
stadef mem = set_mem
stadef sub = set_sub
stadef ==  = set_eq
stadef != (a:set, b:set) = ~(a==b)
stadef size = set_size

praxi lemma_set_sub_emp {g:set} (): [sub(g,snil)] unit_p
praxi lemma_set_sub_sub {g1,g2,g3:set|sub(g1,g2)&&sub(g2,g3)} (): [sub(g1,g3)] unit_p
praxi lemma_set_sub_cap {g,g1,g2:set|sub(g,g1)&&sub(g,g2)} (): [sub(g,g1*g2)] unit_p
praxi lemma_set_sub_cup {g,g1,g2:set|sub(g,g1)&&sub(g,g2)} (): [sub(g,g1+g2)] unit_p
praxi lemma_set_sub_cup2 {g1,g2:set} (): [sub(g1+g2,g1)&&sub(g1+g2,g2)] unit_p
praxi lemma_set_sub_cap2 {g1,g2:set} (): [sub(g1,g1*g2)&&sub(g2,g1*g2)] unit_p
praxi lemma_set_sub_self {g:set} (): [sub(g,g)] unit_p

praxi lemma_set_size_nat {g:set} (): [size g >= 0] unit_p
praxi lemma_set_size_empty (): [size(set_emp()) == 0] unit_p
praxi lemma_set_size_add1 {g:set} {e:selt|not(mem(g,e))} (): [size(g+e) == size(g)+1] unit_p
praxi lemma_set_size_add2 {g:set} {e:selt|mem(g,e)} (): [size(g+e) == size(g)] unit_p


//stacst set_is_com: (set, set, set) -> bool

//praxi lemma_set_comdef1 {g,g1,g2:set|(g1+g2==g)&&(g1*g2==snil)} (): [set_is_com(g,g1,g2)] unit_p

praxi lemma_set_com {g,g1:set|sub(g,g1)} (): [(g1+(g-g1)==g)&&(g1*(g-g1)==snil)&&(sub(g,g-g1))] unit_p