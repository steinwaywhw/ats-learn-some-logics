datasort BagElt = (* *)
sortdef belt = BagElt

datasort Bag = (* *)
sortdef bag = Bag 

stacst bag_emp: () -> bag
stacst bag_add: (bag, belt) -> bag
stacst bag_del: (bag, belt) -> bag
stacst bag_rmv: (bag, belt) -> bag
stacst bag_cap: (bag, bag) -> bag 
stacst bag_cup: (bag, bag) -> bag
stacst bag_dif: (bag, bag) -> bag
stacst bag_jon: (bag, bag) -> bag
stacst bag_mem: (bag, belt) -> bool
stacst bag_sub: (bag, bag) -> bool
stacst bag_eq: (bag, bag) -> bool
stacst bag_car: (bag, belt) -> int
stacst bag_size: (bag) -> int (* not built-in *)

stadef bnil = bag_emp
stadef + (e:belt, s:bag) = bag_add (s, e)
stadef + = bag_add
stadef - = bag_del 
stadef rmv = bag_rmv
stadef + = bag_cup
stadef - = bag_dif
stadef * = bag_cap
stadef join = bag_jon
stadef mem = bag_mem
stadef sub = bag_sub
stadef ==  = bag_eq
stadef != (a:bag, b:bag) = ~(a==b)
stadef car = bag_car
stadef size = bag_size


praxi lemma_bag_sub_emp {g:bag} (): [sub(g,bnil)] unit_p
praxi lemma_bag_sub_sub {g1,g2,g3:bag|sub(g1,g2)&&sub(g2,g3)} (): [sub(g1,g3)] unit_p
praxi lemma_bag_sub_cap {g,g1,g2:bag|sub(g,g1)&&sub(g,g2)} (): [sub(g,g1*g2)] unit_p
//praxi lemma_bag_sub_cup {g,g1,g2:bag|sub(g,g1)&&sub(g,g2)} (): [sub(g,g1+g2)] unit_p
praxi lemma_bag_sub_cup2 {g1,g2:bag} (): [sub(g1+g2,g1)&&sub(g1+g2,g2)] unit_p
praxi lemma_bag_sub_cap2 {g1,g2:bag} (): [sub(g1,g1*g2)&&sub(g2,g1*g2)] unit_p
praxi lemma_bag_sub_self {g:bag} (): [sub(g,g)] unit_p

//praxi lemma_bag_eq_eq {g1,g2,g3:bag|g1==g2&&g2==g3} (): [g1==g3] unit_p


praxi lemma_bag_car_nat {g:bag} {i:belt} (): [car (g, i) >= 0] unit_p
praxi lemma_bag_size_nat {g:bag} (): [size g >= 0] unit_p
praxi lemma_bag_size_empty (): [size(bag_emp()) == 0] unit_p
praxi lemma_bag_size_add {g:bag} {e:belt} (): [size(g+e) == size(g)+1] unit_p
praxi lemma_bag_size_cup {g1,g2:bag} (): [size(g1+g2) == size(g1)+size(g2)] unit_p
praxi lemma_bag_add_bag {g,g1,g2:bag|g==g1+g2} (): [g-g1==g2&&g-g2==g1] unit_p
praxi lemma_bag_add_elt {g,g1:bag} {e:belt|g==g1+e}  (): [g-e==g1] unit_p

praxi lemma_bag_cup_add {g1,g2:bag} {e:belt} (): [(g1+e)+g2==(g1+g2)+e] unit_p
praxi lemma_bag_cup_del {g1,g2:bag} {e:belt|mem(g1,e)} (): [(g1-e)+g2==(g1+g2)-e] unit_p
//praxi lemma_bag_add_del {g:bag} {e1,e2:belt|mem(g,e1)} (): [(g-e1)+e2==(g+e2)-e1] unit_p