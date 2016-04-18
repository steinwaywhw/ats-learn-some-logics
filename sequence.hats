
(* bag definition for patsolve_smt *)

datasort BagElt = (* *)
sortdef elt = BagElt

datasort Bag = (* *)
sortdef bag = Bag 

stacst bag_emp: () -> bag
stacst bag_add: (bag, elt) -> bag
stacst bag_del: (bag, elt) -> bag
stacst bag_rmv: (bag, elt) -> bag
stacst bag_cap: (bag, bag) -> bag 
stacst bag_cup: (bag, bag) -> bag
stacst bag_dif: (bag, bag) -> bag
stacst bag_jon: (bag, bag) -> bag
stacst bag_mem: (bag, elt) -> bool
stacst bag_sub: (bag, bag) -> bool
stacst bag_eq: (bag, bag) -> bool
stacst bag_car: (bag, elt) -> int
stacst bag_size: (bag) -> int (* not built-in *)

stadef nil = bag_emp
stadef add (e:elt, s:bag) = bag_add (s, e)
stadef del = bag_del 
stadef rmv = bag_rmv
stadef cup = bag_cup
stadef dif = bag_dif
stadef cap = bag_cap
stadef join = bag_jon
stadef mem = bag_mem
stadef sub = bag_sub
stadef eq  = bag_eq
stadef bag_neq (a:bag, b:bag) = ~(a==b)
stadef car = bag_car
stadef size = bag_size

stadef + = add 
stadef + = bag_add
stadef + = cup
stadef - = del 
stadef - = dif
stadef * = cap
stadef == = eq
stadef != = bag_neq

praxi lemma_car_nat {g:bag} {i:elt} (): [car (g, i) >= 0] unit_p
praxi lemma_size_nat {g:bag} (): [size g >= 0] unit_p
praxi lemma_size_empty (): [size nil == 0] unit_p
praxi lemma_size_add {g:bag} {e:elt} (): [size(g+e) == size(g) + 1] unit_p

sortdef seqs = bag 
datasort seqt = seqt of (seqs, seqs)

stadef |- = seqt
infix |-


