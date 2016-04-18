
datasort ListElt = 
sortdef lelt = ListElt 

datasort List = 
sortdef list = List 

stacst list_hd: list -> lelt 
stacst list_tl: list -> list 
stacst list_nil: () -> list 
stacst list_cons: (lelt, list) -> list 
stacst list_eq: (list, list) -> bool

stadef lnil = list_nil
stadef ++ = list_cons 
infixr (::) ++
stadef hd = list_hd 
stadef tl = list_tl 
stadef == = list_eq 

stacst list_len: list -> int 
stadef len = list_len
stacst list_append: (list, list) -> list 
stadef + = list_append
stacst list_member: (list, lelt) -> bool 
stadef mem = list_member

praxi lemma_list_len_nil (): [len(lnil)==0] unit_p
praxi lemma_list_len_cons {l:list|not(l==lnil)} (): [len(l)==len(tl(l))+1] unit_p
praxi lemma_list_append_nil {l:list} (): [lnil+l==l] unit_p
praxi lemma_list_append_cons {e:lelt} {l1,l2:list} (): [(e++l1)+l2==e++(l1+l2)] unit_p
praxi lemma_list_mem_nil {e:lelt} (): [not(mem(lnil,e))] unit_p
praxi lemma_list_mem_cons {x:lelt} {e:lelt} {l:list} (): [(x==e&&mem(e++l,x))||(not(x==e)&&mem(e++l,x)==mem(l,x))] unit_p




////
fun test {l1,l2:list|len(l1+l2)==len(l1)+len(l2)} (): void


stacst mk_list: int -> lelt 
stadef mk = mk_list

praxi lemma_mk_list_inj {i:int} (): [mk_list(i)==mk_list(i)] unit_p
praxi lemma_mk_list_bij {i,j:int|not(i==j)} (): [not(mk_list(i)==mk_list(j))] unit_p