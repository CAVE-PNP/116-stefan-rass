theory ex2_7
  imports Main
begin 

datatype 'a tree2 = Tip | Leaf 'a | Node "'a tree2" 'a "'a tree2"


fun mirror :: " 'a tree2 \<Rightarrow> 'a tree2" where
  "mirror Tip = Tip" | 
  "mirror (Leaf a) = Leaf a" |
  "mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun pre_order:: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order(Tip) = []" |
  "pre_order(Leaf a) = [a]" |
  "pre_order(Node l a r) = a # pre_order(l) @ pre_order(r)"

fun post_order:: "'a tree2 \<Rightarrow> 'a list" where
  "post_order(Tip) = []" |
  "post_order(Leaf a) = [a]" |
  "post_order(Node l a r) = post_order(l) @ post_order(r) @ [a]"


lemma "pre_order(mirror t) = rev(post_order t)"
  apply (induction t)
    apply (auto)
  done

end