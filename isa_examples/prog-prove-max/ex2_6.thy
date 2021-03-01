theory ex2_6
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"


fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node lchild item rchild) = contents lchild @ [item] @ contents rchild"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node lchild item rchild) = sum_tree lchild + item + sum_tree rchild"


lemma "sum_tree t = sum_list(contents t)"
  apply (induction t)
   apply (auto)
  done

end