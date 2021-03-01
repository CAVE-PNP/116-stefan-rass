theory ex2_4
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = a # []" |
  "snoc (x#lst) a = x#(snoc lst a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse ( a # lst ) = snoc ( reverse lst ) a "


lemma rev_snoc [simp]: "reverse (snoc lst a) = a # (reverse lst)"
  apply (induction lst)
   apply (auto)
  done

lemma "reverse (reverse lst) = lst"
  apply (induction lst)
   apply (auto)
  done

end