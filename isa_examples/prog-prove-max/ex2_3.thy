theory ex2_3
  imports Main
begin

fun count::"'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count a [] = 0" |
  "count a (b # lst) = (if a=b then Suc (count a lst) else (count a lst))"


lemma "count x xs \<le> length xs"
  apply (induction xs)
   apply (auto)
  done

lemma "count x (a#xs) \<ge> count x xs"
  apply (induction xs)
   apply (auto)
  done

end