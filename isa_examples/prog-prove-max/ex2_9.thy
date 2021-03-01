theory ex2_9
  imports Main
begin

fun itadd :: "[nat,nat] \<Rightarrow> nat" where 
  "itadd 0 a = a" |
  "itadd (Suc a) b = itadd a (Suc b)"


lemma "itadd a b = a + b"
  apply (induction a arbitrary: b)
   apply (auto)
  done

end