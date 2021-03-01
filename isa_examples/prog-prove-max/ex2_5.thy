theory ex2_5
  imports Main
begin

fun sum_upto::"nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = Suc n + sum_upto n"


lemma gauss_sum [simp]: "sum_upto n = (n * (n+1)) div 2"
  by (induction n) auto

end