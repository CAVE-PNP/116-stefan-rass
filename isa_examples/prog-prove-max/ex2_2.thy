theory ex2_2
  imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"


lemma add_02 [simp]: "add m 0 = m"
  apply (induction m)
   apply (auto)
  done

lemma add_03 [simp] : "add m (Suc n) = Suc(add m n)"
  apply (induction m)
   apply (auto)
  done


lemma add_assoc: "add (add a b) c = add a (add b c)"
  apply (induction a)
   apply (auto)
  done

lemma add_comm: "add a b = add b a"
  apply (induction a)
   apply (auto)
  done

end