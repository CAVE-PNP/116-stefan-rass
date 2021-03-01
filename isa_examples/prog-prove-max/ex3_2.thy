theory ex3_2
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (n + 2)"

inductive palindrome :: "'a list \<Rightarrow> bool" where
  p_empty: "palindrome []" |
  p_single: "palindrome [a]" |
  p_step: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"


lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction xs rule: palindrome.induct)
    apply (auto)
  done

end