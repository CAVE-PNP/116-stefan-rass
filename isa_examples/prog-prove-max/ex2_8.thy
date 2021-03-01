theory ex2_8
  imports Main
begin

fun intersperse::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a [x] = [x]" |
  "intersperse a (x#lst) = [x,a] @ intersperse a lst"


lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
    apply (auto)
  done

end