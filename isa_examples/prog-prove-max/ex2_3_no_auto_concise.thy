theory ex2_3_no_auto_concise
  imports Main HOL.HOL
begin

fun count::"'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count a [] = 0" |
  "count a (b # lst) = (if a=b then Suc (count a lst) else (count a lst))"


lemma 
  fixes x xs
  shows "count x xs \<le> length xs"
proof (induction xs)
  case Nil
  have "count x [] = 0" by (rule count.simps(1))
  also have "length [] = 0" by (rule list.size(3))
  finally have "count x [] = length []" by (rule sym)
  then show "count x [] \<le> length []" by (rule eq_imp_le)
next
  fix b
  case (Cons a xs)
  hence "count x (a # xs) \<le> Suc (length xs)"
  proof (cases "x = a")
    case True
    hence "count x (a # xs) = Suc (count x xs)" unfolding count.simps by (rule HOL.if_P)
    also have "Suc (count x xs) \<le> Suc (length xs)" using Cons.IH by (subst Suc_le_mono)
    finally show ?thesis .
  next
    case False
    hence "count x (a # xs) = count x xs" unfolding count.simps by (rule HOL.if_not_P)
    also have "count x xs \<le> Suc (length xs)" using Cons.IH by (rule le_SucI)
    finally show ?thesis .
  qed
  also have "Suc (length xs) = length (a # xs)"
  proof -
    have "(length xs) = (length xs + 0)" by (rule sym) (rule Nat.add_0_right)
    hence "Suc (length xs) = Suc (length xs + 0)" ..
    hence "Suc (length xs) = length xs + Suc 0" by (subst Nat.add_Suc_right)
    also have "length xs + Suc 0 = length (a # xs)" by (rule sym) (rule list.size(4))
    finally show ?thesis .
  qed
  finally show ?case .
qed

lemma 
  fixes x a xs
  shows "count x (a # xs) \<ge> count x xs"
proof (cases "x = a")
  case True
  then have "count x (a # xs) = Suc (count x xs)" unfolding count.simps by (rule HOL.if_P)
  also have "Suc (count x xs) > count x xs" by (rule lessI)
  finally show ?thesis by (rule less_imp_le_nat)
next
  case False
  then have "count x (a # xs) = count x xs" unfolding count.simps by (rule HOL.if_not_P)
  then have "count x xs = count x (a # xs)" by (rule sym)
  then show ?thesis by (rule eq_imp_le)
qed

end